-- Prove2me | Definitions.Def_Yukon_0b6b33c0cec00f644e57a89f
-- name    : Yukon_0b6b33c0cec00f644e57a89f
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:54:38.306899+00:00
-- url     : https://prove2.me/theorems/ac89d537-1a44-49d9-a6c8-ed11bd88315e
-- title:
--   YukonModule.VCVio.EvalDist.Inequalities.part0
-- statement:
--   Source module VCVio.EvalDist.Inequalities.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Inequalities.lean
--
--   yukon-proof-operation:97f7b4e09b8bfeea13fa8bef8f335ae7a1d3cf690dbbde525cc536a127162ce0
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OTdmN2I0ZTA5YjhiZmVlYTEzZmE4YmVmOGYzMzVhZTdhMWQzY2Y2OTBkYmJkZTUyNWNjNTM2YTEyNzE2MmNlMCIsImhhc2giOiIyYjBjNjAzMzM4ZDFhZjc4N2Y1NjQ3NGQwMGViZjUyMjA5ZTRkN2VlNTIwMTU4M2ZiYTVlZmE0MzI3YmU2NTU0Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8wYjZiMzNjMGNlYzAwZjY0NGU1N2E4OWYiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_c042061a45cc167df49b6d76

public import Definitions.Def_Yukon_ac1fabbdddd4e4a4c0618520



public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Init
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
meta import Definitions.Def_Yukon_ac1fabbdddd4e4a4c0618520
meta import Definitions.Def_Yukon_c042061a45cc167df49b6d76
set_option backward.isDefEq.respectTransparency.types false
/-!
# Probability-weighted Cauchy-Schwarz / Jensen inequalities

Inequalities relating per-element bounds and their probabilistic averages, for use in
forking-lemma-style game-hopping arguments where the outermost step marginalizes over a
random key (or, more generally, an arbitrary `MonadLiftT m SPMF` monad output).

The headline lemma is `marginalized_jensen_forking_bound`: given a per-element bound
`acc x · (acc x / q − hinv) ≤ B x` and weights `Pr[= x | mx]` for some monadic computation
`mx`, the marginalized expectation `μ := 𝔼[acc]` satisfies the same shape:

  `μ · (μ / q − hinv) ≤ 𝔼[B]`.

The forking-lemma instantiation is `q := qH + 1`, `hinv := 1/|Chal|`, with `acc x` the
per-pk fork-success probability, `B x` the per-pk extraction-success probability, and
`mx := keygen`. The integration step is genuinely lossy (Cauchy-Schwarz on
`Pr[= · | mx]`), so this lemma sits at the heart of any keygen-marginalized fork-based
extraction bound.
-/

@[expose] public section

open ENNReal

universe u v

namespace OracleComp.EvalDist

variable {m : Type → Type v} [Monad m] [MonadLiftT m SPMF]

private lemma tsum_sub_tsum_le_tsum_sub {ι : Type*} (f g : ι → ℝ≥0∞)
    (_hg : ∑' i, g i ≠ ⊤) : (∑' i, f i) - ∑' i, g i ≤ ∑' i, (f i - g i) := by
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun i => le_tsub_add

omit [Monad m] in
/-- **Marginalized Jensen / Cauchy-Schwarz step for the forking lemma.**

If a per-element bound `acc x · (acc x / q − hinv) ≤ B x` holds for every `x` (with
`acc x ≤ 1`), and we marginalize over the output distribution of any `mx : m X` with
`[MonadLiftT m SPMF]`, then the marginalized expectation `μ := ∑' x, Pr[= x | mx] · acc x`
satisfies the same forking-bound shape:

  `μ · (μ / q − hinv) ≤ ∑' x, Pr[= x | mx] · B x`.

**Intended use.** In Pointcheval-Stern / Bellare-Neven style EUF-CMA-to-relation
reductions, instantiate as follows:

* `mx := hr.gen` (key generator),
* `acc (pk, sk) := Pr[fork point exists | run nmaAdv on pk]`,
* `B (pk, sk) := Pr[extraction succeeds | reduction pk]`,
* `q := qH + 1`, `hinv := 1 / |Chal|`.

The per-element hypothesis `hper` is then exactly the conclusion of `replayForkingBound`
(or `seededForkingBound`) at a fixed `pk`, composed with the special-soundness extractor.

This generalizes the obvious `[Fintype X]` Cauchy-Schwarz: the `tsum` form handles the
typical case where `X = Stmt × Wit` (uncountable in general, supported on whatever
keygen reaches). -/
lemma marginalized_jensen_forking_bound
    {X : Type} (mx : m X)
    (acc B : X → ℝ≥0∞) (q hinv : ℝ≥0∞)
    (hinv_ne_top : hinv ≠ ⊤)
    (hacc_le : ∀ x, acc x ≤ 1)
    (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    (∑' x, Pr[= x | mx] * acc x) *
        ((∑' x, Pr[= x | mx] * acc x) / q - hinv) ≤
      ∑' x, Pr[= x | mx] * B x := by
  classical
  set w : X → ℝ≥0∞ := fun x => Pr[= x | mx]
  set μ : ℝ≥0∞ := ∑' x, w x * acc x with hμ_def
  have hw_tsum_le_one : ∑' x, w x ≤ 1 := tsum_probOutput_le_one
  have hμ_le_one : μ ≤ 1 := by
    calc μ = ∑' x, w x * acc x := rfl
      _ ≤ ∑' x, w x * 1 := by gcongr with x; exact hacc_le x
      _ = ∑' x, w x := by simp
      _ ≤ 1 := hw_tsum_le_one
  have hμ_ne_top : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμ_le_one
  have hμ_hinv_ne_top : ∑' x, w x * acc x * hinv ≠ ⊤ := by
    rw [ENNReal.tsum_mul_right]; exact ENNReal.mul_ne_top hμ_ne_top hinv_ne_top
  have hCS : μ ^ 2 ≤ ∑' x, w x * acc x ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w acc hw_tsum_le_one
  calc μ * (μ / q - hinv)
      = μ ^ 2 / q - μ * hinv := by
        rw [ENNReal.mul_sub (fun _ _ => hμ_ne_top), sq, mul_div_assoc]
    _ ≤ (∑' x, w x * acc x ^ 2) / q - μ * hinv := by gcongr
    _ = (∑' x, w x * acc x ^ 2 / q) - ∑' x, w x * acc x * hinv := by
        rw [hμ_def]
        simp_rw [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, (w x * acc x ^ 2 / q - w x * acc x * hinv) :=
        tsum_sub_tsum_le_tsum_sub _ _ hμ_hinv_ne_top
    _ = ∑' x, w x * (acc x * (acc x / q - hinv)) := by
        refine tsum_congr fun x => ?_
        have hwx_ne_top : w x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
        have hax_ne_top : acc x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (hacc_le x)
        rw [ENNReal.mul_sub (fun _ _ => hax_ne_top), sq, mul_div_assoc,
          ENNReal.mul_sub (fun _ _ => hwx_ne_top), mul_div_assoc, mul_assoc]
    _ ≤ ∑' x, w x * B x := by gcongr with x; exact hper x

end OracleComp.EvalDist


