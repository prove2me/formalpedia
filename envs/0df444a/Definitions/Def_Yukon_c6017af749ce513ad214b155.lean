-- Prove2me | Definitions.Def_Yukon_c6017af749ce513ad214b155
-- name    : Yukon_c6017af749ce513ad214b155
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:03:36.998976+00:00
-- url     : https://prove2.me/theorems/2989878a-0b5f-4e54-865f-371d66f93984
-- title:
--   YukonModule.VCVio.EvalDist.RenyiDivergence.part0
-- statement:
--   Source module VCVio.EvalDist.RenyiDivergence.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/RenyiDivergence.lean
--
--   yukon-proof-operation:8fe17c35547dbb7216fe3fa62cc2acab4027218c53aa0322789a086a85dfa776
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OGZlMTdjMzU1NDdkYmI3MjE2ZmUzZmE2MmNjMmFjYWI0MDI3MjE4YzUzYWEwMzIyNzg5YTA4NmE4NWRmYTc3NiIsImhhc2giOiJlNDgwMTVhMDNhZjFlNzk1OTVlNGIyMjQ3NjI2OTk3NzU1NWE4Y2I4NjJhOTU3YTYwZTM4ZmE1ZDg5NDIxZDU2Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9jNjAxN2FmNzQ5Y2U1MTNhZDIxNGIxNTUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_f588a8e35720876de725963a

public import Definitions.Def_Yukon_bb6a74fb27943bb3c66baf5c



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
meta import Definitions.Def_Yukon_f588a8e35720876de725963a
meta import Definitions.Def_Yukon_bb6a74fb27943bb3c66baf5c
set_option backward.isDefEq.respectTransparency.types false
/-!
# Rényi Divergence for SPMFs and Monadic Computations

This file extends the Rényi divergence from `PMF` (defined in
`ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence`) to:

1. `SPMF.renyiDiv` — on sub-probability mass functions (via `toPMF`)
2. `renyiDiv` — on any monad with `MonadLiftT m SPMF` (via `evalDist`)

This mirrors the structure of `VCVio.EvalDist.TVDist`, which performs the same lift for
total variation distance.

## Application

The monadic `renyiDiv` is used to state sampler quality bounds:

```
renyiDiv a (concreteSamplerZ μ σ') (idealSamplerZ μ σ') ≤ 1 + ε
```

where `concreteSamplerZ` uses FPR arithmetic and `idealSamplerZ` samples from the exact
discrete Gaussian. The probability preservation theorem then translates this into a
security loss factor in the Falcon EUF-CMA proof.
-/

@[expose] public section

noncomputable section

open ENNReal

universe u v

/-! ### SPMF.renyiDiv -/

namespace SPMF

variable {α : Type*}

/-- Rényi MGF on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def renyiMGF (a : ℝ) (p q : SPMF α) : ℝ≥0∞ :=
  p.toPMF.renyiMGF a q.toPMF

/-- Multiplicative Rényi divergence on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def renyiDiv (a : ℝ) (p q : SPMF α) : ℝ≥0∞ :=
  p.toPMF.renyiDiv a q.toPMF

/-- Max-divergence on SPMFs. -/
protected def maxDiv (p q : SPMF α) : ℝ≥0∞ := p.toPMF.maxDiv q.toPMF

@[simp]
theorem renyiDiv_self (a : ℝ) (p : SPMF α) : p.renyiDiv a p = 1 :=
  PMF.renyiDiv_self _ _

universe w in
theorem renyiDiv_map_le (a : ℝ) (ha : 1 < a) {α' : Type w} {β : Type w}
    (f : α' → β) (p q : SPMF α') :
    SPMF.renyiDiv a (f <$> p) (f <$> q) ≤ SPMF.renyiDiv a p q := by
  simpa only [SPMF.renyiDiv, SPMF.toPMF_map] using
    PMF.renyiDiv_map_le a ha (Option.map f) p.toPMF q.toPMF

universe w in
theorem renyiDiv_bind_right_le (a : ℝ) (ha : 1 < a) {α' : Type w} {β : Type w}
    (f : α' → SPMF β) (p q : SPMF α') :
    SPMF.renyiDiv a (p >>= f) (q >>= f) ≤ SPMF.renyiDiv a p q := by
  simpa only [SPMF.renyiDiv, SPMF.toPMF_bind, Option.elimM, PMF.monad_bind_eq_bind] using
    PMF.renyiDiv_bind_right_le a ha _ p.toPMF q.toPMF

end SPMF

/-! ### Monadic renyiDiv -/

section monadic

variable {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] {α : Type u}

/-- Rényi divergence between two monadic computations,
defined via their evaluation distributions. -/
noncomputable def renyiDiv (a : ℝ) (mx my : m α) : ℝ≥0∞ :=
  SPMF.renyiDiv a (𝒟[mx]) (𝒟[my])

omit [Monad m] [LawfulMonadLiftT m SPMF] in
@[simp]
theorem renyiDiv_self (a : ℝ) (mx : m α) : renyiDiv a mx mx = 1 :=
  SPMF.renyiDiv_self _ _

theorem renyiDiv_map_le [LawfulMonad m] {β : Type u} (a : ℝ) (ha : 1 < a)
    (f : α → β) (mx my : m α) :
    renyiDiv a (f <$> mx) (f <$> my) ≤ renyiDiv a mx my := by
  simpa only [renyiDiv, _root_.evalDist_map] using SPMF.renyiDiv_map_le a ha f _ _

theorem renyiDiv_bind_right_le [LawfulMonad m] {β : Type u} (a : ℝ) (ha : 1 < a)
    (f : α → m β) (mx my : m α) :
    renyiDiv a (mx >>= f) (my >>= f) ≤ renyiDiv a mx my := by
  simpa only [renyiDiv, _root_.evalDist_bind] using SPMF.renyiDiv_bind_right_le a ha _ _ _

/-! ### Rényi to Probability Bounds -/

omit [Monad m] [LawfulMonadLiftT m SPMF] in
/-- If the Rényi divergence between two computations is at most `R`, then for any
output `x`, `Pr[= x | my] ≥ Pr[= x | mx]^{a/(a-1)} / R`. -/
theorem probOutput_le_of_renyiDiv (a : ℝ) (ha : 1 < a) (mx my : m α)
    (R : ℝ≥0∞) (hR : renyiDiv a mx my ≤ R) (x : α) :
    Pr[= x | mx] ^ (a / (a - 1) : ℝ) / R ≤ Pr[= x | my] := by
  simp only [probOutput, renyiDiv, SPMF.renyiDiv] at *
  exact (ENNReal.div_le_div_left hR _).trans (PMF.renyiDiv_apply_bound a ha _ _ _)

end monadic


