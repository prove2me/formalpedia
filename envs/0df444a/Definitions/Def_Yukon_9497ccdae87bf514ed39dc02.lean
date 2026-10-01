-- Prove2me | Definitions.Def_Yukon_9497ccdae87bf514ed39dc02
-- name    : Yukon_9497ccdae87bf514ed39dc02
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:08:37.776746+00:00
-- url     : https://prove2.me/theorems/ec540126-7bbd-4755-b725-5b443ec7e8e9
-- title:
--   YukonModule.ArkLib.Data.CodingTheory.ProximityGap.TensorGenerator.part0
-- statement:
--   Source module ArkLib.Data.CodingTheory.ProximityGap.TensorGenerator. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/ProximityGap/TensorGenerator.lean
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/ProximityGap/TensorGenerator.lean
--
--   yukon-proof-operation:6733b7d1dbf695a58614207f2367f4f50dff26521bb7d493facb2e8cc8b37503
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NjczM2I3ZDFkYmY2OTVhNTg2MTQyMDdmMjM2N2Y0ZjUwZGZmMjY1MjFiYjdkNDkzZmFjYjJlOGNjOGIzNzUwMyIsImhhc2giOiJiMDYxN2UyMjQ1YTA4NDMzYzQ5MzUzNzM4ZjVmMmEwYzA4MGFhNWVjYzVkMGI4MDIzYzJiNTAzYWI0OTAyZjM5Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85NDk3Y2NkYWU4N2JmNTE0ZWQzOWRjMDIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Definitions.Def_Yukon_7ec25d71d45b2c1c93aeaa4b

import Definitions.Def_Yukon_57f2f4a582b59c53cdee835d

import Definitions.Def_Yukon_73cb364285b0db29404203c2



import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Order.Star.Basic
import Init
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Notation
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Algebra.Order.Floor.Semifield
set_option backward.isDefEq.respectTransparency.types false
/-!
# Mutual correlated agreement for tensor generators

The tensor generator `G ⊗ G'` combines a family indexed by `ℓ × ℓ'` by applying `G'` across each
row and then `G` across the results. Its mutual correlated agreement error is bounded here in two
forms, differing in which hypothesis is placed on the inner generator `G'`.

Writing `W x' i := ∑ j, G' x' j • U (i, j)` for the `G'`-combined rows, the tensor combination is
the `G`-combination of `W x'`. The bad event splits on whether some row `W x' i` fails to project
into the code on the witness set `T`. If some row fails, the event implies `G`'s at the family
`W x'`. If none does, it implies `G'`'s — but at which family depends on the hypothesis available:

* given MCA for the `ℓ`-fold interleaving, the family is the stack
  `w j := (k, i) ↦ U (i, j) k`, which does not depend on the outer seed, and the errors add;
* given MCA for the base code only, the row witnessing failure depends on the outer seed, so a
  union bound over the `ℓ` rows is forced and the inner error is paid `ℓ` times.

The interleaved hypothesis is the stronger of the two, but it buys the stronger conclusion, so
neither form subsumes the other and both are proved. The correspondence to
[BCGM25]'s printed Lemma 4.4, which assumes the base code and claims the added error, is recorded
in `docs/kb/audits/bcgm25-mca-generators.md` together with the argument that the paper's own proof
reaches only these two forms.

Note that the error bound is typed `I → ℝ≥0` rather than `I → I`, so an added or scaled error is
vacuous once it reaches `1`.

## Main statements

* `TensorMCA.isMCAGenerator_tensorGenerator` — given MCA for the base code, errors add with the
  inner one scaled by `Fintype.card ℓ`.
* `TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` — given MCA for the
  `ℓ`-fold interleaving instead, the errors add unscaled.
* `TensorMCA.isMCAGenerator_of_moduleInterleavedCode` — MCA for the interleaving implies MCA for
  the base code at the same error, so the interleaved hypothesis is the stronger of the two.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
    with Mutual Correlated Agreement*][BCGM25]
-/

namespace TensorMCA

open NNReal ENNReal unitInterval LinearCode CoreDefinitions Code
open scoped ProbabilityTheory
open Probability

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {A : Type} [AddCommMonoid A] [Module F A]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S S' : Type} [Fintype S] [Fintype S'] [Nonempty S] [Nonempty S']

/-- If `G` has mutual correlated agreement with error `ε_mca` for `MC`, and `G'` has it with error
`ε'_mca` for the `ℓ`-fold interleaving of `MC`, then the tensor generator has it for `MC` with the
errors added.

Stated for `TensorGenerator_Explicit`, the componentwise form, which is the one that is a
`Generator`; `TensorGenerator` lands in the tensor product and the two agree under
`tensorProductPiFunEquiv`.

Writing `W x' i := ∑ j, G' x' j • U (i, j)`, the tensor combination is the `G`-combination of
`W x'`. Case-split on whether some `W x' i` fails to project into the code on the witness set `T`:
if so, the tensor event implies `G`'s event at the family `W x'`; if not, it implies `G'`'s event
at the interleaved family `w j := (k, i) ↦ U (i, j) k`, which is independent of `x'`. A union
bound over the two cases gives the sum. -/
theorem isMCAGenerator_tensorGenerator_of_moduleInterleavedCode
    (G : Generator S ℓ F) (G' : Generator S' ℓ' F)
    (ε_mca ε'_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hG : IsMCAGenerator G ε_mca MC)
    (hG' : IsMCAGenerator G' ε'_mca (ModuleCode.moduleInterleavedCode F A ℓ ι MC)) :
    IsMCAGenerator (TensorGenerator_Explicit G G') (ε_mca + ε'_mca) MC := by
  intro δ
  refine iSup_le fun U => ?_
  classical
  -- the `G'`-combined rows, per outer seed `x'`
  set W : S' → ℓ → (ι → A) := fun x' i k => ∑ j, G' x' j • U (i, j) k with hW
  -- the `x'`-independent interleaved family
  set w : ℓ' → (ι → InterleavedSymbol A ℓ) := fun j k i => U (i, j) k with hw
  -- the tensor combination is the `G`-combination of the `W`-rows
  have hv : ∀ (x : S) (x' : S'),
      (fun k => ∑ p : ℓ × ℓ', TensorGenerator_Explicit G G' (x, x') p • U p k)
        = fun k => ∑ i, G x i • W x' i k := by
    intro x x'
    funext k
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp [TensorGenerator_Explicit, mul_smul]
  -- rows of the `G'`-combination of `w` are the `W`-rows
  have hrow : ∀ (x' : S') (i : ℓ),
      InterleavedWord.getRowWord (fun k => ∑ j, G' x' j • w j k) i = W x' i := by
    intro x' i
    funext k
    simp [hw, hW, InterleavedWord.getRowWord, Finset.sum_apply]
  -- the case split: the tensor event implies one of the two MCA events
  have himp : ∀ p : S × S', IsMCA (TensorGenerator_Explicit G G') MC p U δ →
      IsMCA G MC p.1 (W p.2) δ ∨
        IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ := by
    rintro ⟨x, x'⟩ ⟨T, hT, hcomb, ⟨i₀, j₀⟩, hbad⟩
    rw [hv x x'] at hcomb
    by_cases hcase : ∃ i, projectedWord (W x' i) T ∉ projectedCodeSubmod MC T
    · exact Or.inl ⟨T, hT, hcomb, hcase⟩
    · push Not at hcase
      refine Or.inr ⟨T, hT, ?_, j₀, fun hmem => hbad ?_⟩
      · rw [projectedCodeSubmod_moduleInterleavedCode_iff]
        intro i
        rw [hrow x' i]
        exact hcase i
      · have h := (projectedCodeSubmod_moduleInterleavedCode_iff
          F A ℓ ι MC (w j₀) T).mp hmem i₀
        have hwrow : InterleavedWord.getRowWord (w j₀) i₀ = U (i₀, j₀) := by
          funext k; simp [hw, InterleavedWord.getRowWord]
        rwa [hwrow] at h
  -- assemble: implication, union bound, and the two marginal bounds
  have hA : (((do { let p ← $ᵖ (S × S'); return (IsMCA G MC p.1 (W p.2) δ) }) True) : ENNReal)
      ≤ (ε_mca δ : ENNReal) := by
    rw [prob_split_uniform_sampling_of_equiv_prod (Equiv.prodComm S S')
      (fun p => IsMCA G MC p.1 (W p.2) δ)]
    exact Pr_seq_le_of_forall_le _ _ _ fun x' => hG.prob_le (W x') δ
  have hB : (((do { let p ← $ᵖ (S × S'); return (
        IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ) }) True) : ENNReal)
      ≤ (ε'_mca δ : ENNReal) := by
    rw [prob_split_uniform_sampling_of_prod
      (fun p => IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ)]
    exact Pr_seq_le_of_forall_le _ _ _ fun _ => hG'.prob_le w δ
  calc (((do { let p ← $ᵖ (S × S'); return (IsMCA (TensorGenerator_Explicit G G') MC p U δ) }) True) : ENNReal)
      ≤ (((do { let p ← $ᵖ (S × S'); return (IsMCA G MC p.1 (W p.2) δ ∨
          IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ) }) True) : ENNReal) :=
        Pr_le_Pr_of_implies _ _ _ himp
    _ ≤ (((do { let p ← $ᵖ (S × S'); return (IsMCA G MC p.1 (W p.2) δ) }) True) : ENNReal)
        + (((do { let p ← $ᵖ (S × S'); return (
            IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ) }) True) : ENNReal) :=
        Pr_or_le _ _ _
    _ ≤ (ε_mca δ : ENNReal) + (ε'_mca δ : ENNReal) := add_le_add hA hB
    _ = ((ε_mca + ε'_mca) δ : ENNReal) := by
        rw [Pi.add_apply, ENNReal.coe_add]

omit [Fintype ℓ] in
/-- Mutual correlated agreement for the `ℓ`-fold interleaving implies it for the base code, at the
same error: stack a base family as an interleaved family with constant rows.

So the hypothesis of `isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` is the stronger of
the two. -/
theorem isMCAGenerator_of_moduleInterleavedCode [Nonempty ℓ] (G' : Generator S' ℓ' F)
    (ε'_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hG' : IsMCAGenerator G' ε'_mca (ModuleCode.moduleInterleavedCode F A ℓ ι MC)) :
    IsMCAGenerator G' ε'_mca MC := by
  intro δ
  refine iSup_le fun U => ?_
  refine le_trans (Pr_le_Pr_of_implies _ _ _ fun x' => ?_) (hG'.prob_le (fun j k _ => U j k) δ)
  rintro ⟨T, hT, hcomb, j₀, hbad⟩
  refine ⟨T, hT, ?_, j₀, fun hmem => hbad ?_⟩
  · rw [projectedCodeSubmod_moduleInterleavedCode_iff]
    intro i
    have : InterleavedWord.getRowWord (fun k => ∑ j, G' x' j • (fun k _ => U j k : ι → ℓ → A) k) i
        = fun k => ∑ j, G' x' j • U j k := by
      funext k
      simp [InterleavedWord.getRowWord, Finset.sum_apply]
    rw [this]
    exact hcomb
  · obtain ⟨i⟩ := ‹Nonempty ℓ›
    have h := (projectedCodeSubmod_moduleInterleavedCode_iff
      F A ℓ ι MC (fun k _ => U j₀ k) T).mp hmem i
    have hrow : InterleavedWord.getRowWord (fun k (_ : ℓ) => U j₀ k) i = U j₀ := by
      funext k; simp [InterleavedWord.getRowWord]
    rwa [hrow] at h

/-- If `G` and `G'` both have mutual correlated agreement for `MC` itself, the tensor generator has
it for `MC` with the inner error scaled by `Fintype.card ℓ`.

The factor is forced by this route: without the interleaved hypothesis of
`isMCAGenerator_tensorGenerator_of_moduleInterleavedCode`, the row witnessing non-membership
depends on the outer seed `x'`,
so the family fed to `G'` is not fixed and a union bound over the `ℓ` rows is required. -/
theorem isMCAGenerator_tensorGenerator (G : Generator S ℓ F) (G' : Generator S' ℓ' F)
    (ε_mca ε'_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hG : IsMCAGenerator G ε_mca MC)
    (hG' : IsMCAGenerator G' ε'_mca MC) :
    IsMCAGenerator (TensorGenerator_Explicit G G') (ε_mca + Fintype.card ℓ • ε'_mca) MC := by
  intro δ
  refine iSup_le fun U => ?_
  classical
  set W : S' → ℓ → (ι → A) := fun x' i k => ∑ j, G' x' j • U (i, j) k with hW
  have hv : ∀ (x : S) (x' : S'),
      (fun k => ∑ p : ℓ × ℓ', TensorGenerator_Explicit G G' (x, x') p • U p k)
        = fun k => ∑ i, G x i • W x' i k := by
    intro x x'
    funext k
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp [TensorGenerator_Explicit, mul_smul]
  -- case split: either `G`'s event at the combined rows, or `G'`'s event at SOME row —
  -- the row index depends on the seed pair, whence the union bound below
  have himp : ∀ p : S × S', IsMCA (TensorGenerator_Explicit G G') MC p U δ →
      IsMCA G MC p.1 (W p.2) δ ∨ ∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ := by
    rintro ⟨x, x'⟩ ⟨T, hT, hcomb, ⟨i₀, j₀⟩, hbad⟩
    rw [hv x x'] at hcomb
    by_cases hcase : ∃ i, projectedWord (W x' i) T ∉ projectedCodeSubmod MC T
    · exact Or.inl ⟨T, hT, hcomb, hcase⟩
    · push Not at hcase
      exact Or.inr ⟨i₀, T, hT, hcase i₀, j₀, hbad⟩
  have hA : (((do { let p ← $ᵖ (S × S'); return (IsMCA G MC p.1 (W p.2) δ) }) True) : ENNReal)
      ≤ (ε_mca δ : ENNReal) := by
    rw [prob_split_uniform_sampling_of_equiv_prod (Equiv.prodComm S S')
      (fun p => IsMCA G MC p.1 (W p.2) δ)]
    exact Pr_seq_le_of_forall_le _ _ _ fun x' => hG.prob_le (W x') δ
  have hB : (((do { let p ← $ᵖ (S × S'); return (∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ) }) True) : ENNReal)
      ≤ (Fintype.card ℓ : ENNReal) * (ε'_mca δ : ENNReal) := by
    rw [prob_split_uniform_sampling_of_prod
      (fun p => ∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ)]
    refine Pr_seq_le_of_forall_le _ _ _ fun _ => le_trans (Pr_exists_le _ _) ?_
    have hsum : ∑ i : ℓ, (((do { let x' ← $ᵖ S'; return (IsMCA G' MC x' (fun j => U (i, j)) δ) }) True) : ENNReal)
        ≤ ∑ _i : ℓ, (ε'_mca δ : ENNReal) := by
      exact Finset.sum_le_sum fun i _ => hG'.prob_le (fun j => U (i, j)) δ
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  calc (((do { let p ← $ᵖ (S × S'); return (IsMCA (TensorGenerator_Explicit G G') MC p U δ) }) True) : ENNReal)
      ≤ (((do { let p ← $ᵖ (S × S'); return (IsMCA G MC p.1 (W p.2) δ ∨
          ∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ) }) True) : ENNReal) :=
        Pr_le_Pr_of_implies _ _ _ himp
    _ ≤ (((do { let p ← $ᵖ (S × S'); return (IsMCA G MC p.1 (W p.2) δ) }) True) : ENNReal)
        + (((do { let p ← $ᵖ (S × S'); return (∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ) }) True) : ENNReal) :=
        Pr_or_le _ _ _
    _ ≤ (ε_mca δ : ENNReal)
        + (Fintype.card ℓ : ENNReal) * (ε'_mca δ : ENNReal) := add_le_add hA hB
    _ = ((ε_mca + Fintype.card ℓ • ε'_mca) δ : ENNReal) := by
        rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, ENNReal.coe_add, ENNReal.coe_mul,
          ENNReal.coe_natCast]

end TensorMCA


