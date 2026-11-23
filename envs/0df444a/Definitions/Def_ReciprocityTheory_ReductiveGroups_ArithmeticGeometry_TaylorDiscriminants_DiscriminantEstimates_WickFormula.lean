-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_WickFormula
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_WickFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:18.725031+00:00
-- url     : https://prove2.me/theorems/ede460b8-62ae-4e76-8533-799218ca8f34
-- title:
--   Wick Formula
-- statement:
--   Definitions and structural lemmas for Wick Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/WickFormula.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace PI
namespace WickFormula
noncomputable def ordEval {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA] {r s : ℕ}
    (a : Fin r → AA) (a' : Fin s → AA) (P : MvPolynomial (Fin r ⊕ Fin s) k) : AA :=
  ∑ m ∈ P.support, P.coeff m • ((List.ofFn fun i => a i ^ m (Sum.inl i)).prod *
    (List.ofFn fun j => a' j ^ m (Sum.inr j)).prod)
noncomputable def delta {k : Type} [CommRing k] {r s : ℕ} (κ : Fin r → Fin s → k) :
    MvPolynomial (Fin r ⊕ Fin s) k →ₗ[k] MvPolynomial (Fin r ⊕ Fin s) k :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)
end WickFormula
open WickFormula in

def WickFormula : Prop :=
  ∀ (k AA M : Type) [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
    [Module AA M] (r s : ℕ) (a b : Fin r → AA) (a' b' : Fin s → AA) (κ : Fin r → Fin s → k)
    (σ₀ : M),
    (∀ i i', Commute (a i) (a i') ∧ Commute (a i) (b i') ∧ Commute (b i) (b i')) →
    (∀ j j', Commute (a' j) (a' j') ∧ Commute (a' j) (b' j') ∧ Commute (b' j) (b' j')) →
    (∀ i j, Commute (b i) (b' j)) →
    (∀ i j, b i * a' j - a' j * b i = algebraMap k AA (κ i j)) →
    (∀ i, b i • σ₀ = 0) → (∀ j, b' j • σ₀ = 0) →
    ∀ P : MvPolynomial (Fin r ⊕ Fin s) k,
      ordEval (a + b) (a' + b') P • σ₀ =
        ∑ n ∈ Finset.range (P.totalDegree + 1),
          ordEval a a' ((n.factorial : ℚ)⁻¹ • (delta κ ^ n) P) • σ₀
end PI


