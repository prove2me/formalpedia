-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:09.920336+00:00
-- url     : https://prove2.me/theorems/7846c234-ea09-4f59-a4c4-32a86b1a4c3c
-- title:
--   Closure From Spec Mem Comps H
-- statement:
--   Definitions and structural lemmas for Closure From Spec Mem Comps H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
def IsBranchH (T : Set W) {U : W.Opens} (f : Γ(W, U)) (y : W) (C : Set W) : Prop :=
  C ∈ compsH T ∧ y ∈ C ∧ ∃ h : IsIrreducible C, h.genericPoint ∈ U ∧ h.genericPoint ∈ W.zeroLocus {f}
def ParPrimes {U : W.Opens} (hU : IsAffineOpen U) {y : W} (hy : y ∈ U) {n : ℕ} (f : Fin n → Γ(W, U))
    (q : Fin n → PrimeSpectrum Γ(W, U)) : Prop :=
  (∀ i, q i ≤ hU.primeIdealOf ⟨y, hy⟩) ∧ (∀ i, f i ∈ (q i).asIdeal) ∧
  (∀ i (Q : PrimeSpectrum Γ(W, U)), Q ≤ hU.primeIdealOf ⟨y, hy⟩ → (f i ∈ Q.asIdeal ↔ q i ≤ Q)) ∧
  (∀ i j, f j ∈ (q i).asIdeal → j = i)
section Br
variable {Z : W.IdealSheafData} {U : W.Opens} {hU : IsAffineOpen U} {y : W} {hy : y ∈ U} {n : ℕ}
  {f : Fin n → Γ(W, U)} {J : Finset (Fin n)} {q : Fin n → PrimeSpectrum Γ(W, U)}
end Br
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages


