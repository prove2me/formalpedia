-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:21.08+00:00
-- url     : https://prove2.me/theorems/8a817df6-6f8c-4660-b93e-9afd53bde4dd
-- title:
--   PProj Bundle Multi Homog
-- statement:
--   Definitions and structural lemmas for PProj Bundle Multi Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
section Weights
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def zDegInl : (K → ℕ) →+ (K ⊕ Unit → ℤ) :=
  AddMonoidHom.mk' (fun a x => Sum.elim (fun k => (a k : ℤ)) (fun _ => 0) x) (by
    intro a b
    funext x
    cases x <;> simp)
def zDeg : (K ⊕ Unit → ℕ) →+ (K ⊕ Unit → ℤ) := AddMonoidHom.compLeft (Nat.castAddMonoidHom ℤ) _
variable (ι) {S : Type} [Fintype S] (γ : S → K → ℕ)
def genericWeight : S ⊕ (Σ k, ι k) → (K ⊕ Unit → ℤ)
  | .inl s => Pi.single (Sum.inr ()) 1 - zDegInl (γ s)
  | .inr p => zDegInl (NumbersDVR.blockWeight ι p)
variable {ι} {N1 : ℕ}
def genericSubstitution (V : S → Fin N1 → MRing ι) : (Σ x, PBlk ι N1 x) → MvPolynomial (S ⊕ (Σ k, ι k)) ℤ
  | ⟨.inl k, i⟩ => X (.inr ⟨k, i⟩)
  | ⟨.inr _, j⟩ => ∑ s, rename Sum.inr (V s j) * X (.inl s)
end Weights
section Kernel
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]
def genericEvaluation (P : Ideal (MRing ι)) : MvPolynomial (S ⊕ (Σ k, ι k)) ℤ →+* MvPolynomial S (FnField P) :=
  (map (toFn P)).comp (sumAlgEquiv ℤ S (Σ k, ι k)).toAlgHom.toRingHom
end Kernel
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


