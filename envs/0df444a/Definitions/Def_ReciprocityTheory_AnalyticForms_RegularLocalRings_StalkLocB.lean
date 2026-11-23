-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:17.196137+00:00
-- url     : https://prove2.me/theorems/216e74f3-5feb-4f4f-9245-4f9ef9f6ee1f
-- title:
--   Stalk Loc B
-- statement:
--   Definitions and structural lemmas for Stalk Loc B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace ReciprocityTheory.AnForm.R
noncomputable section
namespace StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
def secH : MvPolynomial (Fin n) ℂ →+* Γ(W, V) :=
  V.topIso.hom.hom.comp (iso.hom.appTop.hom.comp
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom.comp (Ideal.Quotient.mk K)))
def phiH : (MvPolynomial (Fin n) ℂ ⧸ K) →+* Γ(W, V) :=
  V.topIso.hom.hom.comp (iso.hom.appTop.hom.comp
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom)
theorem phiH_bijective : Function.Bijective (phiH V K iso) := by
  have h1 : Function.Bijective V.topIso.hom.hom := (V.topIso.commRingCatIsoToRingEquiv).bijective
  haveI : IsIso iso.hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso iso.op).isIso_hom
  have h2 : Function.Bijective iso.hom.appTop.hom :=
    (asIso iso.hom.appTop).commRingCatIsoToRingEquiv.bijective
  have h3 : Function.Bijective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom :=
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).symm.commRingCatIsoToRingEquiv.bijective
  exact h1.comp (h2.comp h3)
def phiE : (MvPolynomial (Fin n) ℂ ⧸ K) ≃+* Γ(W, V) :=
  RingEquiv.ofBijective _ (phiH_bijective V K iso)
end StalkLocB
end
end ReciprocityTheory.AnForm.R


