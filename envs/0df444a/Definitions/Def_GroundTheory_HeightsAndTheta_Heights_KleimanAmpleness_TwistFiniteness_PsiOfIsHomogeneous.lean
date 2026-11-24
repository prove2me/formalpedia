-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:35.436417+00:00
-- url     : https://prove2.me/theorems/fb930f7f-df54-444d-9e1f-d1ebf66906c2
-- title:
--   Psi Of Is Homogeneous
-- statement:
--   Definitions and structural lemmas for Psi Of Is Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
namespace TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
abbrev LA (Ω : Type w) [Field Ω] : Type w := AddMonoidAlgebra Ω (ℤ × ℤ)
set_option linter.unusedVariables false in

def Amb (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) : Type w := LA Ω
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)
instance : AddCommGroup (Amb x η) := inferInstanceAs (AddCommGroup (LA Ω))
instance : Module (LA Ω) (Amb x η) := inferInstanceAs (Module (LA Ω) (LA Ω))
def toA : Amb x η ≃+ LA Ω := AddEquiv.refl _
variable (S : Type u) [CommRing S] [Algebra S Ω]
abbrev Sy (S : Type u) [CommRing S] (r : ℕ) : Type u := MvPolynomial (Fin (r + 1)) S
def psi : Sy S r →ₐ[S] LA Ω := aeval fun j => single ((0 : ℤ), (1 : ℤ)) (η j)
def phi : Poly (Sy S r) N →+* LA Ω :=
  eval₂Hom (psi η S).toRingHom fun i => single ((1 : ℤ), (0 : ℤ)) (x i)
instance modP : Module (Poly (Sy S r) N) (Amb x η) := Module.compHom _ (phi x η S)
instance modSy : Module (Sy S r) (Amb x η) := Module.compHom _ (psi η S).toRingHom
theorem toA_smulP (p : Poly (Sy S r) N) (a : Amb x η) : toA x η (p • a) = phi x η S p * toA x η a := rfl
theorem toA_smulSy (s : Sy S r) (a : Amb x η) : toA x η (s • a) = psi η S s * toA x η a := rfl
theorem phi_C (s : Sy S r) : phi x η S (C s) = psi η S s := eval₂Hom_C _ _ _
instance : IsScalarTower (Sy S r) (Poly (Sy S r) N) (Amb x η) where
  smul_assoc s p a := by
    apply (toA x η).injective
    rw [toA_smulP, toA_smulSy, toA_smulP, MvPolynomial.smul_eq_C_mul, map_mul, phi_C, mul_assoc]
abbrev tgr (c : ℤ) : Submodule Ω (LA Ω) := gradeBy Ω (AddMonoidHom.fst ℤ ℤ) c
def kapT : Polynomial Ω →ₐ[Ω] LA Ω := Polynomial.aeval (single ((1 : ℤ), (0 : ℤ)) 1)
def kapU : Polynomial Ω →ₐ[Ω] LA Ω := Polynomial.aeval (single ((0 : ℤ), (1 : ℤ)) 1)
end TwistFin
end
end GroundTheory.Heights₂.Heights.Kleiman


