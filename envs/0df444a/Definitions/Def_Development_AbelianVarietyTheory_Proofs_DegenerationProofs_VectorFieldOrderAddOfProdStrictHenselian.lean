-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T20:16:54.946418+00:00
-- url     : https://prove2.me/theorems/050de731-24c5-4740-bb19-37bc1eb00e24
-- title:
--   Vector Field Order Add Of Prod Strict Henselian
-- statement:
--   Definitions and structural lemmas for Vector Field Order Add Of Prod Strict Henselian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VectorFieldOrderAddOfProdStrictHenselian.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.OrdProd
section Alg
variable {B E L J : Type} [CommRing B] [CommRing E] [Fintype L] (φ : B →+* E) (d : J → E →+ E)
  (T : L → B)
def InSpan (τ : B) : Prop := ∃ r : L → B, ∀ i, d i (φ τ) = ∑ l, φ (r l) * d i (φ (T l))
variable {φ d T}
end Alg
variable {K : Type} [Field K]
def Lifts {P X : Over (Sp K)} (p : P ⟶ X) (E : VF P) (D : VF X) : Prop :=
  ∀ (V : X.left.Opens) (W : P.left.Opens) (h : W ≤ p.left ⁻¹ᵁ V) (u : Γ(X.left, V)),
    E.D W ((p.left.appLE V W h).hom u) = (p.left.appLE V W h).hom (D.D V u)
section Mod
variable {R : Type} [CommRing R] [Algebra R K] {A A' : Over (Sp K)}
theorem pre_le {Q : Model R A'} {M : Model R A} {p : A' ⟶ A} {p' : Q.Y.left ⟶ M.Y.left}
    (e : Q.j ≫ p' = p.left ≫ M.j) {V : M.Y.left.Opens} {W : Q.Y.left.Opens} (h : W ≤ p' ⁻¹ᵁ V) :
    Q.j ⁻¹ᵁ W ≤ p.left ⁻¹ᵁ (M.j ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← e, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ h
def JacEq {I : Type} [Fintype I] [DecidableEq I] (M : Model R A) (D : I → VF A) (c : K) (U : M.Y.left.Opens)
    (t : I → Γ(M.Y.left, U)) (s : Γ(M.Y.left, U)) : Prop :=
  jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ c * (M.j.app U).hom s
end Mod
end GlobalTheory.SS.OrdProd
end


