-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:37.55385+00:00
-- url     : https://prove2.me/theorems/e56cfbda-57eb-4481-b92f-a572d2148dbb
-- title:
--   Exists Basic Open Cover
-- statement:
--   Definitions and structural lemmas for Exists Basic Open Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
section Top
variable {α : Type*} [TopologicalSpace α]
def comps (T : Set α) : Set (Set α) :=
  {C | Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C}
end Top
variable {W : Scheme.{0}}
def IsBranch (T : Set W) {U : W.Opens} (f : Γ(W, U)) (y : W) (C : Set W) : Prop :=
  C ∈ comps T ∧ y ∈ C ∧ ∃ h : IsIrreducible C, h.genericPoint ∈ U ∧ h.genericPoint ∈ W.zeroLocus {f}
section Chart
variable {s : W ⟶ Spec (.of ℂ)}
theorem AffPres.isAffineOpen (P : AffPres s) : IsAffineOpen P.V := by
  first
  | exact IsAffine.of_isIso P.iso.hom
  | exact AlgebraicGeometry.isAffine_of_isIso P.iso.hom
  | exact (inferInstance : IsAffine (Spec (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).of_isIso P.iso.hom
  | exact isAffine_of_isIso P.iso.hom
def AffPres.affOpen (P : AffPres s) : W.affineOpens := ⟨P.V, P.isAffineOpen⟩
def AffPres.bdIdeal (P : AffPres s) (Z : W.IdealSheafData) : Ideal (MvPolynomial (Fin P.n) ℂ) :=
  (Z.ideal P.affOpen).comap P.secHom
end Chart
end
end ReciprocityTheory.AnForm.R


