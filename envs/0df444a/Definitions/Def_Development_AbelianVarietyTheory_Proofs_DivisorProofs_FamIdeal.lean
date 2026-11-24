-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T19:12:59.81177+00:00
-- url     : https://prove2.me/theorems/59359480-6129-432b-a3e4-7ff57e993b5c
-- title:
--   Fam Ideal
-- statement:
--   Definitions and structural lemmas for Fam Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FamIdeal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.NormSheafDescent
abbrev genPt {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) : Z := π (genericPoint Y)
abbrev fieldK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z)
    (hK : IsField (Z.presheaf.stalk (genPt π))) : Field (Z.presheaf.stalk (genPt π)) :=
  hK.toField
abbrev algKL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) :
    Algebra (Z.presheaf.stalk (genPt π)) Y.functionField :=
  (π.stalkMap (genericPoint Y)).hom.toAlgebra
abbrev algAK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Z, U) (Z.presheaf.stalk (genPt π)) :=
  (Z.presheaf.germ U (genPt π) h).hom.toAlgebra
abbrev algBL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
  (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) h).hom.toAlgebra
open scoped Classical in

def famIdeal {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) [IsAffineHom π]
    (hK : IsField (Z.presheaf.stalk (genPt π)))
    (hfd : letI := fieldK π hK; letI := algKL π
      FiniteDimensional (Z.presheaf.stalk (genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) : Ideal Γ(Z, U) :=
  if h : genPt π ∈ U.1 then
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    GlobalTheory.NormSheaf.normIdeal Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
  else ⊤
end GlobalTheory.NormSheafDescent


