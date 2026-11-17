-- Prove2me | Definitions.Def_N25_CharacterField
-- name    : N25_CharacterField
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:17.209985+00:00
-- url     : https://prove2.me/theorems/133ba501-aee2-49c3-a32d-02abd22c5963
-- title:
--   The quintic character subfield of the $25$th cyclotomic field
-- statement:
--   Let $L=ℚ(ζ_{25})$. The file equips $L$ with its number-field structure, identifies $\operatorname{Gal}(L/ℚ)$ with $(ℤ/25ℤ)^×$, pulls the subgroup $H_{25}$ back to the cyclotomic Galois group, and defines the fixed field $$E=L^{H_{25}}.$$ This quintic number field is the coefficient field on which the global Kummer character is analyzed.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
noncomputable section
namespace N25
/-- The 25th cyclotomic field containing the character field. -/
abbrev cyclotomicField := CyclotomicField 25 ℚ
instance : IsCyclotomicExtension {25} ℚ cyclotomicField := by
  letI : NeZero (25 : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension 25 ℚ
instance : NumberField cyclotomicField :=
  IsCyclotomicExtension.numberField {25} ℚ cyclotomicField
/-- The cyclotomic action identifies the Galois group with units modulo 25. -/
def cyclotomicAutEquiv : (cyclotomicField ≃ₐ[ℚ] cyclotomicField) ≃* (ZMod 25)ˣ :=
  IsCyclotomicExtension.autEquivPow cyclotomicField
    (Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 25))
/-- The subgroup H25 in the cyclotomic Galois group. -/
def characterSubgroup : Subgroup (cyclotomicField ≃ₐ[ℚ] cyclotomicField) :=
  H25.comap cyclotomicAutEquiv.toMonoidHom
/-- The quintic character field Q(zeta25)^H25. -/
def characterField : IntermediateField ℚ cyclotomicField :=
  IntermediateField.fixedField characterSubgroup
instance : NumberField characterField := NumberField.of_module_finite ℚ characterField
end N25


