-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneCharacters_NormOneCharacterApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneCharacters_NormOneCharacterApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:13.960413+00:00
-- url     : https://prove2.me/theorems/9d6b2a84-e4f1-4765-bf05-b24f538d383a
-- title:
--   Norm One Character Apply
-- statement:
--   Definitions and structural lemmas for Norm One Character Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ChiExCM
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.ChiExCM
open NumberField
section
variable {E : Type} [Field E] [NumberField E]
noncomputable def spanHom : E →* Submodule (𝓞 E) E where
  toFun x := Submodule.span (𝓞 E) {x}
  map_one' := Submodule.one_eq_span.symm
  map_mul' x y := by
    show Submodule.span (𝓞 E) {x * y} = Submodule.span (𝓞 E) {x} * Submodule.span (𝓞 E) {y}
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
def normOne (c : E →+* E) : Subgroup Eˣ where
  carrier := {u | (u : E) * c u = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at *
    calc (a : E) * b * (c a * c b) = ((a : E) * c a) * ((b : E) * c b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at *
    rw [← mul_inv, ha, inv_one]
noncomputable def iota (c : E →+* E) : normOne c →* (Submodule (𝓞 E) E)ˣ :=
  (Units.map spanHom).comp (normOne c).subtype
noncomputable def lam (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ) : normOne c →* ℂˣ :=
  (∏ s, (Units.map (emb s).toMonoidHom).comp (normOne c).subtype)⁻¹
noncomputable def chi0 (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ)
    (hker : (iota c).ker ≤ (lam c S emb).ker) : (iota c).range →* ℂˣ :=
  (QuotientGroup.lift (iota c).ker (lam c S emb) hker).comp
    (QuotientGroup.quotientKerEquivRange (iota c)).symm.toMonoidHom
end
end PI.UnitaryGroupMassFormula.ChiExCM


