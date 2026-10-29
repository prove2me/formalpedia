-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
-- name    : LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:46:15.816542+00:00
-- url     : https://prove2.me/theorems/52000f06-ee4e-43c2-882b-9f643365bbec
-- title:
--   LIDT definitions: LDT / Tactic / LdtSimpAttr
-- statement:
--   This bundle defines the opt-in simplification attribute used to keep LDT proof bookkeeping stable. The attribute lets selected declarations participate in `ldt_simp` without changing the ordinary global simplifier set.
--
--   Principal definitions:
--   - `ldt_simp`: the opt-in simplification attribute for stable LDT proof reductions.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Tactic/LdtSimpAttr.lean#L15-L16

-- Generated from MIPStarRE/LDT/Tactic/LdtSimpAttr.lean by skeleton subtraction.
import Mathlib.Tactic.Attr.Register

namespace LIDT

/-!
# Registration for the LDT-local simplifier set

This tiny module declares the opt-in `ldt_simp` simp set.  Lemmas are registered
in downstream modules, rather than here, because Lean cannot reliably use a simp
attribute in the same file that registers it.
-/

public meta section

/-- Opt-in simplification set for stable LDT proof boilerplate. -/
register_simp_attr ldt_simp

end

end LIDT


