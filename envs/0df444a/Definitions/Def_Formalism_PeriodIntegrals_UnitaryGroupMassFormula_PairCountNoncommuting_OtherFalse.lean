-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PairCountNoncommuting_OtherFalse
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PairCountNoncommuting_OtherFalse
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:52.427796+00:00
-- url     : https://prove2.me/theorems/6081d6cb-83f1-4bd7-9681-0ecf850720dc
-- title:
--   Other False
-- statement:
--   Definitions and structural lemmas for Other False, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PairCountNoncommuting/OtherFalse.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace PairCountNCWork
open Formalism.MainNotions.Ext.CutB
variable {N : ℕ} (ε : Fin N → Bool)
def toNC (p : {a // ε a = true} × {b // ε b = false}) : cBNC ε :=
  if h : p.1.1 < p.2.1 then
    ⟨(p.1.1, p.2.1), h, by rw [p.1.2, p.2.2]; decide⟩
  else
    ⟨(p.2.1, p.1.1), lt_of_le_of_ne (not_lt.mp h) (fun e => by
        have e' : p.2.1 = p.1.1 := e
        have h1 := p.1.2; have h2 := p.2.2; rw [e', h1] at h2; exact absurd h2 (by decide)),
      by rw [p.1.2, p.2.2]; decide⟩
theorem other_true {x y : Fin N} (hne : ε x ≠ ε y) (hx : ¬ ε x = true) : ε y = true := by
  cases hy : ε y <;> cases hx' : ε x <;> simp_all
theorem other_false {x y : Fin N} (hne : ε x ≠ ε y) (hx : ε x = true) : ε y = false := by
  cases hy : ε y <;> cases hx' : ε x <;> simp_all
def ofNC (q : cBNC ε) : {a // ε a = true} × {b // ε b = false} :=
  if hx : ε q.1.1 = true then
    (⟨q.1.1, hx⟩, ⟨q.1.2, other_false ε q.2.2 hx⟩)
  else
    (⟨q.1.2, other_true ε q.2.2 hx⟩, ⟨q.1.1, by simpa using hx⟩)
def equivNC : ({a // ε a = true} × {b // ε b = false}) ≃ cBNC ε where
  toFun := toNC ε
  invFun := ofNC ε
  left_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    by_cases h : a < b
    · simp [toNC, ofNC, h, ha]
    · have hb' : ε b ≠ true := by simp [hb]
      simp [toNC, ofNC, h, hb']
  right_inv := by
    rintro ⟨⟨x, y⟩, hlt, hne⟩
    by_cases hx : ε x = true
    · simp [toNC, ofNC, hx, hlt]
    · have hnlt : ¬ y < x := not_lt.mpr hlt.le
      simp [toNC, ofNC, hx, hnlt]
end PairCountNCWork


