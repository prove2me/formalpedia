-- Prove2me | Definitions.Def_Grunbaum2003_rayMachineStep
-- name    : Grunbaum2003_rayMachineStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:35:35.980057+00:00
-- url     : https://prove2.me/theorems/353096da-c402-4fc2-a229-a6c14114f23e
-- title:
--   One ray machine step
-- statement:
--   One transition of the exact real machine, charging only ray oracle calls.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.6, printed pp. 52b–52c / PDF pp. 74–75; exact-real ray-machine expression adapter; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

noncomputable def rayMachineStep {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (c : RayConfiguration) : Option RayConfiguration := by
  classical
  let cell := fun i => c.tape (c.head + i)
  let write := fun dst value next =>
    some { c with pc := next, tape := Function.update c.tape (c.head + dst) value }
  exact match program[c.pc]? with
  | none => none
  | some (.constant dst value next) => write dst (value : ℝ) next
  | some (.add dst a b next) => write dst (cell a + cell b) next
  | some (.sub dst a b next) => write dst (cell a - cell b) next
  | some (.mul dst a b next) => write dst (cell a * cell b) next
  | some (.div dst a b next) =>
      if cell b = 0 then none else write dst (cell a / cell b) next
  | some (.branch a negative equal positive) =>
      some { c with pc := (if cell a < 0 then negative else if cell a = 0 then equal else positive) }
  | some (.shift offset next) => some { c with pc := next, head := c.head + offset }
  | some (.query next) =>
      let v : Fin d → ℝ := fun i => cell (i.val : ℤ)
      if v = 0 then none else
        let answer := oracle v
        some { c with
          pc := next
          queries := c.queries + 1
          tape := fun j =>
            if h : 0 ≤ j - c.head ∧ j - c.head < (d : ℤ) then
              answer ⟨(j - c.head).toNat, by omega⟩
            else c.tape j }
  | some .halt => some c

end Grunbaum2003


