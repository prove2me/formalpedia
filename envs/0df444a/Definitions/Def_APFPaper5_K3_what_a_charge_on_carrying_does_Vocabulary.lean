-- Prove2me | Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
-- name    : APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-17T03:35:41.019924+00:00
-- url     : https://prove2.me/theorems/0c2e0617-fb3b-4e29-8ace-15a11ec428db
-- title:
--   Model vocabulary — Path charges under state functions and changes of presentation
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   A supplied difference-of-state-function charge telescopes and vanishes on loops. Every loop step vanishes only with the explicit nondecreasing-state-function hypothesis. Endpoint changes of presentation preserve closed totals and relative path charges; distinct-endpoint open totals can be gauged to zero. Squared-sum interference is a supplied rule, not a derived physical gauge law.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does; Pullbacks v46, SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9. Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does; pullbacks v46; SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper5.K3.Carrying

universe u

section Paths
variable {X : Type u}

/-- The total charged along the first `n` steps of the path `p`, at charge `A` per step. -/
def total (A : X → X → ℝ) (p : ℕ → X) : ℕ → ℝ
  | 0 => 0
  | n + 1 => total A p n + A (p n) (p (n + 1))





/-! ### A. Booked charge: the ledger is a function of the state -/









/-! ### C. Re-presenting how alternatives are compared from place to place -/

/-- A re-presentation `g` changes the charge of a step by a term at each of its two ends. -/
def represent (g : X → ℝ) (A : X → X → ℝ) : X → X → ℝ := fun x y => A x y + g y - g x









end Paths

/-! ### B. Held charge, as a turn: what is counted where two arms meet -/

/-- Turn the pair `u` by the turn with numbers `c` and `s`. -/
def turnBy (c s : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := (c * u.1 - s * u.2, s * u.1 + c * u.2)

/-- What is counted where two arms meet: the squared length of the sum. Supplied. -/
def meet (u v : ℝ × ℝ) : ℝ := (u.1 + v.1) * (u.1 + v.1) + (u.2 + v.2) * (u.2 + v.2)











end APFPaper5.K3.Carrying


