-- Prove2me | Definitions.Def_SensitivityWordFinite
-- name    : SensitivityWordFinite
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-22T18:45:36.553005+00:00
-- url     : https://prove2.me/theorems/30d14bd5-5241-47b3-a49b-8ddd33abaa3d
-- title:
--   A complete finite alphabet for sensitivity recipe search
-- statement:
--   For a fixed number $N$ of states, a letter consists of target and gate maps into
--   the state set, an auxiliary map into three values, and a tolerance map into six
--   values. Its decoded recipe is the original recipe with each tolerance read as a
--   natural number. Thus the ambient alphabet is finite, of cardinality
--
--   $$N^{2N}18^N.$$
--
--   Recipe validity remains exactly the original monotonicity predicate. No
--   admissibility or growth conclusion is built into the data type. The alphabet
--   can represent every admissible recipe's transfer map: tolerance values on the
--   first three states are unused and may be replaced by zero; on all other states
--   the admissibility condition already bounds the tolerance by five. That
--   completeness assertion is proved separately in the search-correctness theorem.
-- source:
--   Original complete finite-search reduction of SensitivityProfileWord.exists_215_word, https://prove2.me/theorems/76888ed0-dff9-4b8d-b69f-5a603abeb564. Exact source definitions: SensitivityProfileWord.run, Admissible, Crosses215; SensitivityProfileSearch.step and envelope; SensitivityProfileCycle.Recipe.Valid. The recurrence originates in accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a (yousofy with Codex), retaining OpenAI/math, Robin Kothari with Codex, and community attribution. The finite alphabet and dominance-pruning algorithm are new. No crossing witness or search-success bound is supplied or claimed to be known.

import Definitions.Def_SensitivityProfileWord

/-! A finite alphabet for exact searches over admissible recipe words. -/

set_option autoImplicit false

namespace SensitivityWordFinite
open SensitivityProfileCycle SensitivityProfileSearch SensitivityProfileWord

structure Letter (n : ℕ) where
  target : Fin n → Fin n
  gate : Fin n → Fin n
  aux : Fin n → Fin 3
  tol : Fin n → Fin 6
  deriving Fintype, DecidableEq

def Letter.recipe {n : ℕ} (C : Letter n) : Recipe n :=
  ⟨C.target, C.gate, C.aux, fun i => (C.tol i).val⟩

instance {n : ℕ} (C : Letter n) : Decidable C.recipe.Valid := by
  unfold Recipe.Valid Monotone
  infer_instance

end SensitivityWordFinite


