-- Prove2me | Definitions.Def_SensitivityVariableFinite
-- name    : SensitivityVariableFinite
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-29T00:13:59.702997+00:00
-- url     : https://prove2.me/theorems/8b4c1829-94fb-479b-966b-55a5751fa5b7
-- title:
--   Finite recipe alphabets with variable tolerance range
-- statement:
--   For a state count $N$ and tolerance count $Q$, a letter consists of target and gate maps into the $N$ states, an auxiliary map into three values, and a tolerance map into the $Q$ values from zero through $Q-1$. Its decoded recipe reads these tolerance values as natural numbers. The ambient alphabet has cardinality
--
--   $$N^{2N}(3Q)^N.$$
--
--   Recipe validity is the original ordering predicate. Completeness for admissible transfers is proved separately: tolerances on auxiliary states are unused and may be set to zero, while ordinary-state tolerances already satisfy the required finite bound. No success or growth assertion is part of this definition.
-- source:
--   Original exact checked-search reduction of SensitivityVariableWord.exists_215_word, https://prove2.me/theorems/b44a1e84-fdd6-4a5c-a770-91fc1133a055. Source definitions: SensitivityVariableWord.GraphData, step, run, Admissible, Crosses215, https://prove2.me/definitions/1a0f2c01-d616-4449-b679-77a45b8e1182. The variable alphabet and pruning proof generalize the fixed-parameter theorem SensitivityWordFrontier.search_correct, https://prove2.me/theorems/39c67854-b4b0-4292-b640-97e0bef4941e. RawData.Valid reproduces every GraphData field as a finite predicate with Boolean adjacency. Underlying recurrence attribution remains yousofy with Codex, OpenAI/math, Robin Kothari with Codex, and earlier community foundations, via accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2. No source is claimed to supply a crossing input or prove the remaining 2.15 existence claim.

import Definitions.Def_SensitivityVariableWord

/-! Finite recipe alphabets with a variable tolerance count. -/

set_option autoImplicit false

namespace SensitivityVariableFinite
open SensitivityProfileCycle

structure Letter (q n : ℕ) where
  target : Fin n → Fin n
  gate : Fin n → Fin n
  aux : Fin n → Fin 3
  tol : Fin n → Fin q
  deriving Fintype, DecidableEq

def Letter.recipe {q n : ℕ} (C : Letter q n) : Recipe n :=
  ⟨C.target, C.gate, C.aux, fun i => (C.tol i).val⟩

instance {q n : ℕ} (C : Letter q n) : Decidable C.recipe.Valid := by
  unfold Recipe.Valid Monotone
  infer_instance

end SensitivityVariableFinite


