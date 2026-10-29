-- Prove2me | Definitions.Def_SensitivityVariableFrontier
-- name    : SensitivityVariableFrontier
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-29T00:16:51.623385+00:00
-- url     : https://prove2.me/theorems/7de0fc61-8f1d-46fa-878b-a30d584150d0
-- title:
--   Exact finite profile search with variable parameters and dominance pruning
-- statement:
--   Fix a valid graph and labeling datum, a state count $N$, and a depth $k$. Enumerate the finite recipe alphabet and retain only valid recipes. Starting from the normalized upper-triangular all-ones profile, expand each retained profile by every allowed letter. At each depth, discard a profile when another retained profile is componentwise no larger in both matrices.
--
--   The Boolean success test checks whether any retained profile of height $H$, clamped below by two, satisfies
--
--   $$H^{43}<K^{20k},$$
--
--   where $K$ is the datum's vertex count. All parameters come from the supplied datum. The definitions reuse generic finite-list pruning and enumeration from the earlier search module; they impose none of that module's fixed numerical parameters.
--
--   The search terminates for every fixed input and depth. Its correspondence with arbitrary admissible words is a separate theorem. No success, global search bound, or practical runtime bound is asserted.
-- source:
--   Original exact checked-search reduction of SensitivityVariableWord.exists_215_word, https://prove2.me/theorems/b44a1e84-fdd6-4a5c-a770-91fc1133a055. Source definitions: SensitivityVariableWord.GraphData, step, run, Admissible, Crosses215, https://prove2.me/definitions/1a0f2c01-d616-4449-b679-77a45b8e1182. The variable alphabet and pruning proof generalize the fixed-parameter theorem SensitivityWordFrontier.search_correct, https://prove2.me/theorems/39c67854-b4b0-4292-b640-97e0bef4941e. RawData.Valid reproduces every GraphData field as a finite predicate with Boolean adjacency. Underlying recurrence attribution remains yousofy with Codex, OpenAI/math, Robin Kothari with Codex, and earlier community foundations, via accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2. No source is claimed to supply a crossing input or prove the remaining 2.15 existence claim.

import Definitions.Def_SensitivityVariableFinite
import Definitions.Def_SensitivityWordFrontier

/-!
Finite exact search at arbitrary certified graph parameters.
The imported fixed-parameter module supplies only the generic finite-list
dominance-pruning and finite-function enumeration definitions.
-/

set_option autoImplicit false

namespace SensitivityVariableFrontier
open SensitivityProfileCycle SensitivityProfileSearch SensitivityVariableWord
open SensitivityVariableFinite

abbrev Below {n : ℕ} := @SensitivityWordFrontier.Below n
abbrev maps := SensitivityWordFrontier.maps

def allLetters (q n : ℕ) : List (Letter q n) :=
  (maps n n).flatMap fun t =>
    (maps n n).flatMap fun g =>
      (maps n 3).flatMap fun a =>
        (maps n q).map fun v => Letter.mk t g a v

def alphabet (q n : ℕ) : List (Letter q n) :=
  (allLetters q n).filter (fun C => C.recipe.Valid)

def expand {n : ℕ} (G : GraphData) (s : List (Profile n)) : List (Profile n) :=
  s.flatMap fun P => (alphabet G.toleranceCount n).map fun C =>
    SensitivityVariableWord.step G C.recipe P

def frontier (G : GraphData) (n : ℕ) : ℕ → List (Profile n)
  | 0 => [SensitivityProfileSearch.normalize (unitProfile n)]
  | k+1 => FiniteDominance.prune Below (expand G (frontier G n k))

def succeeds (G : GraphData) (n k : ℕ) : Bool :=
  (frontier G n k).any fun P => decide (height P ^ 43 < G.vertices ^ (20*k))

end SensitivityVariableFrontier


