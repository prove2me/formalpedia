-- Prove2me | Definitions.Def_SensitivityWordFrontier
-- name    : SensitivityWordFrontier
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-22T18:46:48.878924+00:00
-- url     : https://prove2.me/theorems/f87046e7-b356-4b06-8916-e0d7d5881f42
-- title:
--   Exact profile search with dominance pruning
-- statement:
--   For a fixed state count $N$, enumerate the valid letters of the finite alphabet.
--   The initial frontier consists only of the normalized all-ones profile. At each
--   depth, apply every valid letter to every retained profile, then prune by the
--   componentwise order on both profile matrices.
--
--   An insertion is skipped if an existing profile is no larger in every entry.
--   Otherwise insert the new profile and remove existing profiles it dominates.
--   All comparisons take place at the same depth. Write $F_N(k)$ for the resulting
--   finite list after $k$ stages. The Boolean test is
--
--   $$\mathrm{succeeds}(N,k)\iff
--     \exists P\in F_N(k),\quad h(P)^{43}<14055^{20k}.$$
--
--   The definitions use finite enumeration and exact natural-number arithmetic.
--   They make no claim that a successful depth or state count exists and supply
--   no bound on runtime, depth, or state count. Correctness and completeness are
--   proved separately; in particular, dominance pruning never splices entries
--   from different reachable profiles.
-- source:
--   Original complete finite-search reduction of SensitivityProfileWord.exists_215_word, https://prove2.me/theorems/76888ed0-dff9-4b8d-b69f-5a603abeb564. Exact source definitions: SensitivityProfileWord.run, Admissible, Crosses215; SensitivityProfileSearch.step and envelope; SensitivityProfileCycle.Recipe.Valid. The recurrence originates in accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a (yousofy with Codex), retaining OpenAI/math, Robin Kothari with Codex, and community attribution. The finite alphabet and dominance-pruning algorithm are new. No crossing witness or search-success bound is supplied or claimed to be known.

import Definitions.Def_SensitivityWordFinite

/-!
Exact finite profile search with componentwise dominance pruning.
No search success or numerical growth bound is assumed by these definitions.
-/

set_option autoImplicit false

namespace FiniteDominance
variable {α : Type} (R : α → α → Prop) [DecidableRel R]

def insert (x : α) (s : List α) : List α :=
  if ∃ y ∈ s, R y x then s else x :: s.filter (fun y => ¬ R x y)

def prune : List α → List α
  | [] => []
  | x :: s => insert R x (prune s)

end FiniteDominance

namespace SensitivityWordFrontier
open SensitivityProfileCycle SensitivityProfileSearch SensitivityProfileWord
open SensitivityWordFinite

def Below {n : ℕ} (P Q : Profile n) : Prop :=
  ∀ i j, P.zero i j ≤ Q.zero i j ∧ P.one i j ≤ Q.one i j

instance {n : ℕ} : DecidableRel (@Below n) := fun P Q => by
  unfold Below
  infer_instance

def maps (n m : ℕ) : List (Fin n → Fin m) :=
  (List.pi (List.finRange n) (fun _ => List.finRange m)).map
    (fun f i => f i (List.mem_finRange i))

def allLetters (n : ℕ) : List (Letter n) :=
  (maps n n).flatMap fun t =>
    (maps n n).flatMap fun g =>
      (maps n 3).flatMap fun a =>
        (maps n 6).map fun q => Letter.mk t g a q

def alphabet (n : ℕ) : List (Letter n) :=
  (allLetters n).filter (fun C => C.recipe.Valid)

def expand {n : ℕ} (s : List (Profile n)) : List (Profile n) :=
  s.flatMap fun P => (alphabet n).map fun C => step C.recipe P

def frontier (n : ℕ) : ℕ → List (Profile n)
  | 0 => [normalize (unitProfile n)]
  | k+1 => FiniteDominance.prune Below (expand (frontier n k))

def succeeds (n k : ℕ) : Bool :=
  (frontier n k).any fun P => decide (height P ^ 43 < 14055 ^ (20*k))

end SensitivityWordFrontier


