-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:44:38.98714+00:00
-- url     : https://prove2.me/theorems/f04e3a8f-b476-4055-816e-d3b62da40283
-- title:
--   An explicit $(|H|+2)$-state automaton for nonempty relation products, and its productive configurations
-- statement:
--   Let $H$ be a set, and take as input alphabet the set of all binary relations $R\subseteq H\times H$. For a word $w=R_1R_2\cdots R_n$ over this alphabet, its relation product $\Pi(w)=R_1R_2\cdots R_n$ is the composition in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$, with $\Pi$ of the empty word equal to $\mathrm{Id}_H$; thus $(x,y)\in\Pi(w)$ iff there are $x=x_0,x_1,\dots,x_n=y$ with $(x_{i-1},x_i)\in R_i$ for all $i$. The source language is the set of words $w$ with $\Pi(w)\neq\emptyset$.
--
--   A two-way nondeterministic automaton reads the tape $\triangleright R_1\cdots R_n\triangleleft$ (positions $0,\dots,n+1$); each transition depends on the current state and scanned symbol and chooses a next state and a head move (left, stay or right); it accepts if some finite run from the initial state at position $0$ reaches an accepting state.
--
--   1. **Source automaton.** $\mathcal S_H$ has state set $\{\mathrm{start},\mathrm{acc}\}\sqcup H$, initial state $\mathrm{start}$, accepting set $\{\mathrm{acc}\}$, and exactly the transitions
--   $$\mathrm{start}\xrightarrow{\ \triangleright\ }(h,\mathrm{right})\ \ (h\in H),\qquad p\xrightarrow{\ R\ }(q,\mathrm{right})\ \ \text{whenever }(p,q)\in R,\qquad p\xrightarrow{\ \triangleleft\ }(\mathrm{acc},\mathrm{stay})\ \ (p\in H).$$
--   There are no other transitions: $\mathrm{start}$ does nothing on letters or on $\triangleleft$, a state $p\in H$ does nothing on $\triangleright$, $\mathrm{acc}$ has no transitions at all, and the machine never moves left.
--   2. **Productive configurations.** For a word $w$ of length $n$, the set $\mathcal P(w)$ of configurations (state, position $i\in\{0,\dots,n+1\}$) is defined by: $(\mathrm{start},i)\in\mathcal P(w)$ iff $i=0$ and $\Pi(w)\neq\emptyset$; $(\mathrm{acc},i)\in\mathcal P(w)$ for every $i$; and, for $p\in H$, $(p,i)\in\mathcal P(w)$ iff $i\ge 1$ and $(p,q)\in\Pi(R_iR_{i+1}\cdots R_n)$ for some $q\in H$, where for $i=n+1$ the suffix is empty and its product is $\mathrm{Id}_H$.
--
--   The automaton $\mathcal S_H$ guesses a starting point, follows a path through the letters from left to right, and accepts at the right endmarker; its language is the source language. Productive configurations are those from which the remaining input still contains a witness path; they are closed under predecessors along steps, which shows that every accepted word has a nonempty relation product. For $|H|=n-2$ the automaton has exactly $n$ states and serves as the $n$-state witness in the main lower-bound theorem.
--
--   **Formalization Note** `sourceAutomaton H : TwoNFA (SetRel H H) (Option (Option H))` uses `none` for start, `some none` for acc and `some (some h)` for the state $h$; in its transitions the move `2 : Fin 3` is right and `1` is stay, and the endmarkers are `Sum.inl 0` and `Sum.inl 1`. `sourceProductive w` is a set of configurations in `Option (Option H) × Fin (w.length + 2)`; the suffix $R_i\cdots R_n$ is `w.drop (i - 1)`, and $\Pi$ is `relationProduct`, i.e. `w.foldr SetRel.comp SetRel.id`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Source.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Source.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- The explicit source machine: `none` starts, `some none` accepts, and
    `some (some h)` is the state labelled by `h`. -/
def sourceAutomaton (H : Type*) : TwoNFA (SetRel H H) (Option (Option H)) where
  initial := none
  accepting := {some none}
  transition state symbol := match state, symbol with
    | none, .inl marker =>
      if marker = 0 then {target | ∃ h, target = (some (some h), 2)} else ∅
    | some (some p), .inr R =>
      {target | ∃ q, (p, q) ∈ R ∧ target = (some (some q), 2)}
    | some (some _), .inl marker =>
      if marker = 1 then {(some none, 1)} else ∅
    | _, _ => ∅

/-- Configurations from which the explicit source machine has a suffix witness. -/
def sourceProductive {H : Type*} (w : List (SetRel H H)) :
    Set (Option (Option H) × Fin (w.length + 2)) :=
  {c | match c.1 with
    | none => c.2.val = 0 ∧ (relationProduct w).Nonempty
    | some none => True
    | some (some p) => 1 ≤ c.2.val ∧ ∃ q, (p, q) ∈ relationProduct (w.drop (c.2.val - 1))}

end TwoWayComplementation

end OAI


