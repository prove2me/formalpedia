-- Prove2me | Definitions.Def_HousingImprove_Step
-- name    : HousingImprove_Step
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:40.720521+00:00
-- url     : https://prove2.me/theorems/dab0eb1e-65ad-4a62-ba5c-866e2f5988ef
-- title:
--   Algorithm HM-Improve as a transition relation
-- statement:
--   Fix an admissible set $Q$ (`IsQChoice`; see `tildeMarket`) and the market $\widetilde H$ built from it. A **state** of algorithm HM-Improve is a pair $(Y,R)$: a sub-allocation $Y$ of $\widetilde H-R$ and a set $R\subseteq\widetilde N$ of **irrelevant** agents. Write $U$ and $V$ for the source and sink sets of $Y$ in $\widetilde H-R$.
--
--   **Initialization.** $Y=X\setminus\{(q,X(q)):q\in Q\}\cup\{(q,\tilde q):q\in Q\}$ and $R=\emptyset$.
--
--   **Iteration.** If $U=V$ the iteration stops. Otherwise:
--
--   1. (Step 2(a)) if a $Y$-augmenting arc $(s,u)$ of $\widetilde H-R$ enters a source $u\in U$ and $s\notin V$, with $u'=Y(s)$, replace the arc $(s,u')$ by $(s,u)$;
--   2. (Step 2(b)) if such an arc has $s\in V$, add $(s,u)$ to $Y$;
--   3. (Step 3) if no $Y$-augmenting arc enters any source, pick any $u\in U\setminus V$ with $u'=Y(u)$, add $u$ to $R$ and delete $(u,u')$.
--
--   **Output.** At the end, with $X_R$ an allocation of the submarket $H'_{R\cap N}$, the output $X'$ gives each $a\in R\cap N$ the house $X_R(a)$ and each $a\in N\setminus R$ the house $Y(a)$, read as $p$ when $Y(a)=\tilde a$.
--
--   The transition relation has one transition for each choice the page leaves free, so every run of the algorithm is a chain of transitions from the initialization; the milestones quantify over all of them.
--
--   **Formalization Note** `HMStep` has the constructors `step2a`, `step2b`, `step3`, each with the page's preconditions (including, for Step 3, that no $Y$-augmenting arc enters any source). `HMReachable` is reachability from `hmInit`; `IsTerminal` is $U=V$; `IsOutput` is the output rule of p.13, whose two printed cases ($X_R\cup Y$, or $X_R\cup Y\setminus\{(q,\tilde q),(\tilde q,p)\}\cup\{(q,p)\}$) it merges.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §4.1, pp.12–13 (Initialization, Iteration Steps 1–3, Output) and Algorithm 1, p.14

import Mathlib
import Definitions.Def_HousingImprove_IsSubAllocation
import Definitions.Def_HousingImprove_tildeMarket

namespace HousingImprove

universe u

variable {N : Type u}

/-- A state of algorithm **HM-Improve** (Schlotter, Biró, Fleiner, arXiv:2110.06875v3, §4.1,
pp.12–13), run with the set `Q` (`IsQChoice`): the current sub-allocation `Y` of `H̃ − R` and the set
`R` of irrelevant agents. -/
structure HMState (Q : Set N) where
  /-- The sub-allocation: `Y a = some b` is the arc `(a, b)`. -/
  Y : Tilde Q → Option (Tilde Q)
  /-- The irrelevant agents. -/
  R : Set (Tilde Q)

variable {Q : Set N}

/-- The agents of `Ñ \ R`, which carry the current sub-allocation and its envy graph `G̃_{Y≺}`. -/
def HMState.alive (s : HMState Q) : Set (Tilde Q) := s.Rᶜ

/-- The source set `U` of the current sub-allocation, in `H̃ − R`. -/
def HMState.U (s : HMState Q) : Set (Tilde Q) := subSources s.alive s.Y

/-- The sink set `V` of the current sub-allocation, in `H̃ − R`. -/
def HMState.V (s : HMState Q) : Set (Tilde Q) := subSinks s.alive s.Y

/-- `(a, b)` is an arc of the envy graph `G̃_{Y≺}` of the current state: a `Y`-augmenting arc of
`H̃ − R`, where `H̃ = tildeMarket H' p Q`. -/
def HMState.Aug (H' : Market N) (p : N) (s : HMState Q) (a b : Tilde Q) : Prop :=
  IsAugmenting (tildeMarket H' p Q) s.alive s.Y a b

/-- **Initialization** of HM-Improve (p.12): "Let `Y = X \ {(q, X(q)) : q ∈ Q} ∪ {(q, q̃) : q ∈ Q}`
in `G̃`. … we define a set `R` of irrelevant agents, initially empty." -/
noncomputable def hmInit (X : Equiv.Perm N) (Q : Set N) : HMState Q := by
  classical
  exact
    { Y := fun
        | .inl a => if h : a ∈ Q then some (.inr ⟨a, h⟩) else some (.inl (X a))
        | .inr _ => none
      R := ∅ }

open scoped Classical in
/-- One **iteration** of HM-Improve (p.12), with the page's preconditions. Writing `U`, `V` for the
source and sink sets of `Y` (Step 1: the iteration stops if `U = V`):

* Step 2(a): if some `Y`-augmenting arc `(s, u)` enters a source `u ∈ U` and `s ∉ V`, with
  `u' = Y(s)`, delete `(s, u')` and add `(s, u)`.
* Step 2(b): if some `Y`-augmenting arc `(s, u)` enters a source `u ∈ U` and `s ∈ V`, add `(s, u)`.
* Step 3: otherwise (no `Y`-augmenting arc enters any source), for any `u ∈ U \ V` with
  `u' = Y(u)`, add `u` to `R` and delete `(u, u')`.

**Formalization Note.** The relation has one transition for each choice the page leaves free, so
every run of the algorithm is a chain of `HMStep`s from `hmInit`. `Function.update` uses classical
decidable equality on `Ñ`. -/
inductive HMStep (H' : Market N) (p : N) (Q : Set N) :
    HMState Q → HMState Q → Prop
  | step2a (s : HMState Q) (a u u' : Tilde Q) :
      s.U ≠ s.V → u ∈ s.U → s.Aug H' p a u → a ∉ s.V → s.Y a = some u' →
      HMStep H' p Q s { s with Y := Function.update s.Y a (some u) }
  | step2b (s : HMState Q) (a u : Tilde Q) :
      s.U ≠ s.V → u ∈ s.U → s.Aug H' p a u → a ∈ s.V →
      HMStep H' p Q s { s with Y := Function.update s.Y a (some u) }
  | step3 (s : HMState Q) (u u' : Tilde Q) :
      s.U ≠ s.V → (∀ a v, v ∈ s.U → ¬ s.Aug H' p a v) → u ∈ s.U → u ∉ s.V → s.Y u = some u' →
      HMStep H' p Q s { Y := Function.update s.Y u none, R := insert u s.R }

/-- A state reached by some run of HM-Improve (with the set `Q`) from its initialization. -/
def HMReachable (H' : Market N) (X : Equiv.Perm N) (p : N) (Q : Set N) (s : HMState Q) : Prop :=
  Relation.ReflTransGen (HMStep H' p Q) (hmInit X Q) s

/-- Step 1 (p.12): the iteration stops when the source set equals the sink set. -/
def HMState.IsTerminal (s : HMState Q) : Prop := s.U = s.V

/-- The agents of `N` that are irrelevant in state `s`: the agent set `R ∩ N` of the submarket on
which TTC runs (p.13). -/
def HMState.RN (s : HMState Q) : Set N := {a | Sum.inl a ∈ s.R}

/-- **Output** of HM-Improve (p.13): `X'` agrees with the allocation `X_R` (computed on
`H'_{R∩N}`) on `R ∩ N`; an agent `a ∈ N \ R` obtains the house `Y(a)`, read as `p` when `Y(a)` is
`q̃` (which happens only for `a = q`).

**Formalization Note.** The page's two cases, `X_R ∪ Y` if `Q̃ \ R \ U = ∅` and
`X_R ∪ Y \ {(q, q̃), (q̃, p)} ∪ {(q, p)}` if `Q̃ \ R \ U = {q̃}`, are this one rule. -/
def HMState.IsOutput (p : N) (s : HMState Q) (XR : Equiv.Perm s.RN) (X' : N → N) : Prop :=
  (∀ a (h : a ∈ s.RN), X' a = (XR ⟨a, h⟩).1) ∧
  (∀ a b, a ∉ s.RN → s.Y (.inl a) = some b → X' a = tildeIota p b)

end HousingImprove


