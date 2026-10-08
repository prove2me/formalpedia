-- Prove2me | Definitions.Def_OnlineSetCover_LowerBound_Game
-- name    : OnlineSetCover_LowerBound_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:46:26.077992+00:00
-- url     : https://prove2.me/theorems/78353c27-95f8-4cfb-818d-b47fd9222595
-- title:
--   The unweighted online set cover game: deterministic online algorithms, chosen sets, cost, validity and offline covers (§1)
-- statement:
--   This definition fixes the model of the **unweighted online set cover problem** of Alon, Awerbuch, Azar, Buchbinder and Naor (§1).
--
--   A ground set $X$ and a family $\mathcal F$ of subsets of $X$ are known in advance. An adversary presents elements $x_1, x_2, \dots$ of $X$ one at a time. A **deterministic online algorithm** $A$ is a rule that, when $x_t$ arrives, looks at the earlier arrivals $h = (x_1,\dots,x_{t-1})$ and at $x_t$, and returns a finite family $A(h, x_t)$ of sets that it adds to its collection. It may add any number of sets at a step, and sets once chosen are never removed. After the arrival sequence $\sigma = (x_1,\dots,x_T)$ the chosen collection is
--
--   $$\mathcal C_A(\sigma) = \bigcup_{t=1}^{T} A\big((x_1,\dots,x_{t-1}),\, x_t\big),$$
--
--   and, since every set has unit cost, the **cost** of $A$ on $\sigma$ is the number $|\mathcal C_A(\sigma)|$ of distinct sets chosen.
--
--   The algorithm is **valid for $\mathcal F$** when (1) every set it adds is a member of $\mathcal F$, and (2) after any arrival $x$ (whatever the earlier arrivals), if $x$ lies in some member of $\mathcal F$ then $x$ lies in some set of the collection chosen so far.
--
--   A subfamily $C \subseteq \mathcal F$ is an **offline cover** of $\sigma$ when every arrived element lies in a member of $C$; the offline optimum $\mathrm{OPT}(\sigma)$ is the least size of such a $C$.
--
--   These objects state every result of §4: a lower bound $\rho$ on the competitive ratio is exhibited by an arrival sequence $\sigma$ with $\mathrm{OPT}(\sigma) \ge 1$ and $|\mathcal C_A(\sigma)| \ge \rho\cdot \mathrm{OPT}(\sigma)$.
--
--   **Formalization Note** Arrival sequences are Lean lists in arrival order (oldest first). The algorithm is a function `List X → X → Finset (Finset X)`; determinism is built in, because its output depends on the arrivals only. Sets are identified with their elements (`Finset X`), so $\mathcal F$ is a family of distinct subsets and $|\mathcal F|$ is the paper's $m$. Validity asks for coverage only of elements that some member of $\mathcal F$ contains. The offline optimum is not given as a number: statements quantify over offline covers, or exhibit a single covering set.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), pp. 361–362, Section 1 (the online game and the competitive ratio); p. 368, Section 4 (unweighted problem)

import Mathlib

namespace OnlineSetCover.LowerBound

/-- A deterministic online algorithm for the unweighted online set cover problem on a ground
set `X` (Alon et al. 2009, §1, pp. 361–362). When an element `x` arrives, the algorithm sees the
list `h` of the elements that arrived before it (in arrival order, oldest first) and the new
element `x`, and returns the finite family `A h x` of sets it adds to its collection at this
step (any number of sets, possibly none). The instance itself (the ground set and the family)
is fixed in advance and known to the algorithm. Being deterministic, its choices are a function
of the arrivals alone. -/
abbrev OnlineAlg (X : Type*) := List X → X → Finset (Finset X)

variable {X : Type*} [DecidableEq X]

/-- `chosenFrom A h σ`: the sets added by `A` while the elements of `σ` arrive one by one (in
order), after the elements of `h` have already arrived. -/
def chosenFrom (A : OnlineAlg X) : List X → List X → Finset (Finset X)
  | _, [] => ∅
  | h, x :: rest => A h x ∪ chosenFrom A (h ++ [x]) rest

/-- `chosen A σ`: the collection `𝒞` of sets chosen by `A` (sets are never removed) after the
arrival sequence `σ` (oldest first). -/
def chosen (A : OnlineAlg X) (σ : List X) : Finset (Finset X) :=
  chosenFrom A [] σ

/-- The cost of `A` on the arrival sequence `σ` in the unweighted problem: the number of
distinct sets it has chosen. -/
def cost (A : OnlineAlg X) (σ : List X) : ℕ :=
  (chosen A σ).card

/-- `A` is a valid online algorithm for the family `𝓕`: it only ever adds members of `𝓕`, and
after each arrival `x` (whatever the earlier arrivals `h`), if `x` lies in some member of `𝓕`
then `x` lies in some set chosen so far. -/
def IsValid (𝓕 : Finset (Finset X)) (A : OnlineAlg X) : Prop :=
  ∀ (h : List X) (x : X),
    A h x ⊆ 𝓕 ∧ ((∃ S ∈ 𝓕, x ∈ S) → ∃ S ∈ chosen A (h ++ [x]), x ∈ S)

/-- `C` is an offline cover of the arrivals `σ` by the family `𝓕`: `C` is a subfamily of `𝓕`
and every arrived element lies in some member of `C`. The offline optimum `OPT(σ)` is the least
cardinality of such a `C`. -/
def IsCoverOf (𝓕 C : Finset (Finset X)) (σ : List X) : Prop :=
  C ⊆ 𝓕 ∧ ∀ x ∈ σ, ∃ S ∈ C, x ∈ S

end OnlineSetCover.LowerBound


