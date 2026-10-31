-- Prove2me | Definitions.Def_PickAnObject_Model
-- name    : PickAnObject_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:01.091418+00:00
-- url     : https://prove2.me/theorems/0afce8d4-3c7d-4e88-8901-a33864a3006e
-- title:
--   Pick-an-object mechanisms: preferences, rules, monotonic discoverability, menu functions, the PAO run, sequentialization and perfect ex-post equilibrium
-- statement:
--   This module defines the model of Bó and Hakimov's *Pick-an-Object Mechanisms* (§3, §3.1, §4 and App. A).
--
--   **Agents, objects, preferences.** $A$ is a finite set of agents and $O=\{o_1,\dots,o_m\}\cup\{\varnothing\}$ a finite set of object types containing the null object $\varnothing$. Each agent has a strict preference $P_a$ over all of $O$ (objects ranked below $\varnothing$ are unacceptable); $o\,R_a\,o'$ means $o\,P_a\,o'$ or $o=o'$. A profile is $P=(P_a)_{a\in A}$, an allocation is any map $\mu:A\to O$ (there is no feasibility constraint), and a rule $\varphi$ maps profiles to allocations.
--
--   1. **Individual rationality:** $\varphi_a(P)\,R_a\,\varnothing$ for all $P$ and $a$.
--   2. **Strategy-proofness:** $\varphi_a(P_a,P_{-a})\,R_a\,\varphi_a(P'_a,P_{-a})$ for all $a$, $P$, $P'_a$.
--   3. **Lower contour set** $\mathcal L(P,\mu)$: the profiles $P'$ such that, for every agent $a$, $P'_a$ has the same objects strictly above $\mu(a)$ as $P_a$, in the same order; formally, for all $o,o'\in O$,
--   $$\bigl(o\,P_a\,o' \wedge o'\,R_a\,\mu(a)\bigr)\iff\bigl(o\,P'_a\,o' \wedge o'\,R'_a\,\mu(a)\bigr).$$
--   4. **Monotonic discoverability** (Definition 3): for every allocation $\mu$ and profile $P$, either $\varphi(P)=\mu$ or some agent $a^*$ has $\mu(a^*)\neq\varphi_{a^*}(P')$ for every $P'\in\mathcal L(P,\mu)$.
--
--   **Histories and menus.** A choice history is a finite sequence $((\Omega_1,\omega_1),\dots,(\Omega_k,\omega_k))$ of menus $\Omega_j\subseteq O$ and choices; $\vec h=\omega_k$ is its last choice. A collective history $h^A$ has one choice history per agent; $h^{A-\varnothing}$ is the one with all histories empty. A preference is consistent with a choice history if every choice is weakly preferred to everything in its menu.
--
--   5. **Menu function:** $S$ assigns every agent a menu at every collective history, with non-empty initial menus $S_i(h^{A-\varnothing})$, and, whenever agent $i$ has faced at least one menu, $S_i(h^A)\subseteq\Omega_{k_i}\setminus\{\omega_{k_i}\}$ (her last menu without her last choice).
--   6. **The pick-an-object run:** at a collective history $h$, if every menu $S_i(h)$ is empty the procedure stops and each agent receives her last choice; otherwise every agent with a non-empty menu chooses from it and the pair (menu, choice) is appended to her history. A strategy chooses an object from the agent's own history and current menu, and must pick from every non-empty menu. The outcome $\mathcal O|_{h}(\sigma)$ is the allocation produced by the run started at $h$.
--   7. **Straightforward strategy** (Definition 1): choose the most-preferred element of every menu.
--   8. **Sequentialization** (Definition 2): $S$ sequentializes $\varphi$ if $S$ is a menu function and, for every $P$, the run from $h^{A-\varnothing}$ under straightforward strategies produces $\varphi(P)$.
--   9. **Collective histories of $S$:** the histories reachable from $h^{A-\varnothing}$ when agents make arbitrary choices from the menus offered (including $h^{A-\varnothing}$).
--   10. **Perfect ex-post equilibrium** (Definition 4): a type-strategy profile $(\Sigma_a)$ is one if, for every agent $a$, every collective history $h^A$ of $S$, every strategy $\sigma'_a$ and every profile $P$,
--   $$\mathcal O_a|_{h^A}\bigl(\Sigma_a(P_a),(\Sigma_{a'}(P_{a'}))_{a'\neq a}\bigr)\;R_a\;\mathcal O_a|_{h^A}\bigl(\sigma'_a,(\Sigma_{a'}(P_{a'}))_{a'\neq a}\bigr).$$
--   11. **Pick-an-object implementability in perfect ex-post equilibrium:** some $S$ sequentializes $\varphi$ and straightforward strategies are a perfect ex-post equilibrium of $S$.
--   12. **Recursive dominance** (Definition 7): for every agent $a$, profile $P$, tuple $\gamma$ of distinct objects (with set of entries $I$) and preference $P^*$ that ranks $\gamma$ first in its order, $\varphi_a(\gamma\oplus P_a|_{O\setminus I},P_{-a})\,R_a\,\varphi_a(P^*,P_{-a})$, where $\gamma\oplus P_a|_{O\setminus I}$ ranks $\gamma$ first and then the remaining objects as $P_a$ does.
--
--   These are the objects of Theorems 1 and 2, Corollary 1 and Lemma 1.
--
--   **Formalization Note** $O$ is `Option Obj` for a finite type `Obj` (`none` $=\varnothing$). A strict preference is its ranking $O\simeq\{0,\dots,|O|-1\}$ (rank $0$ = best); every strict linear order arises exactly once. The printed display of $\mathcal L(P,\mu)$ on p.12 constrains only pairs of objects strictly above $\mu(a)$, which makes Theorem 1 false (one agent, $O=\{x,y,\varnothing\}$, $\varphi(P)=x$ iff $x\,P\,\varnothing$: it is sequentialized by the menu $\{x,\varnothing\}$, but $P=(x,\varnothing,y)$, $\mu=\varnothing$, $P'=(y,\varnothing,x)$ violates the printed Definition 3); the definition above is the reading stated in the sentence under the display. The run is iterated $|A|\cdot|O|+1$ times: valid strategies make every agent's non-empty menus strictly shrink, so the procedure has stopped by then, and a stopped history is left unchanged. Strategies are functions of the agent's own history and menu that pick from every non-empty menu (the paper's condition that a choice extends a feasible history). The menu-shrinking constraint is not imposed at histories other than $h^{A-\varnothing}$ in which an agent has faced no menu; the mechanism never produces such histories. The last choice of an empty history is set to $\varnothing$; it is never an outcome.
-- source:
--   Bó–Hakimov, Pick-an-Object Mechanisms, arXiv:2012.01025v4, §3 pp.9–11 (preferences, IR, SP, histories, consistency, menu functions, PAO mechanism, Definitions 1–2, collective histories of S), §3.1 pp.12–13 (lower contour set, Definition 3), §4 pp.18–19 (strategies, outcomes, Definition 4, implementability), App. A pp.43–44 (𝒫|γ, γ ⊕ P|O∖I, Definition 7)

import Mathlib

namespace PickAnObject

/-! # Pick-an-object mechanisms: the model

Bó–Hakimov, *Pick-an-Object Mechanisms*, arXiv:2012.01025v4, §3 (pp.9–11), §3.1 (pp.12–13),
§4 (pp.18–19) and App. A (pp.43–44).

This module bundles the tightly coupled definitions of the model: preferences, rules, individual
rationality, strategy-proofness, the (corrected) lower contour set, monotonic discoverability,
choice histories, consistency, menu functions, the pick-an-object run, strategies, the
straightforward strategy, sequentialization, reachable collective histories, perfect ex-post
equilibrium, pick-an-object implementability and recursive dominance.

**Formalization Note (object types).** The paper's set of object types
`O = {o₁, …, o_m} ∪ {∅}` (p.9) is `Option Obj` for a finite type `Obj`; `none` is the null
object `∅`. -/

/-- **Strict preferences over `O`**, Bó–Hakimov, arXiv:2012.01025v4, §3, p.9: "Each agent `a` has
strict preferences `P_a` over the set `O`" (`O` includes the null object `∅`); `𝒫` is the set of
all strict preferences over `O`.

**Formalization Note.** A strict preference is encoded by its ranking `Q : O ≃ Fin |O|`
(`Q o = 0` is the most preferred object type); `o P o'` iff `Q o < Q o'` (`Prefers`). Every strict
linear order on the finite set `O` arises from exactly one such ranking. The null object is
ranked like every other object type, so objects may be ranked below `∅` (unacceptable). -/
abbrev Pref (Obj : Type*) [Fintype Obj] : Type _ := Option Obj ≃ Fin (Fintype.card (Option Obj))

section Preferences

variable {Obj : Type*} [Fintype Obj]

/-- `Prefers Q o o'` is `o P o'`: the preference `Q` ranks `o` strictly above `o'`
(arXiv:2012.01025v4, §3, p.9). -/
def Prefers (Q : Pref Obj) (o o' : Option Obj) : Prop := Q o < Q o'

/-- `WeaklyPrefers Q o o'` is `o R o'`, the induced weak preference of arXiv:2012.01025v4, §3,
p.9: "`o R_a o'` if `o P_a o'` or `o = o'`". -/
def WeaklyPrefers (Q : Pref Obj) (o o' : Option Obj) : Prop := Prefers Q o o' ∨ o = o'

end Preferences

/-- A **preference profile** `P = (P_a)_{a ∈ A}` (arXiv:2012.01025v4, §3, p.9). -/
abbrev Profile (A Obj : Type*) [Fintype Obj] : Type _ := A → Pref Obj

/-- An **allocation** `µ : A → O` (arXiv:2012.01025v4, §3, p.9).

**Formalization Note.** There is no feasibility constraint: footnote 15 (p.9) says feasibility
is encoded in the rule, so two agents may receive the same object type. -/
abbrev Allocation (A Obj : Type*) : Type _ := A → Option Obj

/-- A **rule** `φ : 𝒫ⁿ → ℳ` maps preference profiles to allocations (arXiv:2012.01025v4, §3,
p.9). -/
abbrev Rule (A Obj : Type*) [Fintype Obj] : Type _ := Profile A Obj → Allocation A Obj

section Rules

variable {A Obj : Type*} [Fintype Obj]

/-- **Individual rationality**, arXiv:2012.01025v4, §3, p.9: "A rule `φ` is individually rational
if, for any `P ∈ 𝒫` and `a ∈ A`, `φ_a(P) R_a ∅`." (`none` is `∅`.) -/
def IsIndividuallyRational (φ : Rule A Obj) : Prop :=
  ∀ (P : Profile A Obj) (a : A), WeaklyPrefers (P a) (φ P a) none

/-- **Strategy-proofness**, arXiv:2012.01025v4, §3, p.9: "A rule is strategy-proof if for every
agent `a ∈ A`, `P ∈ 𝒫`, and `P'_a ∈ 𝒫`, it is the case that `φ_a(P_a, P_{-a}) R_a φ_a(P'_a, P_{-a})`."
The profile `(P'_a, P_{-a})` is `Function.update P a Q`. -/
def IsStrategyProof [DecidableEq A] (φ : Rule A Obj) : Prop :=
  ∀ (P : Profile A Obj) (a : A) (Q : Pref Obj),
    WeaklyPrefers (P a) (φ P a) (φ (Function.update P a Q) a)

/-- **The lower contour set `ℒ(P, µ)` of `P` at `µ`**, arXiv:2012.01025v4, §3.1, p.12, in the
reading given by the sentence under the display: `ℒ(P, µ)` "contains all preference profiles that,
for each agent `a`, agree with `P_a` with respect to `µ(a)` and all objects preferred by `a` to
`µ(a)`, but may differ with respect to objects that `µ(a)` are preferred to".

Formally `P' ∈ ℒ(P, µ)` iff for every agent `a` and all `o, o' ∈ O`,
`(o P_a o' ∧ o' R_a µ(a)) ↔ (o P'_a o' ∧ o' R'_a µ(a))`: taking `o' = µ(a)` makes the sets of
objects strictly above `µ(a)` equal, and `o'` strictly above `µ(a)` makes the two orders agree on
that set.

**Formalization Note (correction).** The printed display is
`{P' : ∀ a, o, o' : o P_a o' P_a µ(a) ⟺ o P'_a o' P'_a µ(a)}`, which constrains only pairs of
objects strictly above `µ(a)`. With it Theorem 1 is false: one agent, `O = {x, y, ∅}`,
`φ(P) = x` iff `x P ∅` (else `∅`) is individually rational and sequentialized by the menu `{x, ∅}`,
but `P = (x, ∅, y)`, `µ = ∅`, `P' = (y, ∅, x)` violates the printed Definition 3. The corrected set
is the one described by the sentence under the display and used in the proof of Theorem 1 (p.41,
"following `P*` 'up to `µ*`'"); it implies every pair condition of the printed set. -/
def LowerContour (P : Profile A Obj) (μ : Allocation A Obj) : Set (Profile A Obj) :=
  {P' | ∀ (a : A) (o o' : Option Obj),
    (Prefers (P a) o o' ∧ WeaklyPrefers (P a) o' (μ a)) ↔
      (Prefers (P' a) o o' ∧ WeaklyPrefers (P' a) o' (μ a))}

/-- **Monotonic discoverability**, Definition 3, arXiv:2012.01025v4, p.13: "A rule `φ` satisfies
monotonic discoverability if, for any allocation `µ` and preference profile `P`, either
`φ(P) = µ` or there is an agent `a* ∈ A` such that for all `P' ∈ ℒ(P, µ)`, `µ(a*) ≠ φ_{a*}(P')`."

**Formalization Note.** `ℒ(P, µ)` is the corrected lower contour set `LowerContour` (see there). -/
def MonotonicDiscoverability (φ : Rule A Obj) : Prop :=
  ∀ (μ : Allocation A Obj) (P : Profile A Obj),
    φ P = μ ∨ ∃ a : A, ∀ P' ∈ LowerContour P μ, μ a ≠ φ P' a

end Rules

/-- A **choice history** `h = ((Ω₁, ω₁), (Ω₂, ω₂), …, (Ω_k, ω_k))`, arXiv:2012.01025v4, §3, p.9:
a finite sequence of menus `Ω_j ⊆ O` and choices `ω_j`, oldest first; `[]` is the empty choice
history `h_∅`.

**Formalization Note.** The paper's requirement `ω_j ∈ Ω_j` is not built into the type; every
history that a pick-an-object mechanism produces satisfies it (see `Reachable`, whose choices are
taken from the menus offered), and only such histories are quantified over in the theorems. -/
abbrev ChoiceHistory (Obj : Type*) : Type _ := List (Finset (Option Obj) × Option Obj)

/-- A **collective history** `h^A = (h₁, …, h_n)`, one choice history per agent
(arXiv:2012.01025v4, §3, p.9). -/
abbrev CollectiveHistory (A Obj : Type*) : Type _ := A → ChoiceHistory Obj

section Histories

variable {A Obj : Type*}

/-- `h^{A−∅}`, "the collective history consisting of `n` empty choice histories"
(arXiv:2012.01025v4, §3, p.9). -/
def emptyHistory : CollectiveHistory A Obj := fun _ => []

/-- The **last choice** `h→ = ω_k` of a choice history `h = (…, (Ω_k, ω_k))`
(arXiv:2012.01025v4, §3, p.9).

**Formalization Note.** The empty history has no last choice; it is given the value `∅` (`none`).
This value is never used as an outcome: the run only stops when every agent's menu is empty, and
`h^{A−∅}` is never a stopping state of a menu function, whose initial menus are non-empty. -/
def lastChoice (h : ChoiceHistory Obj) : Option Obj :=
  match h.getLast? with
  | some p => p.2
  | none => none

variable [Fintype Obj]

/-- A preference `Q` is **consistent with the choice history** `h`, arXiv:2012.01025v4, §3, p.9:
"for every `(Ω_i, ω_i) ∈ h` and `o ∈ Ω_i`, `ω_i R_a o`." -/
def ConsistentWith (Q : Pref Obj) (h : ChoiceHistory Obj) : Prop :=
  ∀ p ∈ h, ∀ o ∈ p.1, WeaklyPrefers Q p.2 o

/-- A profile `P` is **consistent with the collective history** `h^A`, arXiv:2012.01025v4, §3,
pp.9–10: "for every `i`, `P_{a_i}` is consistent with `h^A_i`" (`P ∈ 𝒫(h^A)`). -/
def ProfileConsistentWith (P : Profile A Obj) (h : CollectiveHistory A Obj) : Prop :=
  ∀ a : A, ConsistentWith (P a) (h a)

end Histories

/-- A **menu function** `S : H^A → Φ` gives every agent a menu (a subset of `O`) at every collective
history (arXiv:2012.01025v4, §3, p.10). Its constraints are `IsMenuFunction`. -/
abbrev MenuFunction (A Obj : Type*) : Type _ := CollectiveHistory A Obj → A → Finset (Option Obj)

/-- A **strategy** of an agent: a choice of object as a function of the agent's own choice history
and the menu she faces, `σ_a : H^A_S(a) ∪ {∅} × 2^O → O` (arXiv:2012.01025v4, §4, p.18). Its
admissibility condition is `IsValidStrategy`. -/
abbrev Strategy (Obj : Type*) : Type _ := ChoiceHistory Obj → Finset (Option Obj) → Option Obj

/-- A **type-strategy**: a map from preferences to strategies (arXiv:2012.01025v4, §4, p.18). -/
abbrev TypeStrategy (Obj : Type*) [Fintype Obj] : Type _ := Pref Obj → Strategy Obj

section Mechanism

variable {A Obj : Type*} [DecidableEq Obj]

/-- `S` is a **menu function**, arXiv:2012.01025v4, §3, p.10:
* "`S(h^{A−∅}) = (φ⁰₁, …, φ⁰_n)`, where for every `i`, `φ⁰_i` is a non-empty subset of `O`.
  These are the initial menus."
* "For any collective history `h^A` and agent `a_i`, let `k_i` be the number of non-empty menus
  that `a_i` faced in `h^A_i` … Then `S(h^A) = (φ₁, …, φ_n)`, where `φ_i ⊆ Ω^i_{k_i} \ {ω^i_{k_i}}`."

**Formalization Note.** The second constraint is imposed whenever agent `i`'s history is
non-empty (`k_i ≥ 1`), with `(Ω_{k_i}, ω_{k_i})` its last entry. A collective history other than
`h^{A−∅}` in which some agent has faced no menu is never produced by the mechanism (every initial
menu is non-empty), and the page states no constraint there; `S` is left unconstrained at such an
agent. -/
def IsMenuFunction (S : MenuFunction A Obj) : Prop :=
  (∀ i : A, (S emptyHistory i).Nonempty) ∧
    ∀ (h : CollectiveHistory A Obj) (i : A) (p : Finset (Option Obj) × Option Obj),
      (h i).getLast? = some p → S h i ⊆ p.1.erase p.2

/-- One period of the pick-an-object mechanism from the collective history `h` when every agent
`i` that receives a non-empty menu `S(h)_i` chooses `c i` from it, arXiv:2012.01025v4, §3, pp.10–11:
"for every agent `a_i` who received a non-empty menu, `h^{A−(t+1)}_i = h^{A−t}_i ⊕ (φ^t_i, σ^t_i)`,
and for those with an empty menu, `h^{A−(t+1)}_i = h^{A−t}_i`." -/
def advance (S : MenuFunction A Obj) (h : CollectiveHistory A Obj) (c : A → Option Obj) :
    CollectiveHistory A Obj :=
  fun i => if S h i = ∅ then h i else h i ++ [(S h i, c i)]

/-- The pick-an-object procedure **stops** at `h` when every menu is empty, arXiv:2012.01025v4,
§3, p.10: "If for all `i`, `φ^t_i = ∅`, then the procedure stops". -/
def IsStopped (S : MenuFunction A Obj) (h : CollectiveHistory A Obj) : Prop :=
  ∀ i : A, S h i = ∅

/-- One period of the mechanism when agent `i` plays the strategy `σ i`: each agent with a
non-empty menu chooses `σ_i(h_i, S_i(h))` (arXiv:2012.01025v4, §3, pp.10–11, and §4, p.18).
At a stopped history every menu is empty, so `step` leaves it unchanged. -/
def step (S : MenuFunction A Obj) (σ : A → Strategy Obj) (h : CollectiveHistory A Obj) :
    CollectiveHistory A Obj :=
  advance S h (fun i => σ i (h i) (S h i))

/-- The number of periods for which the run is iterated: `|A| · |O| + 1`.

**Formalization Note.** For a menu function and strategies that pick from every non-empty menu,
each agent's successive non-empty menus strictly shrink (each is contained in the previous one
with the previous choice removed), so each agent receives at most `|O|` non-empty menus after any
history, and the run reaches a stopped history after at most `|A| · |O|` periods (cf.
arXiv:2012.01025v4, p.11 and p.47, footnote 54). A stopped history is a fixed point of `step`. -/
def runLength (A Obj : Type*) [Fintype A] [Fintype Obj] : ℕ :=
  Fintype.card A * Fintype.card (Option Obj) + 1

/-- **The outcome `𝒪|_{h^A}(σ)`**, arXiv:2012.01025v4, §4, p.18: "the assignment that results from
following the PAO mechanism `S` when agents follow the strategies for `S` in `σ` starting from the
collective history `h^A`"; when the procedure stops it "outputs the allocation `µ`, where for each
`i`, `µ(a_i)` = `h^{A−t}_i→`" (§3, p.10), the last choice of each agent.

**Formalization Note.** The run is the `runLength A Obj = |A|·|O| + 1`-fold iterate of `step`,
after which the last choices are read off. For valid strategies the run has stopped by then (see
`runLength`) and further iteration changes nothing, so this is the paper's outcome; the bound is
never smaller than the number of periods the mechanism can take. -/
def outcome [Fintype A] [Fintype Obj] (S : MenuFunction A Obj) (σ : A → Strategy Obj)
    (h : CollectiveHistory A Obj) : Allocation A Obj :=
  fun i => lastChoice ((step S σ)^[runLength A Obj] h i)

/-- A strategy is **valid** if it picks an object from every non-empty menu it is given.

**Formalization Note.** This encodes the domain condition of arXiv:2012.01025v4, §4, p.18
("`σ_a(h, Ω) = o` implies that `h ⊕ (Ω, o) ∈ H^A_S(a)`"): an agent can only choose from the menu
she faces. Only the behaviour at histories and menus that actually occur matters, and every
strategy that chooses from the menus actually faced extends to a valid one, so the set of
attainable outcomes is unchanged. -/
def IsValidStrategy (σ : Strategy Obj) : Prop :=
  ∀ (h : ChoiceHistory Obj) (Ω : Finset (Option Obj)), Ω.Nonempty → σ h Ω ∈ Ω

variable [Fintype Obj]

/-- The `Q`-most-preferred element of a non-empty menu `Ω` (the element of least rank).

**Formalization Note.** On the empty menu, where no choice is made, the value is `∅` (`none`);
it is never used, since an agent with an empty menu does not choose. -/
def best (Q : Pref Obj) (Ω : Finset (Option Obj)) : Option Obj :=
  if hΩ : Ω.Nonempty then Q.symm ((Ω.image Q).min' (hΩ.image Q)) else none

/-- **The straightforward strategy with respect to `Q`**, Definition 1, arXiv:2012.01025v4, p.11:
"An agent `a ∈ A` follows a straightforward strategy with respect to `P_a` if, whenever presented
with a menu `I ⊆ O`, she chooses the most-preferred element of `I` according to `P_a`." It ignores
the history. -/
def straightforward (Q : Pref Obj) : Strategy Obj := fun _ Ω => best Q Ω

/-- The **straightforward type-strategy profile**: every agent maps her preference `Q` to the
straightforward strategy with respect to `Q` (arXiv:2012.01025v4, §4, pp.18–19). -/
def straightforwardProfile : A → TypeStrategy Obj := fun _ Q => straightforward Q

/-- **`S` sequentializes `φ`**, Definition 2, arXiv:2012.01025v4, p.11: "A pick-an-object mechanism
`S` sequentializes the rule `φ` if, for any preference profile `P`, the pick-an-object mechanism
`S` provides menus such that when each agent `a ∈ A` follows the straightforward strategy with
respect to `P_a`, the outcome `φ(P)` is produced." `S` must be a menu function (p.10); the run
starts at `h^{A−∅}`. -/
def Sequentializes [Fintype A] (S : MenuFunction A Obj) (φ : Rule A Obj) : Prop :=
  IsMenuFunction S ∧
    ∀ P : Profile A Obj, outcome S (fun a => straightforward (P a)) emptyHistory = φ P

/-- **The collective histories of `S`**, `H^A_S ∪ {h^{A−∅}}`, arXiv:2012.01025v4, §3, p.11:
"`H^A_S` contains all the collective histories that can take place when the pick-an-object
mechanism `S` is used … The other menus that they may face, and in which order, are determined by
all the possible combinations of choices that agents make".

**Formalization Note.** Inductive: `h^{A−∅}` is included (Definition 4 quantifies over
`H^A_S ∪ {h^{A−∅}}`), and from any such history every combination of choices `c i ∈ S_i(h)`
(for the agents with non-empty menus) leads to another. Choices are arbitrary, not only
straightforward ones. At a stopped history `advance` changes nothing. -/
inductive Reachable (S : MenuFunction A Obj) : CollectiveHistory A Obj → Prop
  | init : Reachable S emptyHistory
  | step {h : CollectiveHistory A Obj} (c : A → Option Obj) :
      Reachable S h → (∀ i : A, (S h i).Nonempty → c i ∈ S h i) → Reachable S (advance S h c)

/-- **Perfect ex-post equilibrium**, Definition 4, arXiv:2012.01025v4, p.19: "A type-strategy
profile `(Σ_a)_{a∈A}` for `S` is a perfect ex-post equilibrium if for every `a ∈ A`,
`h^A ∈ H^A_S ∪ {h^{A−∅}}`, strategy `σ'_a` for agent `a` and `P ∈ 𝒫^{|A|}`:
`𝒪_a|_{h^A}(Σ_a(P_a), (Σ_{a'}(P_{a'}))_{a'≠a}) R_a 𝒪_a|_{h^A}(σ'_a, (Σ_{a'}(P_{a'}))_{a'≠a})`."

**Formalization Note.** `h^A` ranges over `Reachable S` (all histories reachable under arbitrary
choices, and `h^{A−∅}`); the deviation `σ'` ranges over valid strategies (`IsValidStrategy`), the
paper's strategy space. -/
def IsPerfectExPostEquilibrium [Fintype A] [DecidableEq A] (S : MenuFunction A Obj)
    (ts : A → TypeStrategy Obj) : Prop :=
  ∀ (a : A) (h : CollectiveHistory A Obj), Reachable S h →
    ∀ σ' : Strategy Obj, IsValidStrategy σ' → ∀ P : Profile A Obj,
      WeaklyPrefers (P a) (outcome S (fun b => ts b (P b)) h a)
        (outcome S (Function.update (fun b => ts b (P b)) a σ') h a)

/-- **Pick-an-object implementable in perfect ex-post equilibrium**, arXiv:2012.01025v4, §4, p.19:
"there exists a PAO mechanism `S` that sequentializes `φ`, in which straightforward strategies
constitute a perfect ex-post equilibrium." -/
def PAOImplementable [Fintype A] [DecidableEq A] (φ : Rule A Obj) : Prop :=
  ∃ S : MenuFunction A Obj, Sequentializes S φ ∧ IsPerfectExPostEquilibrium S straightforwardProfile

end Mechanism

section RecursiveDominance

variable {Obj : Type*} [Fintype Obj] [DecidableEq Obj]

/-- The ranking key of `γ ⊕ Q|_{O∖I}`, with `I` the set of entries of `γ`: an entry of `γ` gets
its position in `γ`, any other object `o` gets `|γ| + Q(o)`. -/
def prefixKey (γ : List (Option Obj)) (Q : Pref Obj) (o : Option Obj) : ℕ :=
  if o ∈ γ then γ.idxOf o else γ.length + (Q o : ℕ)

theorem prefixKey_injective (γ : List (Option Obj)) (Q : Pref Obj) :
    Function.Injective (prefixKey γ Q) := by
  intro x y hxy
  unfold prefixKey at hxy
  by_cases hx : x ∈ γ <;> by_cases hy : y ∈ γ <;> simp only [hx, hy, if_true, if_false] at hxy
  · exact (List.idxOf_inj hx).1 hxy
  · have := List.idxOf_lt_length_of_mem hx; omega
  · have := List.idxOf_lt_length_of_mem hy; omega
  · exact Q.injective (Fin.ext (by omega))

/-- The strict preference whose ranking orders `O` by an injective key `f` (smaller key = more
preferred). -/
def ofKey (f : Option Obj → ℕ) (hf : Function.Injective f) : Pref Obj :=
  letI : LinearOrder (Option Obj) := LinearOrder.lift' f hf
  (Fintype.orderIsoFinOfCardEq (Option Obj) rfl).symm.toEquiv

/-- **The preference `γ ⊕ Q|_{O∖I}`**, arXiv:2012.01025v4, App. A, proof of Theorem 2, pp.43–44:
the entries of the tuple `γ` first, in the order of `γ`, followed by the remaining object types
`O ∖ I` ordered as in `Q` ("`P|_I` … the preference `P` restricted to `I`"; "`⊕`" is
concatenation, p.11, footnote 19).

**Formalization Note.** `I` is the set of entries of `γ`; in Definition 7 and Lemma 1 `γ` lists
the elements of `I` without repetition (a permutation of `I`), which the theorems require as
`γ.Nodup`. -/
def prefixPref (γ : List (Option Obj)) (Q : Pref Obj) : Pref Obj :=
  ofKey (prefixKey γ Q) (prefixKey_injective γ Q)

/-- **`Q ∈ 𝒫|_γ`**, arXiv:2012.01025v4, App. A, p.43: "`𝒫|_γ` is the set of all preferences in
which `γ` are the most-preferred object types, ordered as in the tuple `γ` itself": the `j`-th
entry of `γ` has rank `j`. -/
def StartsWith (Q : Pref Obj) (γ : List (Option Obj)) : Prop :=
  ∀ o ∈ γ, (Q o : ℕ) = γ.idxOf o

/-- **Recursive dominance**, Definition 7, arXiv:2012.01025v4, App. A, p.44: "A rule `φ` satisfies
recursive dominance if for every agent `a`, preference `P_a`, preferences of other agents `P_{−a}`,
set `I ⊆ O`, permutation `γ` of `I` and `P* ∈ 𝒫|_γ`:
`φ_a(γ ⊕ P|_{O∖I}, P_{−a}) R_a φ_a(P*, P_{−a})`."

**Formalization Note.** `(I, γ)` is encoded by the duplicate-free list `γ` (`I` = its set of
entries); `P|_{O∖I}` is read as agent `a`'s own preference `P_a` restricted to `O ∖ I`. -/
def RecursiveDominance {A : Type*} [DecidableEq A] (φ : Rule A Obj) : Prop :=
  ∀ (a : A) (P : Profile A Obj) (γ : List (Option Obj)), γ.Nodup →
    ∀ Pstar : Pref Obj, StartsWith Pstar γ →
      WeaklyPrefers (P a) (φ (Function.update P a (prefixPref γ (P a))) a)
        (φ (Function.update P a Pstar) a)

end RecursiveDominance

end PickAnObject


