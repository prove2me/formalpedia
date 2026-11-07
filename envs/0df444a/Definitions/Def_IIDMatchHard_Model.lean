-- Prove2me | Definitions.Def_IIDMatchHard_Model
-- name    : IIDMatchHard_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:17.025059+00:00
-- url     : https://prove2.me/theorems/a79b4541-3d7b-49e9-bef5-952eb28bb423
-- title:
--   Deterministic online policies, their runs, greedy policies, and the online optimum of an i.i.d. instance
-- statement:
--   An **unweighted known-i.i.d. instance** $I$ of online stochastic matching consists of a set $U$ of offline vertices, a finite set $Y$ of online types, a neighbor set $N(y)\subseteq U$ for every type $y$ (all weights are $0$ or $1$, weight $1$ exactly on $N(y)$), a distribution $p$ on $Y$, and a number $T$ of online vertices whose types $y_1,\dots,y_T$ are drawn independently from $p$.
--
--   A **deterministic online policy** $\pi$ sees, when an online vertex arrives, the types of the vertices that arrived before it, the set $S$ of offline vertices already matched, and the current type $y$. It proposes an offline vertex $u$ or rejects. The proposal is executed when $u\in N(y)\setminus S$; otherwise the arrival is rejected. Every offline vertex is matched at most once, and decisions are irrevocable. For a sequence of types, $M_\pi(\ell)$ is the number of matches $\pi$ makes on its first $\ell$ types. The run is also defined for **history-dependent** neighbor sets $N(h,y)$, where $h$ is the list of earlier types; this is how the adjusted Poisson model is run.
--
--   A policy is **greedy** if it matches an arrival whenever the arrival has a free neighbor.
--
--   The **value** of $\pi$ is
--   $$\mathbb E[M_\pi(T)]=\sum_{(y_1,\dots,y_T)\in Y^T}\Big(\prod_{k=1}^T p(y_k)\Big)\,M_\pi(T),$$
--   and the **online optimum** (Definition 2.1) is
--   $$\mathrm{OPT}(I)=\sup_\pi \mathbb E[M_\pi(T)],$$
--   the supremum over deterministic policies.
--
--   These are the objects of the goal theorem and of every milestone.
--
--   **Formalization Note** A policy is a function `List Y → Finset U → Y → Option U`. The matched set is a function of the earlier types for a deterministic policy, so it adds no power; it lets the same policy run in several arrival models. Greedy is required at the states the policy itself reaches. §2.1 states that a deterministic policy attains the optimum, so the supremum is taken over deterministic policies; it is a real supremum, bounded by $T$ when $p$ is a probability vector.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), §2 and §2.1, p.4 (PDF p.5), Definition 2.1, Proposition 2.2

import Mathlib

set_option autoImplicit false

namespace IIDMatchHard

/-- A **deterministic online policy** for unweighted online matching with offline vertices `U`
and online types `Y`: given the types of the online vertices that have arrived so far (oldest
first), the set of offline vertices already matched, and the type of the current arrival, it
proposes an offline vertex to match the arrival to, or `none` to reject it. Teng, Yang,
*Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026, sha256
f0193d92…), §2, p.4 (PDF p.5).

**Formalization Note.** "An online policy can make decisions based on the online vertices that
have arrived so far and their matching history, but it does not see future arrivals" (p.4).
The matched set is a function of the past types for a deterministic policy, so passing it adds
no power; it lets the same policy be run in several arrival models. A proposal that is not a
free neighbor of the current type is executed as a rejection (`stepState`), so a policy can never
match a vertex twice or match outside the neighbor set. Randomized policies are not needed:
§2.1 (p.4) notes that a deterministic policy is optimal. -/
abbrev Policy (U Y : Type*) : Type _ := List Y → Finset U → Y → Option U

variable {U Y : Type*} [DecidableEq U]

/-- One step of the run of a policy `π` against **history-dependent neighbor sets**
`N : List Y → Y → Finset U` (`N h y` is the neighbor set of an arrival of type `y` after the
history `h`). The state is the matched set and the number of matches. If `π` proposes `u`, and
`u` is a neighbor (`u ∈ N h y`) that is still free (`u ∉ S`), the arrival is matched to `u`;
otherwise it is rejected. Teng–Yang (sha256 f0193d92…), §2, p.4: "an online policy either
matches it to a free neighbor u of y … or rejects it. Each offline vertex can only be matched
once, and the decisions are irrevocable." -/
def stepState (N : List Y → Y → Finset U) (π : Policy U Y) (h : List Y) (st : Finset U × ℕ)
    (y : Y) : Finset U × ℕ :=
  match π h st.1 y with
  | some u => if u ∈ N h y ∧ u ∉ st.1 then (insert u st.1, st.2 + 1) else st
  | none => st

/-- Run of `π` on the arrivals `ys` after the history `h`, from the state `st`. -/
def runFrom (N : List Y → Y → Finset U) (π : Policy U Y) :
    List Y → List Y → Finset U × ℕ → Finset U × ℕ
  | _, [], st => st
  | h, y :: ys, st => runFrom N π (h ++ [y]) ys (stepState N π h st y)

/-- The final state (matched set, number of matches) of `π` on the type sequence `ys`, processed
in order from an empty matching. -/
def run (N : List Y → Y → Finset U) (π : Policy U Y) (ys : List Y) : Finset U × ℕ :=
  runFrom N π [] ys (∅, 0)

/-- The set of offline vertices matched by `π` after processing `ys`. -/
def matched (N : List Y → Y → Finset U) (π : Policy U Y) (ys : List Y) : Finset U :=
  (run N π ys).1

/-- `M_π`: the number of matches of `π` on the type sequence `ys`; on the first `ℓ` types it is
`numMatches N π (ys.take ℓ)`, the paper's `M_π(ℓ)` (§2.1, p.4). -/
def numMatches (N : List Y → Y → Finset U) (π : Policy U Y) (ys : List Y) : ℕ :=
  (run N π ys).2

/-- Static (history-independent) neighbor sets `nbr`, viewed as history-dependent ones. -/
def static (nbr : Y → Finset U) : List Y → Y → Finset U := fun _ y => nbr y

/-- `π` is **greedy** for the neighbor sets `N`: whenever the current arrival (after any
history `h`, in the state `π` itself reaches on `h`) has a free neighbor, `π` proposes a free
neighbor, so the arrival is matched. Teng–Yang (sha256 f0193d92…), §2.1, p.4: "greedy policies,
i.e., policies that match an online arrival whenever there is a free neighbor."

**Formalization Note.** Only the states the policy reaches matter, so the condition is imposed
at the matched set `matched N π h` that `π` produces on `h`. -/
def IsGreedy (N : List Y → Y → Finset U) (π : Policy U Y) : Prop :=
  ∀ (h : List Y) (y : Y), (N h y \ matched N π h).Nonempty →
    ∃ u ∈ N h y \ matched N π h, π h (matched N π h) y = some u

/-- An **unweighted known-i.i.d. instance** of online stochastic matching: offline vertices `U`,
online types `Y`, the neighbor set `nbr y` of each type (all weights are `0` or `1`, weight one
exactly on `nbr y`), the type distribution `p` and the number `T` of online vertices. Teng–Yang
(sha256 f0193d92…), §2 and §2.1, p.4.

**Formalization Note.** The structure carries data only; that `p` is a probability vector is
stated where needed (it holds for every instance the paper builds). -/
structure IIDModel (U Y : Type*) where
  /-- The neighbors of each online type. -/
  nbr : Y → Finset U
  /-- The probability of each online type. -/
  p : Y → ℝ
  /-- The number of online vertices. -/
  T : ℕ

variable [Fintype Y]

/-- The **value** `E[M_π(T)]` of a deterministic policy `π` on an i.i.d. instance: the expected
number of matches on `T` independent types drawn from `p`, as a finite sum over type sequences.
Teng–Yang (sha256 f0193d92…), §2.1, p.4. -/
noncomputable def value (I : IIDModel U Y) (π : Policy U Y) : ℝ :=
  ∑ ys : Fin I.T → Y, (∏ k, I.p (ys k)) * (numMatches (static I.nbr) π (List.ofFn ys) : ℝ)

/-- The **online optimum** `OPT(I) = sup_π E[M_π(T)]` of an i.i.d. instance (Definition 2.1,
p.4 (PDF p.5); §2.1, p.4), a supremum over all deterministic policies.

**Formalization Note.** By §2.1, "there exists a deterministic policy that is optimal, so
OPT(I) = max_π E[M_π(T)] where the maximum is over deterministic policies π". The supremum is a
real `iSup`; it is bounded above by `T` whenever `p` is a probability vector (every value is at
most `T`), so it is not a junk value. -/
noncomputable def OPT (I : IIDModel U Y) : ℝ :=
  ⨆ π : Policy U Y, value I π

end IIDMatchHard


