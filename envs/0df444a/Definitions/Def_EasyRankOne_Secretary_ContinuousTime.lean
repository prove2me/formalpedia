-- Prove2me | Definitions.Def_EasyRankOne_Secretary_ContinuousTime
-- name    : EasyRankOne_Secretary_ContinuousTime
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:05:32.04624+00:00
-- url     : https://prove2.me/theorems/7e4b7ea4-c6c0-4802-8512-fb0ef527770b
-- title:
--   Continuous-time ordinal secretary algorithms, D_{O,t}, z_{O,e,t}, capacity (8), consistency (9) and rule (10) (§4.3)
-- statement:
--   In the **continuous-time model** (§4.3) each element $e$ arrives at an independent uniform time $T_e\in[0,1]$; the algorithm observes the time and immediately accepts or rejects $e$ using only observations so far and private randomness. It is **ordinal**: it sees values only through the tie-broken order of the observed elements; it may know the matroid and use its whole history. An algorithm is given by a jointly measurable **behavioural rule** $\mathrm{rule}(O,h,e,t)$: the probability of accepting the current arrival $e$ at time $t$ given the observed ordered set $O$ (including $e$) and the history $h$ of earlier arrivals with their times and decisions. The probability used is the rule clipped to $[0,1]$, and $0$ when accepting would make the accepted set dependent.
--
--   For an ordered set $O$, $0<t\le 1$ and $A\subseteq O$, the **accepted-set distribution** $\mathcal D_{O,t}(A)$ is the probability that the accepted set is $A$ conditional on precisely $O$ having arrived by $t$: since the arrival times of $O$ are then i.i.d. uniform on $[0,t]$,
--   $$\mathcal D_{O,t}(A)=t^{-|O|}\int_{[0,t]^O}\Pr[\text{accepted set}=A\mid \text{arrival times }x]\,dx .$$
--   The **accepting mass** $z_{O,e,t}(A)$ is the joint probability that the previous accepted set is $A$ and $e$ is accepted, conditional on $e$ arriving at time $t$ with preceding observed set $O-e$. A **family** $(\mathcal D,z)$ is indexed by ordered sets; each $\mathcal D_{O,t}$ is a probability distribution on the independent subsets of $O$, $\mathcal D_{\emptyset,t}(\emptyset)=1$, and $z$ is measurable in $t$ and zero outside $e\in O$, $A\subseteq O-e$. **Capacity (8):** for almost every time $t\in(0,1)$ and $e\in O$, $A\subseteq O-e$,
--   $$0\le z_{O,e,t}(A)\le \mathcal D_{O-e,t}(A),\qquad z_{O,e,t}(A)=0\ \text{ if } A+e\notin\mathcal I .$$
--   **Consistency (9):** for $m=|O|>0$, $A\subseteq O$, $0<t\le 1$,
--   $$t^m\mathcal D_{O,t}(A)=\int_0^t u^{m-1}\Big[\sum_{e\in O\setminus A}\big(\mathcal D_{O-e,u}(A)-z_{O,e,u}(A)\big)+\sum_{e\in A} z_{O,e,u}(A-e)\Big]du .$$
--   An algorithm **realizes** the family if its $\mathcal D_{O,t}$ and $z_{O,e,t}$ equal the family's for every value order: $\mathcal D$ at every positive horizon, and $z$ almost everywhere in time, as specified by footnote 2. **Rule (10)** accepts $e$ at time $t$ from accepted set $A$ with probability $q_{O,e,t}(A)=z_{O,e,t}(A)/\mathcal D_{O-e,t}(A)$, $0/0=0$.
--
--   **Formalization Note.** Ordered sets are duplicate-free lists in decreasing order; `D O t A`, `z O e t A`. `histExp` is the expectation over the decision coins along the chronological arrivals; `arrivals x O` sorts `O` by arrival time (ties, a null event, by label); `boxInt O t f` is $\int_{[0,t]^O} f$ (coordinates outside $O$ set to $0$). `algD`, `algZ` are the algorithm's $\mathcal D$ and $z$; `algProb` is the probability of an event of the final accepted set when all elements arrive. `Capacity` is required almost everywhere on $t\in(0,1)$, `Consistency` requires the integrand to be integrable on $(0,t]$; `Realizes` quantifies over all nonnegative value assignments $v$ (every value order) and every $O\subseteq V$, with $\mathcal D$ matched for $t\in(0,1]$ and $z$ for almost every $t\in(0,1)$, and requires the integrands defining the algorithm's $\mathcal D_{O,t}(A)$ and $z_{O,e,t}(A)$ to be integrable (`BoxIntegrable`), i.e. these conditional probabilities exist.
--   `MeasurableRule` requires the effective acceptance probability to be jointly measurable in the past arrival times and current time, for each fixed discrete history and observed order. `Realizes` includes this requirement. Values at impossible histories may be extended measurably; only legal histories enter the conditional laws.
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 11, §4 and §4.1; p. 12; p. 14, §4.3, (8), (9), (10)

import Mathlib
import Definitions.Def_EasyRankOne_Secretary_Greedy

open MeasureTheory

/-!
# Continuous-time ordinal secretary algorithms, accepted-set distributions, capacity and
# consistency

Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, *As Easy as Rank One*, STOC 2027 submission
(manuscript of November 2026, sha256 f74f3f91…), §4 p. 11, §4.1 pp. 11–12, §4.3 p. 14.

"In the continuous-time model, each element e arrives at an independent uniform time
T_e ∈ [0, 1]. The algorithm observes this time when e arrives and immediately accepts or rejects
e, using only observations so far and independent private randomness." "An algorithm is ordinal
if it uses values only through the tie-broken order among observed elements; it may otherwise use
its entire history and internal randomness. The characterization allows advance knowledge of the
matroid."

Encoding.
* An algorithm for a known matroid `M` is a **behavioural rule** `rule obs h e t`: the probability
  of accepting the current arrival `e` at time `t`, given the observed ordered set `obs`
  (the arrived elements including `e`, listed in decreasing tie-broken order: the only access to
  values) and the history `h` (earlier arrivals in chronological order with their times and
  decisions). Private randomness is the coin of each decision. The probability actually used is
  the rule clipped to `[0, 1]`, and `0` when accepting would make the accepted set dependent (the
  accepted set must be independent).
* `histExp` is the expectation, over the decision coins, of a function of the final history when
  the arrivals `arr` (chronological, with times) are processed from history `h`.
* `boxInt O t f` is the integral of `f` over `x ∈ [0, t]^O` (Lebesgue measure on the coordinates
  in `O`; the coordinates outside `O` are set to `0`); `BoxIntegrable O t f` says it exists.
* `algD M v rule O t A = D_{O,t}(A)`: conditional on precisely `O` having arrived by `t`, the
  arrival times of `O` are independent uniforms on `[0, t]`, so
  `D_{O,t}(A) = t^{-|O|} ∫_{[0,t]^O} Pr[accepted set = A | arrival times x] dx`.
* `algZ M v rule O e t A = z_{O,e,t}(A)`: the joint probability that the previous accepted set is
  `A` and `e` is accepted, conditional on `e` arriving at `t` with preceding observed set `O − e`.
* Families `D : List α → ℝ → Finset α → ℝ`, `z : List α → α → ℝ → Finset α → ℝ` are indexed by
  ordered sets (duplicate-free lists in decreasing order), `D O t A = D_{O,t}(A)`,
  `z O e t A = z_{O,e,t}(A)`.
-/

namespace EasyRankOne.Secretary

variable {α : Type*}

/-- A behavioural rule of a continuous-time ordinal algorithm: observed ordered set (including
the current arrival), chronological history `(element, time, accepted?)`, current arrival,
current time ↦ acceptance probability. -/
abbrev Rule (α : Type*) := List α → List (α × ℝ × Bool) → α → ℝ → ℝ

/-- The accepted set recorded in a history. -/
def accSet [DecidableEq α] (h : List (α × ℝ × Bool)) : Finset α :=
  ((h.filter fun r => r.2.2).map Prod.fst).toFinset

open Classical in
/-- The acceptance probability actually used: the rule clipped to `[0, 1]`, and `0` when
accepting `e` would make the accepted set dependent. -/
noncomputable def accProb [DecidableEq α] (M : Matroid α) (rule : Rule α) (obs : List α)
    (h : List (α × ℝ × Bool)) (e : α) (t : ℝ) : ℝ :=
  if M.Indep (↑(insert e (accSet h)) : Set α) then max 0 (min 1 (rule obs h e t)) else 0

/-- A measurable behavioural rule. For each fixed discrete history, the effective acceptance
probability is jointly measurable in its past arrival times and the current time in `(0,1)`.
The sequence supplies the finitely many history coordinates; unused coordinates are ignored.
This is a property of the algorithm, not an extra hypothesis on a feasible family. -/
def MeasurableRule [DecidableEq α] (M : Matroid α) (rule : Rule α) : Prop :=
  ∀ (obs : List α) (past : List (α × Bool)) (e : α), obs.Nodup → e ∈ obs →
    Measurable (fun xt : {xt : (ℕ → ℝ) × ℝ // xt.2 ∈ Set.Ioo (0 : ℝ) 1} =>
      accProb M rule obs
        (past.zipIdx.map fun r => (r.1.1, xt.val.1 r.2, r.1.2)) e xt.val.2)

/-- Expectation over the decision coins of `F (final history)`, processing the chronological
arrivals `arr` from the history `h`. At each arrival the rule sees the observed ordered set
`sortDesc v (arrived elements)`. -/
noncomputable def histExp [LinearOrder α] (M : Matroid α) (v : α → ℝ) (rule : Rule α) :
    List (α × ℝ) → List (α × ℝ × Bool) → (List (α × ℝ × Bool) → ℝ) → ℝ
  | [], h, F => F h
  | (e, t) :: rest, h, F =>
      let q := accProb M rule (sortDesc v (insert e (h.map Prod.fst).toFinset)) h e t
      q * histExp M v rule rest (h ++ [(e, t, true)]) F +
        (1 - q) * histExp M v rule rest (h ++ [(e, t, false)]) F

/-- The elements of `O` in chronological order of the arrival times `x` (ties, a null event,
broken by labels), with their times. -/
noncomputable def arrivals [LinearOrder α] (x : α → ℝ) (O : Finset α) : List (α × ℝ) :=
  (O.toList.mergeSort (fun a b => decide (toLex (x a, a) ≤ toLex (x b, b)))).map
    fun a => (a, x a)

open Classical in
/-- `∫_{[0,t]^O} f(x) dx`: Lebesgue measure on the coordinates in `O`, the others set to `0`. -/
noncomputable def boxInt (O : Finset α) (t : ℝ) (f : (α → ℝ) → ℝ) : ℝ :=
  ∫ y in Set.univ.pi (fun _ : O => Set.Icc (0 : ℝ) t),
    f (fun a => if h : a ∈ O then y ⟨a, h⟩ else 0)

open Classical in
/-- `f` is integrable on `[0, t]^O` (the integral `boxInt O t f` exists). -/
def BoxIntegrable (O : Finset α) (t : ℝ) (f : (α → ℝ) → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun y : O → ℝ => f (fun a => if h : a ∈ O then y ⟨a, h⟩ else 0))
    (Set.univ.pi (fun _ : O => Set.Icc (0 : ℝ) t))

/-- `D_{O,t}(A)` of the algorithm `rule` on the instance `(M, v)`: the distribution of the
accepted set conditional on precisely `O` having arrived by `t`. -/
noncomputable def algD [LinearOrder α] (M : Matroid α) (v : α → ℝ) (rule : Rule α)
    (O : Finset α) (t : ℝ) (A : Finset α) : ℝ :=
  (t ^ O.card)⁻¹ *
    boxInt O t (fun x => histExp M v rule (arrivals x O) [] (fun h => if accSet h = A then 1 else 0))

/-- `z_{O,e,t}(A)` of the algorithm `rule` on the instance `(M, v)`: the joint probability that
the previous accepted set is `A` and `e` is accepted, conditional on `e` arriving at time `t`
with preceding observed set `O − e`. -/
noncomputable def algZ [LinearOrder α] (M : Matroid α) (v : α → ℝ) (rule : Rule α)
    (O : Finset α) (e : α) (t : ℝ) (A : Finset α) : ℝ :=
  (t ^ (O.card - 1))⁻¹ *
    boxInt (O.erase e) t (fun x => histExp M v rule (arrivals x (O.erase e)) []
      (fun h => if accSet h = A then accProb M rule (sortDesc v O) h e t else 0))

/-- The probability of an event of the final accepted set of `rule` when every element of `α`
arrives at an independent Uniform[0,1] time. -/
noncomputable def algProb [Fintype α] [LinearOrder α] (M : Matroid α) (v : α → ℝ)
    (rule : Rule α) (E : Finset α → Prop) : ℝ :=
  open Classical in
  boxInt Finset.univ 1 (fun x => histExp M v rule (arrivals x Finset.univ) []
    (fun h => if E (accSet h) then 1 else 0))

/-- The objects of §4.3: each `D_{O,t}` (`0 < t ≤ 1`) is a probability distribution on the
independent subsets of `O`, `D_{∅,t}(∅) = 1`; the accepting masses are measurable in `t` and
vanish outside their support `e ∈ O`, `A ⊆ O − e` (p. 12: "All entries outside their stated
supports are zero"). -/
def IsFamily [DecidableEq α] (M : Matroid α) (D : List α → ℝ → Finset α → ℝ)
    (z : List α → α → ℝ → Finset α → ℝ) : Prop :=
  (∀ O : List α, O.Nodup → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      (∀ A, 0 ≤ D O t A) ∧ (∀ A, D O t A ≠ 0 → A ⊆ O.toFinset ∧ M.Indep (↑A : Set α)) ∧
      ∑ A ∈ O.toFinset.powerset, D O t A = 1) ∧
  (∀ t ∈ Set.Ioc (0 : ℝ) 1, D [] t ∅ = 1) ∧
  (∀ O e A, Measurable fun t => z O e t A) ∧
  (∀ O e t A, ¬ (e ∈ O ∧ A ⊆ (O.erase e).toFinset) → z O e t A = 0)

/-- Capacity (8): for every ordered set `O`, `e ∈ O`, `A ⊆ O − e` and arrival time
almost every `t ∈ (0, 1)`: `0 ≤ z_{O,e,t}(A) ≤ D_{O−e,t}(A)`, and
`z_{O,e,t}(A) = 0` if `A + e ∉ I` (footnote 2: masses are identified up to null times). -/
def Capacity [DecidableEq α] (M : Matroid α) (D : List α → ℝ → Finset α → ℝ)
    (z : List α → α → ℝ → Finset α → ℝ) : Prop :=
  ∀ O : List α, O.Nodup → ∀ e ∈ O, ∀ A ⊆ (O.erase e).toFinset,
    ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
    0 ≤ z O e t A ∧ z O e t A ≤ D (O.erase e) t A ∧
      (¬ M.Indep (↑(insert e A) : Set α) → z O e t A = 0)

/-- The integrand of (9): `u^{m−1} [Σ_{e∈O∖A} (D_{O−e,u}(A) − z_{O,e,u}(A)) + Σ_{e∈A} z_{O,e,u}(A − e)]`. -/
noncomputable def consistencyIntegrand [DecidableEq α] (D : List α → ℝ → Finset α → ℝ)
    (z : List α → α → ℝ → Finset α → ℝ) (O : List α) (A : Finset α) (u : ℝ) : ℝ :=
  u ^ (O.length - 1) *
    ((∑ e ∈ O.toFinset \ A, (D (O.erase e) u A - z O e u A)) +
      ∑ e ∈ A, z O e u (A.erase e))

/-- Consistency (9): for every nonempty ordered set `O` with `m = |O|`, `A ⊆ O` and
`0 < t ≤ 1`, the integrand is integrable on `(0, t]` and
`t^m D_{O,t}(A) = ∫_0^t u^{m−1}[…] du`. -/
def Consistency [DecidableEq α] (D : List α → ℝ → Finset α → ℝ)
    (z : List α → α → ℝ → Finset α → ℝ) : Prop :=
  ∀ O : List α, O.Nodup → O ≠ [] → ∀ A ⊆ O.toFinset, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn (consistencyIntegrand D z O A) (Set.Ioc 0 t) ∧
      t ^ O.length * D O t A = ∫ u in Set.Ioc 0 t, consistencyIntegrand D z O A u

/-- The algorithm `rule` realizes the family `(D, z)` on the matroid `M`: for every nonnegative
value assignment `v` (every value order) and every `O ⊆ V`, the conditional probabilities
defining the algorithm's `D_{O,t}(A)` and `z_{O,e,t}(A)` exist (their integrands are integrable),
`D_{O,t} = ` the algorithm's accepted-set distribution for `0 < t ≤ 1` and `z_{O,e,t} = ` its
accepting masses for almost every `0 < t < 1` (footnote 2), where the ordered set is `O` under
the tie-broken order of `v`. The effective rule is jointly measurable in the arrival times. -/
def Realizes [LinearOrder α] (M : Matroid α) (rule : Rule α) (D : List α → ℝ → Finset α → ℝ)
    (z : List α → α → ℝ → Finset α → ℝ) : Prop :=
  MeasurableRule M rule ∧
  ∀ v : α → ℝ, (∀ a, 0 ≤ v a) → ∀ O : Finset α,
    (∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ A,
      BoxIntegrable O t (fun x => histExp M v rule (arrivals x O) []
        (fun h => if accSet h = A then 1 else 0)) ∧
      D (sortDesc v O) t A = algD M v rule O t A) ∧
    (∀ e ∈ O, ∀ A, ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      BoxIntegrable (O.erase e) t (fun x => histExp M v rule (arrivals x (O.erase e)) []
        (fun h => if accSet h = A then accProb M rule (sortDesc v O) h e t else 0)) ∧
      z (sortDesc v O) e t A = algZ M v rule O e t A)

/-- Rule (10): accept the current arrival `e` at time `t` from accepted set `A` with probability
`q_{O,e,t}(A) = z_{O,e,t}(A) / D_{O−e,t}(A)` (Lean's `x / 0 = 0` gives `0/0 = 0`). -/
noncomputable def rule10 [DecidableEq α] (D : List α → ℝ → Finset α → ℝ)
    (z : List α → α → ℝ → Finset α → ℝ) : Rule α :=
  fun obs h e t => z obs e t (accSet h) / D (obs.erase e) t (accSet h)

end EasyRankOne.Secretary


