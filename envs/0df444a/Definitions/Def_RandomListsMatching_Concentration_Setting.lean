-- Prove2me | Definitions.Def_RandomListsMatching_Concentration_Setting
-- name    : RandomListsMatching_Concentration_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:06:59.049799+00:00
-- url     : https://prove2.me/theorems/45453186-955f-4e07-8266-b45abf914f7b
-- title:
--   §1 and §2, pp. 1–5 — i.i.d. arrivals with types and random lists, the list-greedy online matching ALG, and the offline maximum matching OPT
-- statement:
--   This definition fixes the objects of the online stochastic matching model of Jaillet and Lu and of their class of **Random Lists Algorithms** (RLA).
--
--   **The graph.** $G = \{A \cup I, E\}$ is a bipartite graph with a finite set $A$ of advertisers, a set $I$ of impression types, and an edge set $E \subseteq A \times I$; $(a, i) \in E$ means that advertiser $a$ is interested in impressions of type $i$.
--
--   **The greedy run of a list sequence.** A list is a finite sequence of advertisers. Given lists $l_1, \dots, l_n$ for $n$ successive requests, the sets $W_j$ of advertisers matched right after the $j$-th request are defined by $W_0 = \emptyset$ and
--   $$
--   W_j = \begin{cases} W_{j-1} \cup \{k\} & \text{if } k \text{ is the first advertiser of } l_j \text{ (in list order) with } k \notin W_{j-1},\\ W_{j-1} & \text{if every advertiser of } l_j \text{ lies in } W_{j-1} \text{ (the request is dropped).}\end{cases}
--   $$
--   Each assignment matches a new advertiser, so the cardinality of the resulting matching is $\mathrm{alg}(l_1, \dots, l_n) = |W_n|$.
--
--   **The offline optimum.** For realized types $\tau_1, \dots, \tau_n \in I$, a realization matching assigns some requests $t$ to advertisers $a$ with $(a, \tau_t) \in E$, no advertiser receiving two requests. $\mathrm{opt}(\tau)$ is the largest number of requests such a matching assigns.
--
--   **Arrivals.** Each request carries an outcome $x$ in a finite set $\mathcal X$, which determines its impression type $\mathrm{typ}(x) \in I$ and the list $\mathrm{lst}(x)$ drawn for it. The outcomes $\omega_1, \dots, \omega_n$ of the $n$ requests are i.i.d. with a law $\nu$ on $\mathcal X$. Then
--   $$
--   \mathrm{ALG}(\omega) = \mathrm{alg}\bigl(\mathrm{lst}(\omega_1), \dots, \mathrm{lst}(\omega_n)\bigr), \qquad \mathrm{OPT}(\omega) = \mathrm{opt}\bigl(\mathrm{typ}(\omega_1), \dots, \mathrm{typ}(\omega_n)\bigr),
--   $$
--   and $\mathbb E[\mathrm{ALG}]$, $\mathbb E[\mathrm{OPT}]$ are their expectations under $\nu^{\otimes n}$. Finally, the lists are **interested** when every advertiser on $\mathrm{lst}(x)$ is adjacent to $\mathrm{typ}(x)$, for every $x$.
--
--   An RLA with type distribution $p$ on $I$ and list distributions $\mathcal D_i$ is the case $\mathcal X = \{(i, l) : l \in \Omega_i\}$, $\nu(i, l) = p_i \mathcal D_i(l)$, $\mathrm{typ}(i, l) = i$, $\mathrm{lst}(i, l) = l$; its lists are interested by construction. These objects are shared by every statement of the mission.
--
--   **Formalization Note** The outcome set $\mathcal X$ is a finite type with the discrete σ-algebra, so every function of the arrivals is measurable and integrable, and expectations are honest finite sums. The model allows any joint law of type and list, which covers every RLA; lists need not be nonempty or repetition-free (repetitions do not change the greedy rule). A matching is encoded as a partial assignment `Fin n → Option A`, and OPT is a maximum over a finite nonempty set (the empty assignment qualifies), so it is never a junk value. The OPT encoding copies `OnlineStochMatching.TSM.Model` (Feldman et al. series), which is not published and so cannot be imported.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), pp. 1–3, §1 (model) and §1.1 (OPT, Random Lists Algorithms); p. 5, §2 (the lists L_1, …, L_n and the sets W_j of the proof of Claim 1)

import Mathlib

namespace RandomListsMatching.Concentration

open MeasureTheory

/-- One period of a Random Lists Algorithm (Jaillet & Lu, *Online Stochastic Matching: New
Algorithms with Better Bounds*, accepted manuscript (rev. June 2013), §1.1, p. 3, RLA step 3).
`W` is the set of advertisers already matched and `l` is the list drawn for the arriving request.
If every advertiser of `l` is in `W` the request is dropped (`W` is unchanged); otherwise the
request is assigned to the first advertiser of `l`, in list order, that is not in `W`. -/
def greedyStep {A : Type} [DecidableEq A] (W : Finset A) (l : List A) : Finset A :=
  match l.find? (fun a => decide (a ∉ W)) with
  | some a => insert a W
  | none => W

/-- `matchedAfter ls j` is the set `W_j` of advertisers matched right after the `j`-th arrival
(§2, p. 5, proof of Claim 1) when the `n` requests receive the lists `ls 0, …, ls (n-1)`:
`W_0 = ∅` and `W_{j+1}` is one greedy step of `W_j` with the list of the `(j+1)`-th request.
Beyond `n` the set no longer changes. -/
def matchedAfter {A : Type} [DecidableEq A] {n : ℕ} (ls : Fin n → List A) : ℕ → Finset A
  | 0 => ∅
  | j + 1 => if h : j < n then greedyStep (matchedAfter ls j) (ls ⟨j, h⟩) else matchedAfter ls j

/-- The cardinality of the matching that a Random Lists Algorithm builds from the realization
`(l_1, …, l_n)` of the lists (§2, p. 5). Every assignment matches a new advertiser, so the number
of assigned requests equals `|W_n|`. -/
def algValue {A : Type} [DecidableEq A] {n : ℕ} (ls : Fin n → List A) : ℕ :=
  (matchedAfter ls n).card

/-- A matching of the realization graph (§1.1, p. 3). The graph `G = {A ∪ I, E}` has advertisers
`A`, impression types `I` and edge set `E ⊆ A × I`; the `n` requests have types `τ 0, …, τ (n-1)`.
`M t = some a` means that request `t` is assigned to advertiser `a`: every assigned pair is an
edge of `G`, and no advertiser receives two requests. -/
def IsRealizationMatching {A I : Type} {n : ℕ} (E : Finset (A × I)) (τ : Fin n → I)
    (M : Fin n → Option A) : Prop :=
  (∀ t a, M t = some a → (a, τ t) ∈ E) ∧ ∀ s t a, M s = some a → M t = some a → s = t

/-- The number of requests that a partial assignment `M` assigns. -/
def matchSize {A : Type} {n : ℕ} (M : Fin n → Option A) : ℕ :=
  (Finset.univ.filter fun t => (M t).isSome = true).card

/-- The offline optimum for the realized types `τ` (§1.1, p. 3): the cardinality of a maximum
matching of the realization graph, a maximum over the finite nonempty set of realization
matchings (the empty assignment is one). -/
noncomputable def optValue {A I : Type} [Fintype A] {n : ℕ} (E : Finset (A × I))
    (τ : Fin n → I) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n → Option A)).filter (IsRealizationMatching E τ)).sup
    matchSize

/-- "Every list only contains interested advertisers" (§2, p. 5). An arrival outcome `x` carries
the impression type `typ x` and the list `lst x` drawn for it; every advertiser on the list is
adjacent to that type in `G`. -/
def ListsInterested {A I X : Type} (E : Finset (A × I)) (typ : X → I) (lst : X → List A) :
    Prop :=
  ∀ x, ∀ a ∈ lst x, (a, typ x) ∈ E

/-- The random variable ALG: the number of requests the Random Lists Algorithm assigns when the
`n` arrivals have outcomes `ω 0, …, ω (n-1)`, the `j`-th request receiving the list `lst (ω j)`. -/
def ALG {A X : Type} [DecidableEq A] {n : ℕ} (lst : X → List A) (ω : Fin n → X) : ℕ :=
  algValue (fun j => lst (ω j))

/-- The random variable OPT (§1.1, p. 3): the maximum matching cardinality of the realization in
which the `j`-th request has type `typ (ω j)`. -/
noncomputable def OPT {A I X : Type} [Fintype A] {n : ℕ} (E : Finset (A × I)) (typ : X → I)
    (ω : Fin n → X) : ℕ :=
  optValue E (fun j => typ (ω j))

/-- The law of the `n` arrivals: the outcomes `ω 0, …, ω (n-1)` are i.i.d. with law `ν`. -/
noncomputable def arrivalLaw {X : Type} [MeasurableSpace X] (ν : Measure X) (n : ℕ) :
    Measure (Fin n → X) :=
  Measure.pi (fun _ : Fin n => ν)

/-- `E[ALG]` under `n` i.i.d. arrivals with law `ν`. -/
noncomputable def expALG {A X : Type} [DecidableEq A] [MeasurableSpace X] (ν : Measure X)
    (lst : X → List A) (n : ℕ) : ℝ :=
  ∫ ω, (ALG lst ω : ℝ) ∂(arrivalLaw ν n)

/-- `E[OPT]` under `n` i.i.d. arrivals with law `ν`. -/
noncomputable def expOPT {A I X : Type} [Fintype A] [MeasurableSpace X] (ν : Measure X)
    (E : Finset (A × I)) (typ : X → I) (n : ℕ) : ℝ :=
  ∫ ω, (OPT E typ ω : ℝ) ∂(arrivalLaw ν n)

end RandomListsMatching.Concentration


