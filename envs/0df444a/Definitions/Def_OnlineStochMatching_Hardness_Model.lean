-- Prove2me | Definitions.Def_OnlineStochMatching_Hardness_Model
-- name    : OnlineStochMatching_Hardness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:46:30.050016+00:00
-- url     : https://prove2.me/theorems/5dc434ce-ea79-4288-a126-27ed4b4dffd5
-- title:
--   Online bipartite matching with uniform i.i.d. arrivals: online algorithms, ALG, OPT and the expected approximation factor (Section 2)
-- statement:
--   This definition fixes the model of the **online stochastic matching problem** of Feldman, Mehta, Mirrokni and Muthukrishnan (§2) in the case where every impression type is expected once ($e_i = 1$), so that the arrival distribution is uniform.
--
--   A bipartite graph $G = (A, I, E)$ between a finite set $A$ of **advertisers** and a finite set $I$ of **impression types** is known in advance. Online, $n$ impressions arrive one at a time; their types $\omega(0), \dots, \omega(n-1)$ are independent and uniformly distributed on $I$. When arrival $t$ comes, the algorithm must immediately assign it to an advertiser $a$ with $(a, \omega(t)) \in E$ that has not been assigned before, or leave it unassigned; decisions are irrevocable.
--
--   1. A **deterministic online algorithm** is a rule that, at each arrival $t$, sees the types $\omega(0), \dots, \omega(t-1)$ of the earlier arrivals and the type $\omega(t)$ of the current one (but nothing about later arrivals), and proposes an advertiser or declines. The arrival is assigned to the proposed advertiser $a$ exactly when $(a, \omega(t)) \in E$ and $a$ is still free; otherwise it stays unassigned.
--   2. $\mathrm{ALG}(\omega)$ is the number of arrivals the algorithm assigns on the sequence $\omega$.
--   3. The **realization graph** $\hat G(\omega)$ has the advertisers on one side, one node per arrival on the other, and an edge between $a$ and arrival $t$ iff $(a, \omega(t)) \in E$. $\mathrm{OPT}(\omega)$ is the size of a maximum matching of $\hat G(\omega)$: the largest number of arrivals that can be assigned, with hindsight, to pairwise distinct adjacent advertisers.
--   4. The **expected approximation factor** of a deterministic algorithm is
--   $$\mathbb E_\omega\!\left[\frac{\mathrm{ALG}(\omega)}{\mathrm{OPT}(\omega)}\right] = \frac{1}{|I|^n}\sum_{\omega \in I^n} \frac{\mathrm{ALG}(\omega)}{\mathrm{OPT}(\omega)}.$$
--   5. A **randomized online algorithm** is a probability distribution $P$ on deterministic online algorithms; its expected approximation factor is $\sum_{\mathrm{alg}} P(\mathrm{alg})\, \mathbb E_\omega[\mathrm{ALG}/\mathrm{OPT}]$, the expectation over both the algorithm's coins and the arrivals.
--
--   These objects are what the hardness result of §3 (Theorem 3) quantifies over: it bounds the expected approximation factor of every randomized online algorithm on explicit instances.
--
--   **Formalization Note** Arrival sequences are functions `Fin n → I`; the algorithm at time `t` receives the prefix `Fin t → I` and the current type, so it cannot read the future. Proposing an advertiser that is not adjacent or already used is the same as declining, so the encoding covers every online algorithm, including those that skip an arrival while an adjacent advertiser is free. A randomized algorithm is a `PMF` on the finite type of deterministic ones (a mixed strategy); by Kuhn's theorem this is equivalent to flipping fresh coins at each step with perfect recall. The expectation over arrivals is the average over all $|I|^n$ sequences. Lean's division gives $x/0 = 0$; on the instances of this mission every impression type has an edge, so $\mathrm{OPT}(\omega) \ge 1$ whenever $n \ge 1$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, pp. 3–4, Section 2 (the model, the realization graph, the expected approximation factor)

import Mathlib

namespace OnlineStochMatching.Hardness

/-- A **deterministic online algorithm** for the online bipartite matching problem with
advertisers `A`, impression types `I` and `n` arrivals (Feldman–Mehta–Mirrokni–Muthukrishnan,
arXiv:0905.4100v1, §2, p. 3). At arrival `t` (`t = 0, …, n - 1`) it sees the types of the `t`
earlier arrivals (a function `Fin t → I`) and the type of the current arrival, and proposes an
advertiser (`some a`) or declines (`none`). It cannot see later arrivals. The graph and the
arrival law are fixed by the instance, so the algorithm knows them. Its own earlier decisions
are a function of the history it sees, so they are not a separate input. -/
def OnlineAlg (A I : Type) (n : ℕ) : Type :=
  (t : Fin n) → (Fin t → I) → I → Option A

instance instFintypeOnlineAlg (A I : Type) [Fintype A] [Fintype I] [DecidableEq I] (n : ℕ) :
    Fintype (OnlineAlg A I n) := by
  unfold OnlineAlg
  infer_instance

variable {A I : Type} {n : ℕ}

/-- The types of the arrivals strictly before arrival `t`: `prefixOf ω t j = ω j` for `j < t`. -/
def prefixOf (ω : Fin n → I) (t : Fin n) : Fin t → I :=
  fun j => ω (Fin.castLE (Nat.le_of_lt t.isLt) j)

variable [DecidableEq A]

/-- One step of the run: arrival `t` (of type `ω t`) is assigned to the advertiser `a` the
algorithm proposes iff `(a, ω t)` is an edge and `a` is not yet assigned; otherwise it is left
unassigned. `S` is the set of advertisers already assigned. -/
def step (G : A → I → Prop) [DecidableRel G] (alg : OnlineAlg A I n) (ω : Fin n → I)
    (t : Fin n) (S : Finset A) : Finset A :=
  match alg t (prefixOf ω t) (ω t) with
  | some a => if G a (ω t) ∧ a ∉ S then insert a S else S
  | none => S

/-- The set of advertisers assigned after the first `k` arrivals `0, …, k - 1` have been
processed (for `k ≥ n`, after all of them). -/
def matchedAfter (G : A → I → Prop) [DecidableRel G] (alg : OnlineAlg A I n)
    (ω : Fin n → I) : ℕ → Finset A
  | 0 => ∅
  | k + 1 =>
    if h : k < n then step G alg ω ⟨k, h⟩ (matchedAfter G alg ω k)
    else matchedAfter G alg ω k

/-- `ALG(ω)`: the number of arrivals the algorithm assigns on the arrival sequence `ω`. Every
assignment uses a fresh advertiser, so this is the number of assigned advertisers. -/
def ALG (G : A → I → Prop) [DecidableRel G] (alg : OnlineAlg A I n) (ω : Fin n → I) : ℕ :=
  (matchedAfter G alg ω n).card

/-- A matching of the realization graph `Ĝ(Î)` of the arrival sequence `ω` (§2, p. 4): a partial
map `M` from arrivals to advertisers that uses only edges (`M t = some a` implies
`(a, ω t) ∈ E`) and assigns each advertiser at most once. -/
def IsRealizationMatching (G : A → I → Prop) (ω : Fin n → I) (M : Fin n → Option A) : Prop :=
  (∀ t a, M t = some a → G a (ω t)) ∧ ∀ s t a, M s = some a → M t = some a → s = t

/-- The number of arrivals a partial map `M` assigns. -/
def matchingSize (M : Fin n → Option A) : ℕ :=
  (Finset.univ.filter fun t => (M t).isSome).card

open Classical in
/-- `OPT(ω)`: the size of a maximum matching of the realization graph of `ω`, i.e. the largest
number of arrivals that can be assigned, with hindsight, to pairwise distinct adjacent
advertisers. The empty map is always a realization matching, so the maximum is attained. -/
noncomputable def OPT [Fintype A] (G : A → I → Prop) (ω : Fin n → I) : ℕ :=
  ((Finset.univ : Finset (Fin n → Option A)).filter (IsRealizationMatching G ω)).sup
    matchingSize

/-- The **expected approximation factor** `E[ALG(Î)/OPT(Î)]` (§2, p. 4) of a deterministic online
algorithm when the `n` arrivals are i.i.d. uniform on `I` (the case `e_i = 1` of the model):
the average of `ALG(ω)/OPT(ω)` over all `|I|^n` arrival sequences `ω`. (Lean's `x / 0 = 0`
applies when `OPT(ω) = 0`; on the instances of this mission `OPT(ω) ≥ 1` for every `ω`.) -/
noncomputable def expectedRatio [Fintype A] [Fintype I] (G : A → I → Prop) [DecidableRel G]
    (alg : OnlineAlg A I n) : ℝ :=
  (∑ ω : Fin n → I, (ALG G alg ω : ℝ) / (OPT G ω : ℝ)) / (Fintype.card I : ℝ) ^ n

/-- The expected approximation factor of a **randomized online algorithm**, given as a probability
distribution `P` on deterministic online algorithms (a mixed strategy): the expectation over the
algorithm's randomness and over the uniform arrivals, `∑_alg P(alg) · E_ω[ALG/OPT]`. -/
noncomputable def randExpectedRatio [Fintype A] [Fintype I] [DecidableEq I]
    (G : A → I → Prop) [DecidableRel G] (P : PMF (OnlineAlg A I n)) : ℝ :=
  ∑ alg : OnlineAlg A I n, (P alg).toReal * expectedRatio G alg

end OnlineStochMatching.Hardness


