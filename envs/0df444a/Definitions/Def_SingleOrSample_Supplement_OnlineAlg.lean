-- Prove2me | Definitions.Def_SingleOrSample_Supplement_OnlineAlg
-- name    : SingleOrSample_Supplement_OnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:31:35.234261+00:00
-- url     : https://prove2.me/theorems/9e0ba90f-b468-476a-a2d7-2aa47c7a98c0
-- title:
--   Randomized and deterministic online allocation algorithms, their run and the $\alpha$-MMS success event
-- statement:
--   Agents $1,\dots,n$ arrive one at a time; when agent $i$ arrives her valuation $v_i$ is revealed, and the algorithm must irrevocably allocate her a set of goods still available. A **randomized online allocation algorithm** is given, at each arrival, by a probability law on bundles that may depend on the valuations $v_1,\dots,v_i$ revealed so far and on the bundles $A_1,\dots,A_{i-1}$ already allocated. A **deterministic** algorithm chooses the bundle as a function of the same data.
--
--   For a fixed profile $(v_1,\dots,v_n)$, chosen before the algorithm's coins (an **oblivious adversary**), the **run** is the law of $(A_1,\dots,A_n)$; the bundle named by the algorithm is intersected with the goods still available, and goods may remain unallocated. The bundles form an **$\alpha$-MMS allocation** if
--   $$
--   v_i(A_i)\ \ge\ \alpha\cdot\mathrm{MMS}_i\qquad\text{for every agent }i,
--   $$
--   where $\mathrm{MMS}_i$ is the maximin share of $v_i$ over all partitions of the $m$ goods into $n$ bundles. When the profile is itself drawn from a distribution $\mathcal D$ before the run, the **success probability** is the probability of this event under the joint law. An algorithm is $(\alpha,\beta)$-competitive if its success probability is at least $\beta$ on every instance.
--
--   **Formalization Note** Randomized algorithms are behavioural: a fresh law at every arrival. Internal randomness not visible in the earlier bundles can be resampled conditionally later, so this captures every randomized algorithm (Kuhn's theorem, perfect recall). The algorithm knows $n$ and $m$ because it is quantified after them. Lean indexes agents from $0$.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §2.1, p.6 (online MMS, oblivious adversary, Definitions 1 and 2); App. C, p.34 (deterministic algorithms, Yao)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace SingleOrSample.Supplement

/-- A **randomized online allocation algorithm** on `m` goods (Chawla, Huang, Kulkarni, Mehta, Shahkar,
Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission,
arXiv:2609.32286, manuscript sha256 28cd3d7b…, §2.1, p.6): when an agent arrives, `act vals bs` is the
law of the bundle it allocates to her, given the valuations `vals = [v_1, …, v_i]` revealed so far (hers
last) and the bundles `bs = [A_1, …, A_{i−1}]` allocated to the earlier agents.

**Formalization Note.** The algorithm is behavioural: a fresh law at every arrival, which may depend on
everything the algorithm has seen. It knows `n` and `m` because it is quantified after them. Any internal
randomness that is not visible in the earlier bundles can be resampled conditionally at a later
arrival, so behavioural algorithms induce every law of bundle sequences that a general randomized
algorithm does (Kuhn's theorem, perfect recall). The algorithm never sees the coins of the future or
the valuations of later agents. -/
structure OnlineAlg (m : ℕ) where
  act : List (Finset (Fin m) → ℝ) → List (Finset (Fin m)) → PMF (Finset (Fin m))

/-- A **deterministic** online allocation algorithm (App. C, p.34): the bundle is a function of the
valuations revealed so far and the earlier bundles. -/
def DetOnlineAlg (m : ℕ) : Type :=
  List (Finset (Fin m) → ℝ) → List (Finset (Fin m)) → Finset (Fin m)

/-- A deterministic algorithm as a randomized one, with point-mass laws. -/
noncomputable def DetOnlineAlg.toAlg {m : ℕ} (A : DetOnlineAlg m) : OnlineAlg m :=
  ⟨fun vals bs => PMF.pure (A vals bs)⟩

/-- The goods allocated in a list of bundles. -/
def allocated {m : ℕ} (bs : List (Finset (Fin m))) : Finset (Fin m) :=
  bs.foldr (· ∪ ·) ∅

/-- The law of the bundles `[A_1, …, A_j]` after the first `j` arrivals, when the algorithm `A` runs on
the valuation profile `vs` of `n` agents (p.6: agent `i` arrives at time `i`, her valuation is revealed,
and the algorithm "must irrevocably allocate a subset of goods to the agent from the available set of
goods"). For `j ≥ n` nothing changes.

**Formalization Note.** The bundle named by the algorithm is intersected with the goods still
available (`B \ allocated bs`); an algorithm that only names available goods is unchanged, and every
other algorithm is replaced by one that is. Goods may stay unallocated. Lean's agent index (from `0`)
is the page's `i + 1`. The profile `vs` is fixed before any coin (oblivious adversary, p.6). -/
noncomputable def OnlineAlg.runLaw {m n : ℕ} (A : OnlineAlg m) (vs : Fin n → Finset (Fin m) → ℝ) :
    ℕ → PMF (List (Finset (Fin m)))
  | 0 => PMF.pure []
  | j + 1 => (A.runLaw vs j).bind fun bs =>
      if j < n then
        (A.act ((List.ofFn vs).take (j + 1)) bs).map fun B => bs ++ [B \ allocated bs]
      else PMF.pure bs

/-- The bundle of the agent with index `i` in a list of bundles (`∅` if absent). -/
def bundleOf {m n : ℕ} (bs : List (Finset (Fin m))) (i : Fin n) : Finset (Fin m) :=
  bs.getD i ∅

/-- The bundles `bs` form an **α-MMS allocation** for the profile `vs` (Definition 1, p.6):
`v_i(A_i) ≥ α · MMS_i` for every agent `i`, with `MMS_i` the maximin share of `v_i` over partitions of
all `m` goods into `n` bundles. -/
def IsAlphaMMS {m n : ℕ} (α : ℝ) (vs : Fin n → Finset (Fin m) → ℝ) (bs : List (Finset (Fin m))) :
    Prop :=
  ∀ i : Fin n, α * LittleCharity.MMS.mms (vs i) n Finset.univ ≤ vs i (bundleOf bs i)

/-- The probability that the algorithm `A` produces an α-MMS allocation when the profile is drawn from
`D` before the algorithm's first coin (Definition 2, p.6; App. C, p.34). For a point mass `D` this is
the success probability on one instance. -/
noncomputable def successProb {m n : ℕ} (A : OnlineAlg m) (α : ℝ)
    (D : PMF (Fin n → Finset (Fin m) → ℝ)) : ENNReal :=
  (D.bind fun vs => (A.runLaw vs n).map fun bs => (vs, bs)).toOuterMeasure
    {p | IsAlphaMMS α p.1 p.2}

end SingleOrSample.Supplement


