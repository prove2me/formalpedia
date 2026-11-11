-- Prove2me | Definitions.Def_MemoSDPI_Main_Selection
-- name    : MemoSDPI_Main_Selection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:41:54.420203+00:00
-- url     : https://prove2.me/theorems/16021fcf-916d-4cf4-957b-34e16e5491b2
-- title:
--   k-subsets of [m], the k-th largest coordinate θ_(k), (m, k)-selection accuracy (4.1), and uniform permutations
-- statement:
--   For $\theta \in [0,1]^m$, $\theta_{(k)}$ denotes its **$k$-th largest coordinate**, counted with multiplicity. An algorithm solves the **$(m,k)$-selection** (top-$k$ selection) problem with accuracy $\alpha$ and failure probability $\beta$ on a family of distributions if it returns a set $T \subseteq [m]$ of size $k$ and, for every distribution in the family with mean $\theta$,
--   $$
--   \Pr\Big[\min_{j \in T} \theta_j \;\ge\; \theta_{(k)} - \alpha\Big] \;\ge\; 1 - \beta, \tag{4.1}
--   $$
--   the probability being over the sample and the randomness of the algorithm. Here the family is that of all product Bernoulli distributions on $\{0,1\}^m$, each record being a full vector of $m$ observations.
--
--   For Lemma 4.1 the module also defines the uniform distribution on permutations $\pi$ of $[m]$ and the set $\{\pi(1), \dots, \pi(t)\}$ of the first $t$ places.
--
--   **Formalization Note** $[m]$ is `Fin m` and places are $0$-based, so $\{\pi(1),\dots,\pi(t)\}$ is $\{\pi(i) : i < t\}$. Outputs live in the type `KSubset m k` of $k$-element subsets (discrete $\sigma$-algebra), so an algorithm returns a $k$-set on every sample and seed. $\theta_{(k)}$ is $\sup\{c : |\{i : c \le x_i\}| \ge k\}$; for $1 \le k \le m$ the supremum is attained and equals the $k$-th entry of the non-increasing rearrangement (ties counted). "$\min_{j\in T}\theta_j \ge \theta_{(k)}-\alpha$" is written "$\theta_j \ge \theta_{(k)} - \alpha$ for every $j \in T$" ($T$ nonempty when $k \ge 1$). The algorithm is the published `DPVerify.RandAlg`: a seed $\omega$ drawn from a probability space $(\Omega, P)$ and a jointly measurable output map $(S, \omega) \mapsto A(S;\omega)$. `SolvesSelection A α β` requires (4.1) for **every** $\theta \in [0,1]^m$, with probability under the product of the sample law $(\mathrm{Ber}(\theta_1)\otimes\cdots\otimes\mathrm{Ber}(\theta_m))^{n}$ and the seed law. Permutations carry the discrete $\sigma$-algebra.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 15, §4, eq. (4.1) and Lemma 4.1

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_MemoSDPI_Main_ProductBernoulli

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- **`k`-element subsets of `[m]`**, the outputs of a top-`k` selection algorithm (Feldman, Lyu,
Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data
Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 15, §4).

**Formalization Note.** `[m]` is `Fin m`; the type carries the discrete σ-algebra. -/
def KSubset (m k : ℕ) : Type := {T : Finset (Fin m) // T.card = k}

/-- Every set of `k`-subsets is measurable. -/
instance KSubset.measurableSpace (m k : ℕ) : MeasurableSpace (KSubset m k) := ⊤

/-- The underlying finite set of a `k`-subset. -/
def KSubset.toFinset {m k : ℕ} (T : KSubset m k) : Finset (Fin m) := T.1

/-- **The `k`-th largest coordinate** `θ_(k)` of `x ∈ ℝ^m` (p. 15, §4), counted with
multiplicity: the largest `c` such that at least `k` coordinates are `≥ c`.

**Formalization Note.** For `1 ≤ k ≤ m` the set below is nonempty and bounded above and its
supremum is attained; it equals the `k`-th entry of the non-increasing rearrangement of `x`
(and `max` over `k`-subsets `T'` of `min_{j∈T'} x_j`). Outside `1 ≤ k ≤ m` the value is Lean's
junk `sSup` and is never used: the theorems assume `1 ≤ k ≤ m`. -/
noncomputable def kthLargest {m : ℕ} (x : Fin m → ℝ) (k : ℕ) : ℝ :=
  sSup {c : ℝ | k ≤ (Finset.univ.filter fun i => c ≤ x i).card}

/-- **Selection success** (p. 15, eq. (4.1)): the output set `T` satisfies
`min_{j∈T} θ_j ≥ θ_(k) − α`, written as `θ_j ≥ θ_(k) − α` for every `j ∈ T`. -/
def selectionSuccess {m k : ℕ} (θ : Fin m → unitInterval) (α : ℝ) (T : KSubset m k) : Prop :=
  ∀ j ∈ T.toFinset, kthLargest (fun i => (θ i : ℝ)) k - α ≤ (θ j : ℝ)

/-- **`(m, k)`-selection with accuracy `α` and failure probability `β` on every product Bernoulli
distribution** (p. 15, eq. (4.1)): for every `θ ∈ [0, 1]^m`,
`Pr[min_{j∈A(S)} θ_j ≥ θ_(k) − α] ≥ 1 − β`, the probability being over the sample
`S ∼ (Ber(θ_1) ⊗ ⋯ ⊗ Ber(θ_m))^n` and the seed of `A`.

**Formalization Note.** `A` is the published `DPVerify.RandAlg` on samples of length `n` over
`{0,1}^m = Fin m → Bool` with output type `KSubset m k`, so it returns a `k`-subset on every sample
and seed. The probability is the measure `S ∼ P_θ^n ⊗ ω ∼ A.P` of the success set, in `ℝ≥0∞`. -/
def SolvesSelection {m k n : ℕ} (A : DPVerify.RandAlg (Fin m → Bool) (KSubset m k) n)
    (α β : ℝ) : Prop :=
  ∀ θ : Fin m → unitInterval,
    ENNReal.ofReal (1 - β) ≤
      ((Measure.pi fun _ : Fin n => prodBernoulli θ).prod A.P)
        {q | selectionSuccess θ α (A.run q.1 q.2)}

/-- Every set of permutations of `[m]` is measurable. -/
instance permFin_measurableSpace (m : ℕ) : MeasurableSpace (Equiv.Perm (Fin m)) := ⊤

/-- **Uniformly random permutation of `[m]`** (p. 15, Lemma 4.1). -/
noncomputable def uniformPerm (m : ℕ) : Measure (Equiv.Perm (Fin m)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin m))).toMeasure

/-- **The first `t` places of a permutation**: `{π(1), …, π(t)}` (p. 15, Lemma 4.1).

**Formalization Note.** Places are `0`-based: `{π(i) : i < t}` in `Fin m`. -/
def firstPlaces {m : ℕ} (π : Equiv.Perm (Fin m)) (t : ℕ) : Finset (Fin m) :=
  (Finset.univ.filter fun i : Fin m => i.val < t).image π

end MemoSDPI.Main


