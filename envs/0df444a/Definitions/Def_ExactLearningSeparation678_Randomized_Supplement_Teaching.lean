-- Prove2me | Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching
-- name    : ExactLearningSeparation678_Randomized_Supplement_Teaching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:31.701672+00:00
-- url     : https://prove2.me/theorems/5b695191-0fea-4add-b414-d1b620d784ff
-- title:
--   Extended teaching dimension, fractional splitting $f\gamma$ and fractional extended teaching dimension
-- statement:
--   Let $C\subseteq\{0,1\}^N$ be a concept class and, for a distribution $\mu$ on $C$, write $\mu(C_{i,b})$ for the mass of the concepts $c$ with $c_i=b$.
--
--   1. **Extended teaching dimension.** For any $h\in\{0,1\}^N$ (in $C$ or not), a set $S\subseteq[N]$ is specifying if at most one concept of $C$ agrees with $h$ on all of $S$, and
--   $$\mathrm{ETD}(C,h)=\min\{|S|: S\text{ specifying for }h\},\qquad \mathrm{ETD}(C)=\max_{h\in\{0,1\}^N}\mathrm{ETD}(C,h).$$
--   2. **Fractional splitting parameter (Definition 4.5).**
--   $$f\gamma(C)=\min_{\substack{\mu\text{ distribution on }C\\ \max_c\mu(c)\le1/2}}\ \max_{i\in[N]}\min\{\mu(C_{i,0}),\mu(C_{i,1})\}.$$
--   3. **Fractional extended teaching dimension (Definition 4.7).**
--   $$\mathrm{fETD}(C,h)=\min_{\substack{c^*\in C\\ w_1,\dots,w_N\ge0}}\Big\{\sum_{i=1}^N w_i:\ \sum_{i:c_i\ne h_i}w_i\ge1\text{ for every }c\in C\setminus\{c^*\}\Big\},\qquad \mathrm{fETD}(C)=\max_{h\in\{0,1\}^N}\mathrm{fETD}(C,h).$$
--
--   The splitting parameter $\gamma(C)$ is the mission's published one. These are the fractional relaxations of $\gamma$ and $\mathrm{ETD}$ compared in Theorem 4.10 and used in the query bounds of Theorems 4.11, 4.12 and 1.6.
--
--   **Formalization Note** Distributions are real mass functions on the members of $C$. The minima are written as real infima over the feasible sets. For $f\gamma$ on $|C|\ge2$, the feasible capped simplex is nonempty and compact and the objective continuous. For $\mathrm{fETD}$ on nonempty $C$, feasible weights can be clipped to $[0,1]$ without increasing cost or violating a constraint; a minimum exists on a finite union of compact cubes. Thus these infima are attained source minima. Where the source assigns no value ($|C|\le1$ for $f\gamma$, $C=\emptyset$ for $\mathrm{fETD}$, because no feasible point exists) the value is $0$. The maxima over $h$ range over all of $\{0,1\}^N$.
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), §4.2.1, p.31 (ETD, Eq. (22)); Definition 4.5, p.31; Definition 4.7, p.31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Learning

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

/-- p.31: `ETD(C, h)`, the least size of a coordinate set `S` on which at most one concept of
`C` agrees with `h` (a specifying set; zero agreeing concepts also qualify). The set is nonempty
(`S` = all coordinates). -/
noncomputable def etdAt {ι : Type*} [Fintype ι] (C : Finset (ι → Bool)) (h : ι → Bool) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset ι, S.card = k ∧ (C.filter fun c => ∀ i ∈ S, c i = h i).card ≤ 1}

/-- p.31: `ETD(C) = max_{h ∈ {0,1}^N} ETD(C, h)`, over every ambient `h`, in `C` or not. -/
noncomputable def etd {ι : Type*} [Fintype ι] (C : Finset (ι → Bool)) : ℕ :=
  (Finset.univ : Finset (ι → Bool)).sup fun h => etdAt C h

/-- Definition 4.5, p.31: the probability distributions `µ` on `C` (real masses on the members
of `C`, nonnegative, summing to `1`) with every atom `µ(c) ≤ 1/2`. -/
def IsCappedDist {ι : Type*} (C : Finset (ι → Bool)) (μ : {c // c ∈ C} → ℝ) : Prop :=
  QAlgorithms.Learning.IsDistribution μ ∧ ∀ c, μ c ≤ 1 / 2

/-- p.31: `µ(C_{i,b})`, the mass of the concepts `c ∈ C` with `c_i = b`. -/
noncomputable def massAt {ι : Type*} {C : Finset (ι → Bool)} (μ : {c // c ∈ C} → ℝ) (i : ι)
    (b : Bool) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : {c // c ∈ C} => c.1 i = b), μ c

/-- Definition 4.5, p.31: the objective `max_{i ∈ [N]} min{µ(C_{i,0}), µ(C_{i,1})}`. -/
noncomputable def splitObjective {ι : Type*} [Fintype ι] {C : Finset (ι → Bool)}
    (μ : {c // c ∈ C} → ℝ) : ℝ :=
  ⨆ i : ι, min (massAt μ i false) (massAt μ i true)

/-- Definition 4.5, p.31: the fractional splitting parameter
`fγ(C) = min_µ max_i min{µ(C_{i,0}), µ(C_{i,1})}` over all distributions `µ` on `C` with
`max_c µ(c) ≤ 1/2`. For `|C| ≥ 2` the feasible set is nonempty and the objective is bounded below
by `0`, so this infimum is the source's value (attainment is a fact about the compact feasible
set). Reading for `|C| ≤ 1`, where no distribution is feasible and the source assigns no value:
the empty infimum is `0`. -/
noncomputable def fGamma {ι : Type*} [Fintype ι] (C : Finset (ι → Bool)) : ℝ :=
  ⨅ μ : {μ : {c // c ∈ C} → ℝ // IsCappedDist C μ}, splitObjective μ.1

/-- Definition 4.7, p.31: the feasible pairs `(c*, w)` for `fETD(C, h)`: `c* ∈ C`, real weights
`w_i ≥ 0`, and `∑_{i : c_i ≠ h_i} w_i ≥ 1` for every `c ∈ C ∖ {c*}`. -/
def IsFetdFeasible {ι : Type*} [Fintype ι] (C : Finset (ι → Bool)) (h : ι → Bool)
    (p : (ι → Bool) × (ι → ℝ)) : Prop :=
  p.1 ∈ C ∧ (∀ i, 0 ≤ p.2 i) ∧
    ∀ c ∈ C, c ≠ p.1 → 1 ≤ ∑ i ∈ Finset.univ.filter (fun i => c i ≠ h i), p.2 i

/-- Definition 4.7, p.31: `fETD(C, h) = min_{c* ∈ C, w ≥ 0} ∑_i w_i` subject to the constraints
of `IsFetdFeasible`, minimizing jointly over the exempt concept and the weights. For nonempty
`C` the feasible set is nonempty and the objective is bounded below by `0`, so this infimum is
the source's minimum (an attained linear-program optimum). Reading for `C = ∅`, where no `c*`
exists: the empty infimum is `0`. -/
noncomputable def fetdAt {ι : Type*} [Fintype ι] (C : Finset (ι → Bool)) (h : ι → Bool) : ℝ :=
  ⨅ p : {p : (ι → Bool) × (ι → ℝ) // IsFetdFeasible C h p}, ∑ i, p.1.2 i

/-- Definition 4.7, p.31: `fETD(C) = max_{h ∈ {0,1}^N} fETD(C, h)`, a maximum over the finite set
of all ambient `h`. -/
noncomputable def fetd {ι : Type*} [Fintype ι] (C : Finset (ι → Bool)) : ℝ :=
  ⨆ h : ι → Bool, fetdAt C h

/-! ### Sanity checks -/

example {ι : Type*} [Fintype ι] (h : ι → Bool) : etdAt (∅ : Finset (ι → Bool)) h = 0 :=
  Nat.sInf_eq_zero.2 (Or.inl ⟨∅, rfl, by simp⟩)

example {ι : Type*} [Fintype ι] : fGamma (∅ : Finset (ι → Bool)) = 0 := by
  have : IsEmpty {μ : {c // c ∈ (∅ : Finset (ι → Bool))} → ℝ // IsCappedDist ∅ μ} :=
    ⟨fun μ => by simpa [QAlgorithms.Learning.IsDistribution] using μ.2.1.2⟩
  simp [fGamma]

end ExactLearningSeparation678.Randomized.Supplement


