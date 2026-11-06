-- Prove2me | Definitions.Def_HMajConsensus_majLaw
-- name    : HMajConsensus_majLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:57.106209+00:00
-- url     : https://prove2.me/theorems/ec476b82-4079-4127-adb5-51563eddb3e0
-- title:
--   Multinomial samples, the mode set and the law of $\mathrm{Maj}(X)$, $X\sim\mathrm{Multinomial}(h;p)$
-- statement:
--   Let $k\ge1$ be the number of opinions and let $p=(p_1,\dots,p_k)$ be a probability vector on $[k]$. Draw $h$ independent samples from $p$; the **count vector** $X=(X_1,\dots,X_k)$ records how often each opinion occurs, so $X\sim\mathrm{Multinomial}(h;p)$. The **mode set** of a count vector $x$ is
--   $$M(x)=\{j\in[k]: x_j=\|x\|_\infty\},$$
--   the opinions of highest frequency. $\mathrm{Maj}(X)$ is an element of $M(X)$ chosen uniformly at random. The module defines:
--
--   1. the law of the ordered sample, the product $p^{\otimes h}$;
--   2. the count map $s\mapsto X(s)$ and $\mathrm{Multinomial}(h;p)$ as its image law;
--   3. $M(x)$ and the uniform law on $M(x)$ (tie-breaking);
--   4. the law of $\mathrm{Maj}(X)$, and the **winner probabilities** $q^{(h)}_i(p)=\Pr[W_i]=\Pr[\mathrm{Maj}(X)=i]$, collected in the vector $q^{(h)}(p)$;
--   5. the vector $(p_1,\dots,p_k)$ of a probability vector, for comparisons with $q^{(h)}(p)$.
--
--   These objects describe one node's update in one round of $h$-Majority: its new opinion has law $\mathrm{Maj}(X)$ with $p$ the current opinion distribution. Sampling, counting and tie-breaking come from a single sample law, so the multinomial distribution and the winner probabilities cannot drift apart.
--
--   **Formalization Note** Opinions are `Fin k` (labels $0,\dots,k-1$) and a probability vector is a `PMF (Fin k)`. The uniform law on $M(x)$ is $|M(x)|^{-1}\sum_{j\in M(x)}\delta_j$; $M(x)$ is nonempty for $k\ge1$, and the module proves that the law of $\mathrm{Maj}(X)$ is a probability measure. For $h=1$ the law of $\mathrm{Maj}(X)$ is $p$ itself (the Voter rule).
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, §2, p.4 (multinomial distribution, Maj, uniform tie-breaking); §5, p.14 (W_i, q_i); §5.1.1, p.15 (M(x)); §5.2, p.24 (q^(r)_i(p), q^(r)(p))

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HMajConsensus

/-- `h` independent samples from a probability vector `p` on the opinions `[k]`
(d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus
Dynamics*, arXiv:2610.40562, §2, p.4: "consider h independent samples from p").

**Formalization Note** Opinions `[k] = {1, …, k}` are `Fin k` (labels `0, …, k-1`); a probability
vector `p ∈ [0,1]^k` with `|p| = 1` is a `PMF (Fin k)`. The law of the ordered sample
`(s₁, …, s_h)` is the product measure `p^{⊗h}` on `Fin h → Fin k`. -/
noncomputable def iidSample {k : ℕ} (h : ℕ) (p : PMF (Fin k)) : Measure (Fin h → Fin k) :=
  Measure.pi (fun _ : Fin h => p.toMeasure)

/-- The count vector `X = (X₁, …, X_k)` of a sample: `X_i` is the number of occurrences of
opinion `i` in the sample (arXiv:2610.40562, §2, p.4). -/
def counts {k h : ℕ} (s : Fin h → Fin k) : Fin k → ℕ :=
  fun i => (Finset.univ.filter (fun j => s j = i)).card

/-- `Multinomial(h; p)`: the law of the count vector of `h` independent samples from `p`
(arXiv:2610.40562, §2, p.4, and its pmf (1)).

**Formalization Note** It is the push-forward of `iidSample h p` by `counts`, a measure on
`Fin k → ℕ` (every subset of the finite sample space is measurable, so `counts` is measurable). -/
noncomputable def multinomial {k : ℕ} (h : ℕ) (p : PMF (Fin k)) : Measure (Fin k → ℕ) :=
  (iidSample h p).map counts

/-- The mode set `M(x) = {j ∈ [k] : x_j = ‖x‖_∞}` of a count vector (arXiv:2610.40562, §5.1.1,
p.15): the opinions of highest frequency. -/
def modes {k : ℕ} (x : Fin k → ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun j => ∀ i, x i ≤ x j)

/-- Uniform tie-breaking among the modes: the law of `Maj(x)` for a fixed count vector `x`, i.e.
the uniform distribution on `M(x)` (arXiv:2610.40562, §2, p.4: "an index attaining the largest
coordinate of X(u), chosen uniformly in case of a tie").

**Formalization Note** Written as `|M(x)|⁻¹ ∑_{j ∈ M(x)} δ_j`; `M(x)` is nonempty whenever
`k ≥ 1`, so this is a probability measure (`tieBreak_isProbabilityMeasure`). -/
noncomputable def tieBreak {k : ℕ} (x : Fin k → ℕ) : Measure (Fin k) :=
  ((modes x).card : ℝ≥0∞)⁻¹ • ∑ j ∈ modes x, Measure.dirac j

lemma modes_nonempty {k : ℕ} [Nonempty (Fin k)] (x : Fin k → ℕ) : (modes x).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  exact ⟨j, by simpa [modes] using fun i => hj i (Finset.mem_univ i)⟩

instance tieBreak_isProbabilityMeasure {k : ℕ} [Nonempty (Fin k)] (x : Fin k → ℕ) :
    IsProbabilityMeasure (tieBreak x) := by
  constructor
  have hne : ((modes x).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (modes_nonempty x)).ne'
  simp only [tieBreak, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    measure_univ, Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hne (by simp)

/-- The tie-breaking kernel from ordered samples to opinions: `s ↦ Law(Maj(counts s))`. -/
noncomputable def majKernel (k h : ℕ) : Kernel (Fin h → Fin k) (Fin k) :=
  Kernel.ofFunOfCountable (fun s => tieBreak (counts s))

instance majKernel_isMarkovKernel (k h : ℕ) [Nonempty (Fin k)] :
    IsMarkovKernel (majKernel k h) :=
  ⟨fun s => by
    change IsProbabilityMeasure (tieBreak (counts s))
    infer_instance⟩

/-- The law of `Maj(X)` for `X ∼ Multinomial(h; p)`, with uniform tie-breaking
(arXiv:2610.40562, §2, p.4 and §5, p.14: the winning opinion of one node's update).

**Formalization Note** Sampling, counting and tie-breaking come from one primitive: draw the
ordered sample from `iidSample h p`, then draw `Maj` uniformly from the modes of its count
vector. For `h = 1` this is `p` itself (Voter, "1-majority", p.25). -/
noncomputable def majLaw {k : ℕ} (h : ℕ) (p : PMF (Fin k)) : Measure (Fin k) :=
  majKernel k h ∘ₘ iidSample h p

instance majLaw_isProbabilityMeasure {k : ℕ} (h : ℕ) (p : PMF (Fin k)) :
    IsProbabilityMeasure (majLaw h p) := by
  have : Nonempty (Fin k) := ⟨p.support_nonempty.some⟩
  unfold majLaw iidSample
  infer_instance

/-- The winner probability `q^{(h)}_i(p) = Pr[W_i] = Pr[Maj(X) = i]`, `X ∼ Multinomial(h; p)`
(arXiv:2610.40562, §5, p.14 and §5.2, p.24). -/
noncomputable def winProb {k : ℕ} (h : ℕ) (p : PMF (Fin k)) (i : Fin k) : ℝ :=
  (majLaw h p {i}).toReal

/-- The winner distribution `q^{(h)}(p) = (q^{(h)}_i(p))_{i ∈ [k]}` as a real vector
(arXiv:2610.40562, §5.2, p.24). -/
noncomputable def winVec {k : ℕ} (h : ℕ) (p : PMF (Fin k)) : Fin k → ℝ :=
  fun i => winProb h p i

/-- A probability vector `p` as a real vector `(p_1, …, p_k)`. -/
noncomputable def probVec {k : ℕ} (p : PMF (Fin k)) : Fin k → ℝ :=
  fun i => (p i).toReal

end HMajConsensus


