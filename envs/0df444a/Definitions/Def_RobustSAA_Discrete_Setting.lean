-- Prove2me | Definitions.Def_RobustSAA_Discrete_Setting
-- name    : RobustSAA_Discrete_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:03.743322+00:00
-- url     : https://prove2.me/theorems/56569f92-f817-4115-bed9-705ccbeb5b7f
-- title:
--   Finite-support data, Pearson and G confidence regions, and uniform consistency
-- statement:
--   Let the known finite support have $n$ labelled points. A distribution $F$ assigns probability $p_F(j)$ to label $j$, and a sample $s=(s_1,\ldots,s_N)$ has empirical frequency $\widehat p_N(j)=N^{-1}\#\{i:s_i=j\}$. The data law is the independent infinite product of $F$, and the sample of size $N$ is its first $N$ coordinates.
--
--   For a hypothetical law $F_0$, the Pearson statistic and squared G statistic are
--
--   $$
--   X_N(F_0)^2=\sum_j\frac{(p_{F_0}(j)-\widehat p_N(j))^2}{p_{F_0}(j)},\qquad
--   G_N(F_0)^2=2\sum_j\widehat p_N(j)\log\frac{\widehat p_N(j)}{p_{F_0}(j)}.
--   $$
--
--   Each confidence region consists of the laws whose statistic is at most $\sqrt{Q/N}$, for a fixed nonnegative $Q$. Total variation is $d_{\mathrm{TV}}(q,q')=\frac12\sum_j|q(j)-q'(j)|$. A region map is **uniformly consistent** if, for every generating law $F$, almost surely every sequence $F_N$ that fails to converge weakly to $F$ is rejected infinitely often.
--
--   These definitions fix the objects used by Theorem 4 and its four proof milestones.
--
--   **Formalization Note** The labelled points are `Fin n`; their Euclidean coordinates play no role in these tests. At $N=0$, the empirical frequency is zero and the regions follow Lean's total arithmetic, but all asymptotic statements concern positive $N$. A positive numerator divided by a zero hypothetical probability contributes $+\infty$ to $X_N^2$; in the G statistic, a positive empirical frequency against zero hypothetical probability contributes $+\infty$, while a zero empirical frequency contributes zero. The G region compares squared quantities. The parameter $Q$ is fixed across sample sizes and includes the paper's chi-square quantile.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §2 (7) p. 7, §3.1 p. 8, Definition 3 p. 13, §10.6 p. 38

import Mathlib

namespace RobustSAA.Discrete

open Filter MeasureTheory
open scoped BigOperators

noncomputable def pvec {n : ℕ} (F : ProbabilityMeasure (Fin n)) (j : Fin n) : ℝ :=
  (F : Measure (Fin n)).real {j}

noncomputable def phat {n N : ℕ} (s : Fin N → Fin n) (j : Fin n) : ℝ :=
  ((Finset.univ.filter (fun i => s i = j)).card : ℝ) / N

noncomputable def empiricalDist {n N : ℕ} (hN : 0 < N) (s : Fin N → Fin n) :
    ProbabilityMeasure (Fin n) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact ⟨((PMF.uniformOfFintype (Fin N)).map s).toMeasure, inferInstance⟩

noncomputable def dataLaw {n : ℕ} (F : ProbabilityMeasure (Fin n)) :
    Measure (ℕ → Fin n) :=
  Measure.infinitePi (fun _ : ℕ => (F : Measure (Fin n)))

def sample {n : ℕ} (ω : ℕ → Fin n) (N : ℕ) : Fin N → Fin n :=
  fun i => ω i

noncomputable def chiStat {n N : ℕ} (F₀ : ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) : ENNReal :=
  (∑ j : Fin n,
    ENNReal.ofReal ((pvec F₀ j - phat s j) ^ 2) / ENNReal.ofReal (pvec F₀ j)) ^ (1 / 2 : ℝ)

noncomputable def gTerm {n N : ℕ} (F₀ : ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) (j : Fin n) : EReal :=
  if phat s j = 0 then 0
  else if pvec F₀ j = 0 then ⊤
  else ((phat s j * Real.log (phat s j / pvec F₀ j) : ℝ) : EReal)

noncomputable def gStatSq {n N : ℕ} (F₀ : ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) : EReal :=
  2 * ∑ j : Fin n, gTerm F₀ s j

noncomputable def chiRegion {n : ℕ} (Q : ℝ) (N : ℕ) (s : Fin N → Fin n) :
    Set (ProbabilityMeasure (Fin n)) :=
  {F₀ | chiStat F₀ s ≤ ENNReal.ofReal (Real.sqrt (Q / N))}

noncomputable def gRegion {n : ℕ} (Q : ℝ) (N : ℕ) (s : Fin N → Fin n) :
    Set (ProbabilityMeasure (Fin n)) :=
  {F₀ | gStatSq F₀ s ≤ ((Q / N : ℝ) : EReal)}

noncomputable def dTV {n : ℕ} (q q' : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin n, |q j - q' j|

def IsUniformlyConsistent {n : ℕ}
    (region : (N : ℕ) → (Fin N → Fin n) → Set (ProbabilityMeasure (Fin n))) : Prop :=
  ∀ F : ProbabilityMeasure (Fin n),
    ∀ᵐ ω ∂dataLaw F,
      ∀ G : ℕ → ProbabilityMeasure (Fin n),
        ¬ Tendsto G atTop (nhds F) →
          ∃ᶠ N in atTop, G N ∉ region N (sample ω N)

end RobustSAA.Discrete


