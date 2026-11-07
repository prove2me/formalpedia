-- Prove2me | Definitions.Def_PrettyGoodShadow_failureProb
-- name    : PrettyGoodShadow_failureProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:05.96943+00:00
-- url     : https://prove2.me/theorems/7cd4ecf4-1b61-40a1-b513-3e7aa3515f8d
-- title:
--   Boosting weights, priors $q_r$, odd median, failure probability, admissible parameters
-- statement:
--   The boosted algorithm starts from $w_0=p$. For $r=1,\dots,R$ it sets
--
--   $$
--   Z_{r-1}=\sum_x w_{r-1}(x),\qquad q_r=\frac{w_{r-1}}{Z_{r-1}},\qquad w_r(x)=w_{r-1}(x)\big(1+2e_{q_r}(x)\big).
--   $$
--
--   For odd $R$ it runs Algorithm 1 with prior $q_r$ on disjoint copies for each $r$ and outputs the coordinatewise median of $\hat o^{(1)},\dots,\hat o^{(R)}$. This module defines the weights, the priors, the median, and the failure probability
--
--   $$
--   \Pr\Big[\max_{i\in[m]}|\hat o_i-\operatorname{tr}(O_i\rho)|>\varepsilon\Big],
--   $$
--
--   over $x\sim p$ and the runs. It also defines the admissible parameters: $k\ge48/\varepsilon^2$, $T\ge1$, $2me^{-T/128}\le1/8$, $R$ odd and $m(\sqrt3/2)^R\le\delta$.
--
--   **Formalization Note** The priors are deterministic functions of the instance, since $e_q(x)$ is a number given by a formula. Rounds are indexed from $0$, so the source's $q_r$ is `prior (r-1)`. The median is the entry at position $\lfloor R/2\rfloor$ (from $0$) of the sorted values. The threshold $48/\varepsilon^2$ equals $12/(\varepsilon/2)^2$: the source's proof replaces $O$ by $(I+O)/2$ and $\varepsilon$ by $\varepsilon/2$ (§4.1, p.19).
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Appendix A, pp.31–32

import Mathlib
import Definitions.Def_PrettyGoodShadow_alg1Law

namespace PrettyGoodShadow

/-- **Boosting weights** `w_r` (arXiv:2610.06781, sha256 bd055b7d…, Appendix A, p.31): `w_0 = p` and
`w_r(x) = w_{r−1}(x) (1 + 2 e_{q_r}(x))`, with `q_r = w_{r−1} / Σ_y w_{r−1}(y)`.

**Formalization Note** The weights are deterministic functions of the instance: `e_q(x)` is a number given by
a formula, and no measurement outcome enters. The sum `Σ_y w_r(y)` is at least `Σ_y p_y = 1`, so the division
is by a positive number. -/
noncomputable def wt {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] {m : ℕ} (p : L → ℝ)
    (ρ : L → Matrix d d ℂ) (O : Fin m → Matrix d d ℂ) (ε : ℝ) (k T : ℕ) : ℕ → L → ℝ
  | 0 => p
  | r + 1 => fun x =>
      wt p ρ O ε k T r x *
        (1 + 2 * maxErr (fun y => wt p ρ O ε k T r y / ∑ z, wt p ρ O ε k T r z) ρ O k T ε x)

/-- **Boosted priors** (arXiv:2610.06781, sha256 bd055b7d…, Appendix A, p.31): `prior r` is the paper's
`q_{r+1}`, that is, `w_r / Z_r` with `Z_r = Σ_y w_r(y)`.

**Formalization Note** The paper indexes rounds by `r = 1, …, R`; here rounds are `r = 0, …, R − 1`, so the
paper's `q_r` is `prior (r − 1)`. -/
noncomputable def prior {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] {m : ℕ} (p : L → ℝ)
    (ρ : L → Matrix d d ℂ) (O : Fin m → Matrix d d ℂ) (ε : ℝ) (k T r : ℕ) : L → ℝ :=
  fun x => wt p ρ O ε k T r x / ∑ z, wt p ρ O ε k T r z

/-- **The median of an odd number of reals** (arXiv:2610.06781, sha256 bd055b7d…, Appendix A, p.31,
"coordinatewise median"): the entry at position `R / 2` (from `0`) of the values sorted increasingly.

**Formalization Note** For odd `R` this is an actual entry with `(R − 1)/2` entries on each side. The default
`0` of `getD` is never reached for `R ≥ 1`. -/
noncomputable def medianOdd {R : ℕ} (v : Fin R → ℝ) : ℝ :=
  ((List.ofFn v).insertionSort (· ≤ ·)).getD (R / 2) 0

/-- **Failure probability of the boosted algorithm** (arXiv:2610.06781, sha256 bd055b7d…, Appendix A,
pp.31–32): the probability over `x ∼ p` and over independent runs of Algorithm 1 with priors `q_1, …, q_R` that
the coordinatewise median of `ô^{(1)}, …, ô^{(R)}` misses some `tr(O_i ρ_x)` by more than `ε`:
`Pr[max_{i ∈ [m]} |ô_i − tr(O_i ρ)| > ε]`.

**Formalization Note** The runs use disjoint copies, so the joint law of the outcomes `y : Fin R → L` given `x`
is the product `∏_r alg1Law (prior r) ρ k T x (y r)`; `copy_accounting` states the single POVM realizing it. -/
noncomputable def failureProb {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] {m : ℕ}
    (p : L → ℝ) (ρ : L → Matrix d d ℂ) (O : Fin m → Matrix d d ℂ) (ε : ℝ) (k T R : ℕ) : ℝ :=
  ∑ x, p x * ∑ y : Fin R → L with
      (∃ i, ε < |medianOdd (fun r => obs (O i) (ρ (y r))) - obs (O i) (ρ x)|),
    ∏ r : Fin R, alg1Law (prior p ρ O ε k T r) ρ k T x (y r)

/-- **Admissible parameters of the boosted algorithm** (arXiv:2610.06781, sha256 bd055b7d…, Appendix A,
pp.31–32): `k ≥ 48/ε²`, `T ≥ 1`, `2 m e^{−T/128} ≤ 1/8`, `R` odd, and `m (√3/2)^R ≤ δ`.

**Formalization Note** The paper's proof fixes `T` by `2 m e^{−T/128} ≤ 1/8` (p.31) and takes `R` with
`m (√3/2)^R ≤ δ` (p.32). The value `48/ε²` is `12/(ε/2)²`: the proof of Lemma 4.3 assumes `0 ⪯ O ⪯ I` after
replacing `O` by `(I + O)/2` and `ε` by `ε/2` (§4.1, p.19). -/
def Admissible (m : ℕ) (ε δ : ℝ) (k T R : ℕ) : Prop :=
  48 / ε ^ 2 ≤ (k : ℝ) ∧ 1 ≤ T ∧ 2 * (m : ℝ) * Real.exp (-(T : ℝ) / 128) ≤ 1 / 8 ∧ Odd R ∧
    (m : ℝ) * (Real.sqrt 3 / 2) ^ R ≤ δ

end PrettyGoodShadow


