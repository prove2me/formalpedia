-- Prove2me | Definitions.Def_MinRankRecovery_RandomRIP_NearlyIsometric
-- name    : MinRankRecovery_RandomRIP_NearlyIsometric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:52.125823+00:00
-- url     : https://prove2.me/theorems/346c1c7b-fa33-4403-9059-cf6673edb611
-- title:
--   Definition 4.1 — nearly isometrically distributed random linear maps
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and let $\omega\mapsto\mathcal A_\omega$ be a random linear map $\mathbb R^{m\times n}\to\mathbb R^p$, given by random measurement matrices $X_1(\omega),\dots,X_p(\omega)$ whose entries are random variables, with $\mathcal A_\omega(X)_i=\langle X_i(\omega),X\rangle$. Write
--   $$\|\mathcal A\| = \sup\{\|\mathcal A(X)\| : \|X\|_F\le 1\}$$
--   for the operator norm of $\mathcal A$ from $(\mathbb R^{m\times n},\|\cdot\|_F)$ to $(\mathbb R^p,\|\cdot\|_2)$.
--
--   The random map $\mathcal A$ is **nearly isometrically distributed** if
--
--   1. for every $X\in\mathbb R^{m\times n}$, $\|\mathcal A(X)\|^2$ is integrable and $$\mathbb E\big[\|\mathcal A(X)\|^2\big]=\|X\|_F^2;$$
--   2. for every nonzero $X$ and every $0<\epsilon<1$, $$\mathbb P\big(\big|\|\mathcal A(X)\|^2-\|X\|_F^2\big|\ge\epsilon\|X\|_F^2\big)\le 2\exp\Big(-\frac p2\big(\epsilon^2/2-\epsilon^3/3\big)\Big);$$
--   3. there is a constant $\gamma>0$ such that for every $t>0$, $$\mathbb P\Big(\|\mathcal A\|\ge 1+\sqrt{mn/p}+t\Big)\le\exp(-\gamma p t^2).$$
--
--   The Gaussian ensemble with i.i.d. $N(0,1/p)$ entries and the symmetric Bernoulli and sparse ensembles of the paper are examples. The definition isolates exactly the two ingredients the paper's analysis uses: isometry in expectation and exponentially small probability of large distortions.
--
--   **Formalization Note** The concentration inequality (2) is imposed for $X\neq 0$ only. At $X=0$ the event is the whole sample space, so the printed inequality would read $1\le 2\exp(-\tfrac p2(\epsilon^2/2-\epsilon^3/3))$, which fails for large $p$ and would make the class empty. Integrability is part of (1) because a Lean integral of a non-integrable function is $0$. The constant $\gamma$ may depend on the distribution and on $m,n,p$, as printed. When $p=0$, $\sqrt{mn/p}$ is read as $0$ (Lean's division convention); such a map cannot satisfy (1) unless $mn=0$.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Definition 4.1, (4.1)–(4.3), p. 14

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst

open HighDimStat.MatrixRank MeasureTheory

namespace MinRankRecovery.RandomRIP

/-- The operator norm `‖A‖` of the linear map `A : (ℝ^{m×n}, ‖·‖_F) → (ℝᵖ, ‖·‖₂)` given by the
measurement matrices `Xs`: the supremum of `‖A(X)‖` over the Frobenius unit ball. The index
set is nonempty (it contains `0`) and the values are bounded (`A` is linear on a
finite-dimensional space), so the supremum is not a junk value. -/
noncomputable def mapNorm {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨆ X : {X : Matrix (Fin m) (Fin n) ℝ // frobeniusNorm X ≤ 1}, MinRankRecovery.Recovery.measNorm Xs X.1

/-- Definition 4.1, p. 14: the random linear map `ω ↦ A_ω`, `A_ω(X) = (⟨Xs ω i, X⟩)ᵢ`, on the
probability space `(Ω, μ)` is *nearly isometrically distributed*:
* every entry of every measurement matrix is a random variable (measurable);
* (4.1) for every `X`, `‖A(X)‖²` is integrable and `E‖A(X)‖² = ‖X‖_F²`;
* (4.2) for every `X ≠ 0` and `0 < ε < 1`,
  `P(|‖A(X)‖² − ‖X‖_F²| ≥ ε‖X‖_F²) ≤ 2 exp(−(p/2)(ε²/2 − ε³/3))`;
* (4.3) there is `γ > 0` with `P(‖A‖ ≥ 1 + √(mn/p) + t) ≤ exp(−γ p t²)` for all `t > 0`.
(4.2) is imposed for `X ≠ 0` only: at `X = 0` the event is the whole space and the printed
inequality would read `1 ≤ 2 exp(−(p/2)(ε²/2 − ε³/3))`, false for large `p`. -/
def IsNearlyIsometric {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {m n p : ℕ}
    (Xs : Ω → Fin p → Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i j k, Measurable fun ω => Xs ω i j k) ∧
  (∀ X : Matrix (Fin m) (Fin n) ℝ,
    Integrable (fun ω => MinRankRecovery.Recovery.measNorm (Xs ω) X ^ 2) μ ∧
    ∫ ω, MinRankRecovery.Recovery.measNorm (Xs ω) X ^ 2 ∂μ = frobeniusNorm X ^ 2) ∧
  (∀ X : Matrix (Fin m) (Fin n) ℝ, X ≠ 0 → ∀ ε : ℝ, 0 < ε → ε < 1 →
    μ {ω | ε * frobeniusNorm X ^ 2 ≤ |MinRankRecovery.Recovery.measNorm (Xs ω) X ^ 2 - frobeniusNorm X ^ 2|} ≤
      ENNReal.ofReal (2 * Real.exp (-((p : ℝ) / 2 * (ε ^ 2 / 2 - ε ^ 3 / 3))))) ∧
  (∃ γ : ℝ, 0 < γ ∧ ∀ t : ℝ, 0 < t →
    μ {ω | 1 + Real.sqrt ((m : ℝ) * n / p) + t ≤ mapNorm (Xs ω)} ≤
      ENNReal.ofReal (Real.exp (-(γ * p * t ^ 2))))

end MinRankRecovery.RandomRIP


