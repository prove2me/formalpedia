-- Prove2me | Definitions.Def_GaussianBCSecondOrder_Codes
-- name    : GaussianBCSecondOrder_Codes
-- status  : Definition
-- author  : @Vincent Tan
-- created : 2026-11-23T07:27:10.066371+00:00
-- url     : https://prove2.me/theorems/8d2b1d9a-5cc4-4844-b457-2d4451c0c3ba
-- title:
--   Gaussian broadcast channel: codes, error probabilities and second-order coding region
-- statement:
--   This file formalizes the channel model, the notion of a code and the second-order coding region of the two-receiver scalar Gaussian broadcast channel, in the normalized form of eqs. (6)-(7).
--
--   **Channel.** Let $S_1>S_2>0$ be the signal-to-noise ratios of the two receivers and $\rho\in[-1,1]$ the noise correlation coefficient. The normalized channel is $Y_j^n=X^n+Z_j^n$, $j=1,2$, where the noise pairs $(Z_{1,i},Z_{2,i})$, $i=1,\dots,n$, are i.i.d. centered Gaussian with variances $1/S_1$, $1/S_2$ and covariance $\rho/\sqrt{S_1S_2}$, and codewords satisfy $\|x^n\|^2\le n$.
--
--   **Codes (Definition 1).** An $(n,M_1,M_2)$-code consists of an encoder $f_n:[M_1]\times[M_2]\to\mathbb R^n$ with $\|f_n(m_1,m_2)\|^2\le n$ for all message pairs (eq. (9)) and two measurable decoders $\varphi_{j,n}:\mathbb R^n\to[M_j]$. When $(m_1,m_2)$ is sent, receiver $j$ outputs $\hat W_j=\varphi_{j,n}(Y_j^n)$. The conditional error probability is
--   $$\varepsilon_n(m_1,m_2)=\Pr\big((\hat W_1,\hat W_2)\ne(m_1,m_2)\,\big|\,W_1=m_1,W_2=m_2\big),$$
--   the average error probability is $\varepsilon_{n,\mathrm{av}}=\frac1{M_1M_2}\sum_{m_1,m_2}\varepsilon_n(m_1,m_2)$, and the maximal error probability is $\max_{m_1,m_2}\varepsilon_n(m_1,m_2)$. A code is an $(n,M_1,M_2,\varepsilon_n)_\dagger$-code, $\dagger\in\{\mathrm{av},\mathrm{max}\}$, if the corresponding error probability is at most $\varepsilon_n$. The file also defines the joint success probability $s(m_1,m_2)=\Pr(\hat W_1=m_1,\hat W_2=m_2\mid W_1=m_1,W_2=m_2)$ and its average.
--
--   **Second-order region (Definition 2).** Fix $\varepsilon$, a first-order rate pair $R^*=(R_1^*,R_2^*)$ and $\dagger$. A pair $(L_1,L_2)\in\mathbb R^2$ is $(\varepsilon,R^*)_\dagger$-second-order achievable if there is a sequence of $(n,M_{1,n},M_{2,n},\varepsilon_n)_\dagger$-codes with
--   $$\liminf_{n\to\infty}\frac1{\sqrt n}\big(\log M_{j,n}-nR_j^*\big)\ge L_j,\quad j=1,2,\qquad \limsup_{n\to\infty}\varepsilon_n\le\varepsilon .$$
--   The second-order region $\mathcal L_\dagger(\varepsilon;R^*)$ is the closure of the set of all such pairs.
--
--   These definitions are the model on which Theorem 1 and all code-level lemmas of the mission rest.
--
--   **Formalization Note** Vectors in $\mathbb R^n$ are elements of `EuclideanSpace ℝ (Fin n)`, so $\|\cdot\|$ is the Euclidean norm; message sets are `Fin M₁`, `Fin M₂` (a code can only exist when $M_1,M_2\ge1$). A noise sample is a function `z : Fin n → EuclideanSpace ℝ (Fin 2)` with `z i 0` $=Z_{1,i}$ and `z i 1` $=Z_{2,i}$; its law is the $n$-fold product of Mathlib's `multivariateGaussian 0` with the covariance matrix of eq. (7) (which may be singular when $\rho=\pm1$). The maximal-error criterion is stated as "every conditional error probability is at most $\varepsilon_n$". A sequence of codes has one code for every $n\in\mathbb N$, and the $\liminf$ and $\limsup$ are taken in the extended reals, so unbounded sequences are handled correctly.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, pp. 5-6, Section II-A, eqs. (6), (7), (9)-(12), (16), Definition 1 and Definition 2

import Definitions.Def_GaussianBCSecondOrder_Functions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Order.LiminfLimsup

/-!
Channel model, codes, error probabilities and the second-order coding region of the scalar
Gaussian broadcast channel (V. Y. F. Tan, arXiv:2611.01583v1, Section II-A, eqs. (6)–(16),
Definitions 1 and 2), in the normalized form `Y_j^n = X^n + Z_j^n`, `j = 1, 2`, with unit power
constraint.
-/

open MeasureTheory ProbabilityTheory Filter

namespace GaussianBCSecondOrder

/-- Covariance matrix of one normalized noise pair `(Z_{1,i}, Z_{2,i})`, eq. (7):
variances `1 / S₁`, `1 / S₂` and covariance `ρ / √(S₁ S₂)`. -/
noncomputable def noiseCov (S₁ S₂ ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / S₁, ρ / Real.sqrt (S₁ * S₂); ρ / Real.sqrt (S₁ * S₂), 1 / S₂]

/-- Joint law of the `n` noise pairs `(Z_{1,i}, Z_{2,i})`, `i = 1, …, n`: independent and
identically distributed centered Gaussian pairs with covariance `noiseCov S₁ S₂ ρ`.
A sample is `z : Fin n → ℝ²`, where `z i 0 = Z_{1,i}` and `z i 1 = Z_{2,i}`. -/
noncomputable def noiseLaw (S₁ S₂ ρ : ℝ) (n : ℕ) :
    Measure (Fin n → EuclideanSpace ℝ (Fin 2)) :=
  Measure.pi fun _ => multivariateGaussian 0 (noiseCov S₁ S₂ ρ)

/-- The noise vector seen by one receiver: `noiseVec 0 z = Z₁^n` and `noiseVec 1 z = Z₂^n`. -/
def noiseVec {n : ℕ} (j : Fin 2) (z : Fin n → EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => z i j

/-- An `(n, M₁, M₂)`-code (Definition 1): an encoder `[M₁] × [M₂] → ℝⁿ` whose codewords satisfy
the unit power constraint `‖x‖² ≤ n` (eq. (9)), and two measurable decoders
`ℝⁿ → [M_j]`. The message sets are `Fin M₁` and `Fin M₂`. -/
structure Code (n M₁ M₂ : ℕ) where
  encoder : Fin M₁ → Fin M₂ → EuclideanSpace ℝ (Fin n)
  decoder₁ : EuclideanSpace ℝ (Fin n) → Fin M₁
  decoder₂ : EuclideanSpace ℝ (Fin n) → Fin M₂
  measurable_decoder₁ : Measurable decoder₁
  measurable_decoder₂ : Measurable decoder₂
  power_le : ∀ m₁ m₂, ‖encoder m₁ m₂‖ ^ 2 ≤ (n : ℝ)

namespace Code

variable {n M₁ M₂ : ℕ}

/-- Probability `s(m₁, m₂)` that both receivers decode correctly when `(m₁, m₂)` is sent:
receiver 1 observes `Y₁^n = x^n(m₁, m₂) + Z₁^n` and receiver 2 observes
`Y₂^n = x^n(m₁, m₂) + Z₂^n`. -/
noncomputable def condSuccess (c : Code n M₁ M₂) (S₁ S₂ ρ : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ :=
  (noiseLaw S₁ S₂ ρ n).real
    {z | c.decoder₁ (c.encoder m₁ m₂ + noiseVec 0 z) = m₁ ∧
         c.decoder₂ (c.encoder m₁ m₂ + noiseVec 1 z) = m₂}

/-- Conditional (joint) error probability `ε_n(m₁, m₂)`, eq. (10): the probability that
`(Ŵ₁, Ŵ₂) ≠ (m₁, m₂)` when `(m₁, m₂)` is sent. -/
noncomputable def condError (c : Code n M₁ M₂) (S₁ S₂ ρ : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ :=
  (noiseLaw S₁ S₂ ρ n).real
    {z | ¬ (c.decoder₁ (c.encoder m₁ m₂ + noiseVec 0 z) = m₁ ∧
            c.decoder₂ (c.encoder m₁ m₂ + noiseVec 1 z) = m₂)}

/-- Average error probability `ε_{n,av}`, eq. (11), for independent uniform messages. -/
noncomputable def avgError (c : Code n M₁ M₂) (S₁ S₂ ρ : ℝ) : ℝ :=
  (1 / ((M₁ : ℝ) * (M₂ : ℝ))) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, c.condError S₁ S₂ ρ m₁ m₂

/-- Average probability of successful decoding, `(1 / (M₁ M₂)) ∑ s(m₁, m₂)`. -/
noncomputable def avgSuccess (c : Code n M₁ M₂) (S₁ S₂ ρ : ℝ) : ℝ :=
  (1 / ((M₁ : ℝ) * (M₂ : ℝ))) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, c.condSuccess S₁ S₂ ρ m₁ m₂

end Code

/-- The two error criteria: average (`av`) and maximal (`max`) error probability. -/
inductive Criterion where
  | avg
  | max

/-- `c.Meets crit S₁ S₂ ρ e` says that `c` is an `(n, M₁, M₂, e)_†`-code:
for `† = av` the average error probability is at most `e` (eq. (11));
for `† = max` every conditional error probability is at most `e` (eq. (12)). -/
def Code.Meets {n M₁ M₂ : ℕ} (c : Code n M₁ M₂) (crit : Criterion) (S₁ S₂ ρ e : ℝ) : Prop :=
  match crit with
  | .avg => c.avgError S₁ S₂ ρ ≤ e
  | .max => ∀ m₁ m₂, c.condError S₁ S₂ ρ m₁ m₂ ≤ e

/-- Second-order rate of a message-size sequence at first-order rate `R`:
`(log M_n - n R) / √n`, as an extended real number. -/
noncomputable def secondOrderRate (M : ℕ → ℕ) (R : ℝ) (n : ℕ) : EReal :=
  (((Real.log (M n) - n * R) / Real.sqrt n : ℝ) : EReal)

/-- `(ε, R*)_†`-second-order achievability of the offset pair `L = (L₁, L₂)` (Definition 2):
there is a sequence of `(n, M_{1,n}, M_{2,n}, ε_n)_†`-codes, one for every blocklength `n`, with
`liminf (log M_{j,n} - n R*_j) / √n ≥ L_j` for `j = 1, 2` and `limsup ε_n ≤ ε` (eq. (16)).
The `liminf` and `limsup` are taken in the extended reals. -/
def SecondOrderAchievable (crit : Criterion) (S₁ S₂ ρ ε : ℝ) (R L : ℝ × ℝ) : Prop :=
  ∃ (M₁ M₂ : ℕ → ℕ) (e : ℕ → ℝ) (c : ∀ n, Code n (M₁ n) (M₂ n)),
    (∀ n, (c n).Meets crit S₁ S₂ ρ (e n)) ∧
    (L.1 : EReal) ≤ liminf (secondOrderRate M₁ R.1) atTop ∧
    (L.2 : EReal) ≤ liminf (secondOrderRate M₂ R.2) atTop ∧
    limsup (fun n => ((e n : ℝ) : EReal)) atTop ≤ (ε : EReal)

/-- The second-order coding region `L_†(ε; R*)` (Definition 2): the closure in `ℝ²` of the set
of `(ε, R*)_†`-second-order achievable offset pairs. -/
def secondOrderRegion (crit : Criterion) (S₁ S₂ ρ ε : ℝ) (R : ℝ × ℝ) : Set (ℝ × ℝ) :=
  closure {L | SecondOrderAchievable crit S₁ S₂ ρ ε R L}

end GaussianBCSecondOrder


