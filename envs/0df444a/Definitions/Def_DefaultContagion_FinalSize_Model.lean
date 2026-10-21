-- Prove2me | Definitions.Def_DefaultContagion_FinalSize_Model
-- name    : DefaultContagion_FinalSize_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:57:38.534992+00:00
-- url     : https://prove2.me/theorems/357265e2-495c-4aa0-a482-1bb5c8ac050b
-- title:
--   §§2.3–3, pp. 7–13 — threshold death process, fluid functions, final time and corrected covariance
-- statement:
--   Consider economies with $n$ banks and a countable type space $X$. A type $x$ has $d_x^+$ incoming and $d_x^-$ outgoing half-edges. Bank $i$ in economy $n$ has deterministic type $x_i^{(n)}$ and a random threshold $\Theta_i^{(n)}$ with law $q_x^{(n)}$ on $\{0,\ldots,d_x^+\}$. Each incoming half-edge has an independent exponential lifetime of mean one, also independent of the thresholds. A bank is solvent at time $t$ precisely when fewer than $\Theta_i^{(n)}$ of its incoming balls have died. The five counts are solvent banks $S_n$, defaulted banks $D_n$, alive healthy incoming balls $H_n^+$, alive infected incoming balls $I_n^+$, and white infected outgoing balls $W_n=L_n-H_n^--1$. The final time is the first nonnegative time $\tau_n^*$ with $W_n<0$.
--
--   Write $\mu_x^{(n)}$ for the fraction of banks of type $x$, $\lambda^{(n)}=n^{-1}\sum_i d_{x_i^{(n)}}^+$, and $\mu_x,q_x,\lambda$ for their limits. Equations (4)–(6) define the binomial probabilities $b(d,z,\ell)$, tails $\beta(d,z,\ell)$, the fluid functions $f_\clubsuit(z)$ and their finite-economy versions, and the largest zero
--   $$z^*=\sup\{z\in[0,1]:f_W(z)=0\}. $$
--   The five fluid functions are ordered $S,D,H^+,I^+,W$. The type-threshold count $S_{x,\theta,\ell}^{(n)}$ and its centring $s_{x,\theta,\ell}(z)=\mu_xq_x(\theta)b(d_x^+,1-z,\ell)$ are also defined.
--
--   The corrected covariance at a fixed survival probability $y$ is explicit. For type $x$, draw $\Theta\sim q_x$ and independently $K\sim\mathrm{Bin}(d_x^+,y)$, let $s=\mathbf1\{K+\Theta>d_x^+\}$, and put $\xi=(s,1-s,Ks,K-Ks,K-d_x^-s)$. Then
--   $$C(y)=\sum_{x\in X}\mu_x\operatorname{Cov}_x(\xi,\xi).$$
--   A linear correction matrix $J$ and the analogous variance for $S_{x,\theta,\ell}^{(n)}$ define the two Gaussian limits in Theorem 3.7. This model is shared by the goal and all seven milestones.
--
--   **Formalization Note** The threshold support, joint independence, degree-sum equality, and correction from printed $\lambda$ to $\lambda^{(n)}$ in two finite-economy fluid formulas are explicit. Time is real and nonnegative; the counts are defined after $\tau_n^*$ but used at or before it. The covariance replaces printed formulas whose lifetime variance is too small by a factor of two.
-- source:
--   Amini, Cao & Sulem, arXiv:2104.00248v1, pp. 7–13, §§2.3–3, equations (4)–(6), Assumptions 1, 2, 3a, 3b; covariance correction to pp. 31, 39, equations (24), (39)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DefaultContagion.FinalSize

/-- Equation (4): the binomial point probability. -/
noncomputable def binPmf (d : ℕ) (z : ℝ) (l : ℕ) : ℝ :=
  (d.choose l : ℝ) * z ^ l * (1 - z) ^ (d - l)

/-- Equation (5): the binomial upper tail. -/
noncomputable def binTail (d : ℕ) (z : ℝ) (l : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc l d, binPmf d z r

variable {X : Type*}

/-- The fraction of banks of type `x` in the economy of size `n`. -/
noncomputable def muN [DecidableEq X] (typ : (n : ℕ) → Fin n → X)
    (n : ℕ) (x : X) : ℝ :=
  ((Finset.univ.filter fun i : Fin n => typ n i = x).card : ℝ) / n

/-- The finite-economy average incoming degree. -/
noncomputable def lamN (dp : X → ℕ) (typ : (n : ℕ) → Fin n → X) (n : ℕ) : ℝ :=
  (∑ i : Fin n, (dp (typ n i) : ℝ)) / n

/-- The limiting solvent fraction. -/
noncomputable def fS (dp : X → ℕ) (mu : X → ℝ) (q : X → ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' x, mu x * ∑ θ ∈ Finset.Icc 1 (dp x),
    q x θ * binTail (dp x) z (dp x - θ + 1)

/-- The limiting number of healthy incoming balls per bank. -/
noncomputable def fH (dp : X → ℕ) (mu : X → ℝ) (q : X → ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' x, mu x * ∑ θ ∈ Finset.Icc 1 (dp x),
    q x θ * ∑ l ∈ Finset.Icc (dp x - θ + 1) (dp x),
      (l : ℝ) * binPmf (dp x) z l

/-- The limiting white infected outgoing balls per bank. -/
noncomputable def fW (dp dm : X → ℕ) (lam : ℝ) (mu : X → ℝ)
    (q : X → ℕ → ℝ) (z : ℝ) : ℝ :=
  lam * z - ∑' x, mu x * (dm x : ℝ) *
    ∑ θ ∈ Finset.Icc 1 (dp x), q x θ * binTail (dp x) z (dp x - θ + 1)

/-- The five fluid coordinates, in the order `S, D, H⁺, I⁺, W`. -/
noncomputable def fVec (dp dm : X → ℕ) (lam : ℝ) (mu : X → ℝ)
    (q : X → ℕ → ℝ) (z : ℝ) : Fin 5 → ℝ :=
  ![fS dp mu q z, 1 - fS dp mu q z, fH dp mu q z,
    lam * z - fH dp mu q z, fW dp dm lam mu q z]

/-- Equation (9)'s type-threshold-neighbour centring. -/
noncomputable def sFun (dp : X → ℕ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (x : X) (θ l : ℕ) (z : ℝ) : ℝ :=
  mu x * q x θ * binPmf (dp x) (1 - z) l

/-- Equation (6): the largest zero of `f` in `[0,1]`. -/
noncomputable def lastZero (f : ℝ → ℝ) : ℝ :=
  sSup {z | z ∈ Set.Icc (0 : ℝ) 1 ∧ f z = 0}

/-- A threshold probability law supported on `0, …, d⁺_x`. -/
def IsThresholdLaw (dp : X → ℕ) (q : X → ℕ → ℝ) : Prop :=
  ∀ x, (∀ θ, 0 ≤ q x θ) ∧ (∀ θ, dp x < θ → q x θ = 0) ∧
    ∑ θ ∈ Finset.range (dp x + 1), q x θ = 1

/-- Assumption 2, including the threshold-law support needed by the fluid formulas. -/
def Assumption2 [DecidableEq X] (dp : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (qn : ℕ → X → ℕ → ℝ) (mu : X → ℝ) (q : X → ℕ → ℝ) : Prop :=
  (∀ x, 0 ≤ mu x) ∧ HasSum mu 1 ∧ IsThresholdLaw dp q ∧
    (∀ n, IsThresholdLaw dp (qn n)) ∧
    (∀ x, Tendsto (fun n => muN typ n x) atTop (𝓝 (mu x))) ∧
    ∀ x θ, Tendsto (fun n => qn n x θ) atTop (𝓝 (q x θ))

/-- Assumption 3a and the degree-sum equality from the configuration model. -/
def Assumption3a (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (mu : X → ℝ) : Prop :=
  (∀ n, ∑ i : Fin n, dp (typ n i) = ∑ i : Fin n, dm (typ n i)) ∧
    Summable (fun x => mu x * (dp x : ℝ)) ∧
    0 < ∑' x, mu x * (dp x : ℝ) ∧
    Tendsto (lamN dp typ) atTop (𝓝 (∑' x, mu x * (dp x : ℝ)))

/-- Assumption 3b: uniform exponential moments of both degree sequences. -/
def Assumption3b (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X) : Prop :=
  ∀ A : ℝ, 1 < A → ∃ C : ℝ, ∀ n,
    (∑ i : Fin n, A ^ dp (typ n i) ≤ C * n) ∧
    (∑ i : Fin n, A ^ dm (typ n i) ≤ C * n)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Assumption 1 and §2.4: thresholds and the actual in-ball lifetimes are jointly
independent for each economy; the latter have exponential law of mean one. -/
def IsDeathProcess (P : Measure Ω) (dp : X → ℕ)
    (typ : (n : ℕ) → Fin n → X) (qn : ℕ → X → ℕ → ℝ)
    (Θ : (n : ℕ) → Fin n → Ω → ℕ)
    (T : (n : ℕ) → Fin n → ℕ → Ω → ℝ) : Prop :=
  ∀ n, (∀ i, Measurable (Θ n i)) ∧
    (∀ i k, k < dp (typ n i) → Measurable (T n i k)) ∧
    iIndepFun (fun (j : Fin n ⊕ ((i : Fin n) × Fin (dp (typ n i)))) (ω : Ω) =>
      match j with
      | Sum.inl i => (Θ n i ω : ℝ)
      | Sum.inr ⟨i, k⟩ => T n i k ω) P ∧
    (∀ i θ, P {ω | Θ n i ω = θ} = ENNReal.ofReal (qn n (typ n i) θ)) ∧
    ∀ i k, k < dp (typ n i) → P.map (T n i k) = expMeasure 1

/-- Number of dead incoming balls of bank `i` at time `t`. -/
noncomputable def dead (dp : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (T : (n : ℕ) → Fin n → ℕ → Ω → ℝ)
    (n : ℕ) (i : Fin n) (t : ℝ) (ω : Ω) : ℕ :=
  ((Finset.range (dp (typ n i))).filter fun k => T n i k ω ≤ t).card

/-- The five §2.4 counts before the death process is stopped. -/
noncomputable def stateVec (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (Θ : (n : ℕ) → Fin n → Ω → ℕ)
    (T : (n : ℕ) → Fin n → ℕ → Ω → ℝ)
    (n : ℕ) (t : ℝ) (ω : Ω) : Fin 5 → ℝ :=
  let solv := Finset.univ.filter fun i : Fin n => dead dp typ T n i t ω < Θ n i ω
  let alive : Fin n → ℝ := fun i => ((dp (typ n i) - dead dp typ T n i t ω : ℕ) : ℝ)
  let S : ℝ := solv.card
  let Hp : ℝ := ∑ i ∈ solv, alive i
  let L : ℝ := ∑ i, alive i
  let Hm : ℝ := ∑ i ∈ solv, (dm (typ n i) : ℝ)
  ![S, n - S, Hp, L - Hp, L - Hm - 1]

/-- Number of banks with type `x`, threshold `θ` and `l` dead incoming balls. -/
noncomputable def Sxtl [DecidableEq X] (dp : X → ℕ)
    (typ : (n : ℕ) → Fin n → X) (Θ : (n : ℕ) → Fin n → Ω → ℕ)
    (T : (n : ℕ) → Fin n → ℕ → Ω → ℝ)
    (n : ℕ) (x : X) (θ l : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ((Finset.univ.filter fun i : Fin n =>
      typ n i = x ∧ Θ n i ω = θ ∧ dead dp typ T n i t ω = l).card : ℝ)

/-- The first nonnegative time at which the white-ball count is negative. -/
noncomputable def tauStar (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (Θ : (n : ℕ) → Fin n → Ω → ℕ)
    (T : (n : ℕ) → Fin n → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ stateVec dp dm typ Θ T n t ω 4 < 0}

/-- Expectation with a type-specific threshold and a binomial alive-ball count. -/
noncomputable def binExp (dp : X → ℕ) (q : X → ℕ → ℝ)
    (x : X) (y : ℝ) (φ : ℕ → ℕ → ℝ) : ℝ :=
  ∑ θ ∈ Finset.range (dp x + 1),
    ∑ K ∈ Finset.range (dp x + 1), q x θ * binPmf (dp x) y K * φ θ K

/-- Corrected equal-time covariance of two per-bank coordinates. -/
noncomputable def limCov (dp : X → ℕ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (g h : X → ℕ → ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑' x, mu x * (binExp dp q x y (fun θ K => g x θ K * h x θ K) -
    binExp dp q x y (g x) * binExp dp q x y (h x))

/-- Per-bank contribution to each of the five counts, with `K` alive balls. -/
noncomputable def feat (dp dm : X → ℕ) (c : Fin 5)
    (x : X) (θ K : ℕ) : ℝ :=
  let s : ℝ := if dp x < K + θ then 1 else 0
  ![s, 1 - s, (K : ℝ) * s, (K : ℝ) - K * s,
    (K : ℝ) - dm x * s] c

/-- Per-bank contribution to the type-threshold-neighbour count. -/
noncomputable def featX [DecidableEq X] (dp : X → ℕ)
    (x₀ : X) (θ₀ l : ℕ) (x : X) (θ K : ℕ) : ℝ :=
  if x = x₀ ∧ θ = θ₀ ∧ K + l = dp x then 1 else 0

/-- Corrected equal-time covariance matrix for the five coordinates. -/
noncomputable def covMat (dp dm : X → ℕ) (mu : X → ℝ)
    (q : X → ℕ → ℝ) (y : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => limCov dp mu q (feat dp dm i) (feat dp dm j) y

/-- Linear correction for evaluating the fluid functions at the random final time. -/
noncomputable def jac (dp dm : X → ℕ) (lam : ℝ) (mu : X → ℝ)
    (q : X → ℕ → ℝ) (z : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (if i = j then 1 else 0) -
    (if j = 4 then deriv (fun w => fVec dp dm lam mu q w i) z /
      deriv (fW dp dm lam mu q) z else 0)

/-- Variance of the type-threshold-neighbour final-size limit in (9). -/
noncomputable def var9 [DecidableEq X] (dp dm : X → ℕ) (lam : ℝ)
    (mu : X → ℝ) (q : X → ℕ → ℝ)
    (z : ℝ) (x : X) (θ l : ℕ) : ℝ :=
  let g := featX dp x θ l
  let w := feat dp dm 4
  let a := deriv (sFun dp mu q x θ l) z /
    deriv (fW dp dm lam mu q) z
  limCov dp mu q g g z - 2 * a * limCov dp mu q g w z +
    a ^ 2 * limCov dp mu q w w z

end DefaultContagion.FinalSize


