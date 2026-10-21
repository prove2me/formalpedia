-- Prove2me | Definitions.Def_LiqProvision_Oligopoly_Model
-- name    : LiqProvision_Oligopoly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:51.958563+00:00
-- url     : https://prove2.me/theorems/8b273b1a-e24c-4642-a347-0d9210ba9333
-- title:
--   §2–§3.2, pp. 3–11 — K dealers quoting price schedules to a client with log-concave effective type: admissibility, compatibility, dealer goal functional, symmetric Nash equilibrium, ODE (3.8)
-- statement:
--   This file sets up the model of Herdegen, Muhle-Karbe and Stebegg: $K$ dealers quote price schedules to a client who trades a risky asset, and the dealers compete in schedules.
--
--   **Primitives.** The model is given by the number $K$ of dealers, the client's inventory cost $\gamma_c$, the dealers' inventory cost $\gamma_d$, and the densities $f_S$ of the client's signal $S$ and $f_M$ of the client's initial inventory $M$. The **standing assumptions** are
--   $$K\ge 2,\qquad \gamma_c>0,\qquad \gamma_d\ge 0,$$
--   and $f_S$, $f_M$ are positive probability densities on $\mathbb R$. **Assumption 2.1** adds that $\log f_S$ and $\log f_M$ are concave.
--
--   **Effective type.** The client's effective type is $Y=S-\gamma_c M$. Its density is the convolution
--   $$f(y)=\int_{\mathbb R} f_S(s)\,\frac{1}{\gamma_c}f_M\!\Big(\frac{s-y}{\gamma_c}\Big)\,ds,$$
--   with distribution function $F(x)=\int_{-\infty}^x f$ and survival function $\bar F(x)=\int_x^\infty f$. The conditional mean of the asset payoff given the type is the Bayes ratio
--   $$g(y)=E[V\mid Y=y]=E[S\mid Y=y]=\frac{1}{f(y)}\int_{\mathbb R} s\,f_S(s)\,\frac{1}{\gamma_c}f_M\!\Big(\frac{s-y}{\gamma_c}\Big)\,ds .$$
--   **Assumption 3.7** asks that $\limsup_{w\to\pm\infty} g'(w)<1$.
--
--   **Price schedules and the client.** A price schedule is a continuous $P:\mathbb R\to\mathbb R$ with $P(0)=0$ that is twice continuously differentiable on $\mathbb R\setminus\{0\}$. Against a profile $\mathbf P=(P_1,\dots,P_K)$ a client of type $y$ maximizes
--   $$J^{\mathbf P}(y;\mathbf n)=y\sum_{k=1}^K n_k-\sum_{k=1}^K P_k(n_k)-\frac{\gamma_c}{2}\Big(\sum_{k=1}^K n_k\Big)^2 \qquad (2.2)$$
--   over $\mathbf n\in\mathbb R^K$. A price schedule $P$ is **admissible** (Definition 2.3) if, when every dealer quotes $P$, this problem has a unique maximizer for every type $y$. Admissible schedules $P_1,\dots,P_K$ are **compatible** (Definition 2.7) if the problem has a maximizer for some type $y$.
--
--   **Dealers.** Given the client's trade $n_1(y)$ with dealer 1, dealer 1's goal functional is
--   $$J_d^{\mathbf P}(P_1)=\int_{-\infty}^{\infty}\Big(P_1(n_1(y))-g(y)n_1(y)-\frac{\gamma_d}{2}n_1(y)^2\Big)f(y)\,dy,$$
--   with the convention that the integral equals $-\infty$ if the negative part of the integrand is not integrable (footnote 5). A price schedule $P$ is a **symmetric Nash equilibrium** if $P$ is admissible and, for every $P_1$ such that $(P_1,P,\dots,P)$ is compatible, dealer 1's goal functional under $(P_1,P,\dots,P)$ is at most her goal functional under $(P,\dots,P)$, the client's trades being the optimal responses to the respective profiles.
--
--   **The ODE (3.8).** For a marginal price function $p=P'$ on $\mathbb R\setminus\{0\}$, write $y_p(n)=p(n)+\gamma_cKn$ and $c_p(n)=\gamma_d n-p(n)+g(y_p(n))$. The ODE (3.8) is
--   $$p'(n)=\begin{cases}\dfrac{(K-1)\gamma_c\,c_p(n)}{(F/f)(y_p(n))-c_p(n)}, & n<0,\\[2ex] \dfrac{(K-1)\gamma_c\,c_p(n)}{-(\bar F/f)(y_p(n))-c_p(n)}, & n>0,\end{cases}$$
--   with nonvanishing denominators. Theorem 3.8's class consists of the increasing, continuously differentiable functions $p$ on $\mathbb R\setminus\{0\}$ that solve (3.8).
--
--   **Assumption 3.10** asks that $(F/f)'-g'\le\gamma_d/\gamma_c$ on $(-\infty,p(0-)]$ and $(-\bar F/f)'-g'\le\gamma_d/\gamma_c$ on $[p(0+),\infty)$, where $p$ is the solution of (3.8).
--
--   **Proof objects of Theorem 3.11 (pp. 18, 21, 28).** With $h=fg$, $H(x)=\int_{-\infty}^x h$ and $\bar H(x)=\int_x^\infty h$, and the inverse $p^{-1}$ of $p$ on $\mathbb R\setminus\{0\}$ extended by $p^{-1}(z)=0$ for $z\in[p(0-),p(0+)]$,
--   $$\eta_-(n,x,z)=(\gamma_d n-z)F(\xi)+H(\xi),\qquad \eta_+(n,x,z)=-(\gamma_d n-z)\bar F(\xi)-\bar H(\xi),\qquad \xi=z+\gamma_c n+\gamma_c(K-1)x .$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.**
--   1. The error term $\varepsilon$ in $V=S+\varepsilon$ is mean zero and independent, so it enters only through $E[V\mid Y]=E[S\mid Y]$ (p. 17); the model does not carry it. $g$ is the explicit Bayes ratio, the continuous version of $E[S\mid Y=y]$ that the paper differentiates.
--   2. Dealers are indexed by `Fin K`, and dealer 1 of the paper is index `0`.
--   3. The client's optimal responses are quantified rather than chosen: the equilibrium condition is required for every response function. For compatible profiles the maximizer exists and is unique for every type (Theorem 2.8(a)), so this is the paper's $\mathbf n^{\mathbf P}$ and the quantifier is not vacuous.
--   4. Dealer 1's goal functional is an extended real: $-\infty$ if the lower Lebesgue integral of the negative part is infinite, else the difference of the positive and negative parts (footnote 5).
--   5. "Increasing" is strict, as in the paper. $p(0\mp)$ are the one-sided limits of $p$ at $0$; the value $p(0)$ is never used.
--   6. Assumption 3.7 is stated as: there is $c<1$ with $g'(w)\le c$ for all large $w$, and likewise for all sufficiently negative $w$; this is equivalent to $\limsup<1$.
--   7. In (3.10), Assumption 3.10 is stated as $(-\bar F/f)'-g'\le\gamma_d/\gamma_c$. The page prints $(\bar F/f)'$ without the minus sign. That printed condition always holds, because $\bar F/f$ is nonincreasing and $g'>0$, and the proof ((B.57), p. 28) uses $(-\bar F/f)'$, which also matches (3.6) on p. 8.
--   8. $p^{-1}(z)$ is defined as the (unique, for increasing $p$) $n\ne0$ with $p(n)=z$, and as $0$ if there is none. For an increasing solution of (3.8) the image of $\mathbb R\setminus\{0\}$ is $\mathbb R\setminus[p(0-),p(0+)]$, so this is the paper's convention.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, pp. 3–11, 17–18, 21, 28; §2, (2.2), Assumption 2.1, Definitions 2.3, 2.7, (3.2), footnote 5, §3.2, (3.8), Assumptions 3.7, 3.10, (B.51)–(B.52)

import Mathlib

namespace LiqProvision.Oligopoly

open MeasureTheory Filter Topology

/-- Primitives of the model (pp. 3–4, 7, 9): the number `K` of dealers, the client's inventory cost
`γc`, the dealers' inventory cost `γd`, and the densities `fS` of the signal `S` and `fM` of the
client's initial inventory `M`. -/
structure Params where
  K : ℕ
  γc : ℝ
  γd : ℝ
  fS : ℝ → ℝ
  fM : ℝ → ℝ

/-- A positive probability density on `ℝ`. -/
def IsDensity (h : ℝ → ℝ) : Prop :=
  (∀ x, 0 < h x) ∧ Integrable h ∧ ∫ x, h x = 1

/-- Standing assumptions: `K ≥ 2` (p. 9), `γc > 0` (p. 3), `γd ≥ 0` (p. 7), positive probability
densities (Assumption 2.1, p. 4). -/
def Params.Standing (M : Params) : Prop :=
  2 ≤ M.K ∧ 0 < M.γc ∧ 0 ≤ M.γd ∧ IsDensity M.fS ∧ IsDensity M.fM

/-- Log-concavity of a positive function: `log h` is concave on `ℝ`. -/
def LogConcave (h : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ Set.univ (fun x => Real.log (h x))

/-- Assumption 2.1 (p. 4): the densities of `S` and `M` are log-concave. -/
def Params.Assumption21 (M : Params) : Prop :=
  LogConcave M.fS ∧ LogConcave M.fM

/-- Joint kernel of `(Y, S)` at `Y = y`, `S = s`, for the effective type `Y = S − γc M`:
`fS(s) · f_{−γc M}(y − s)` with `f_{−γc M}(z) = fM(−z/γc)/γc`. -/
noncomputable def kernel (M : Params) (y s : ℝ) : ℝ :=
  M.fS s * (M.fM ((s - y) / M.γc) / M.γc)

/-- The density `f` of the effective type `Y = S − γc M` (p. 4). -/
noncomputable def dens (M : Params) (y : ℝ) : ℝ :=
  ∫ s, kernel M y s

/-- The cumulative distribution function `F(x) = ∫_{-∞}^x f` (p. 4). -/
noncomputable def cdf (M : Params) (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, dens M y

/-- The survival function `F̄(x) = ∫_x^∞ f` (p. 4). -/
noncomputable def surv (M : Params) (x : ℝ) : ℝ :=
  ∫ y in Set.Ioi x, dens M y

/-- The conditional mean `g(y) = E[V | Y = y] = E[S | Y = y]` (3.2), as the Bayes ratio. -/
noncomputable def condMean (M : Params) (y : ℝ) : ℝ :=
  (∫ s, s * kernel M y s) / dens M y

/-- Assumption 3.7 (p. 10): `limsup_{w → ±∞} g'(w) < 1`, as an eventual bound by a constant `< 1`
at each end. -/
def Params.Assumption37 (M : Params) : Prop :=
  (∃ c < 1, ∀ᶠ w in atTop, deriv (condMean M) w ≤ c) ∧
  (∃ c < 1, ∀ᶠ w in atBot, deriv (condMean M) w ≤ c)

/-- A price schedule (p. 3): continuous, `P 0 = 0`, twice continuously differentiable off `0`. -/
def IsPriceSchedule (P : ℝ → ℝ) : Prop :=
  Continuous P ∧ P 0 = 0 ∧ ContDiffOn ℝ 2 P {0}ᶜ

/-- The client's normalized goal functional (2.2) against the profile `Q = (Q₁, …, Q_K)`. -/
noncomputable def clientObj (M : Params) (Q : Fin M.K → ℝ → ℝ) (y : ℝ) (n : Fin M.K → ℝ) : ℝ :=
  y * ∑ k, n k - ∑ k, Q k (n k) - M.γc / 2 * (∑ k, n k) ^ 2

/-- `n` maximizes the client's goal functional at type `y`. -/
def IsClientMax (M : Params) (Q : Fin M.K → ℝ → ℝ) (y : ℝ) (n : Fin M.K → ℝ) : Prop :=
  ∀ n', clientObj M Q y n' ≤ clientObj M Q y n

/-- A response function: `r y` is a maximizer of the client's problem for every type `y`. -/
def IsResponse (M : Params) (Q : Fin M.K → ℝ → ℝ) (r : ℝ → Fin M.K → ℝ) : Prop :=
  ∀ y, IsClientMax M Q y (r y)

/-- Definition 2.3 (p. 5): `P` is admissible for `K` dealers if, when all dealers quote `P`, the
client's problem has a unique maximizer for every type. -/
def Admissible (M : Params) (P : ℝ → ℝ) : Prop :=
  IsPriceSchedule P ∧ ∀ y, ∃! n, IsClientMax M (fun _ => P) y n

/-- Definition 2.7 (p. 6): admissible schedules are compatible if the client's problem has a
solution for some type. -/
def Compatible (M : Params) (Q : Fin M.K → ℝ → ℝ) : Prop :=
  (∀ k, Admissible M (Q k)) ∧ ∃ y n, IsClientMax M Q y n

/-- The profile `(P₁, P, …, P)`; dealer 1 of the paper is index `0`. -/
def devProfile (M : Params) (P₁ P : ℝ → ℝ) : Fin M.K → ℝ → ℝ :=
  fun k => if k.val = 0 then P₁ else P

/-- Footnote 5 (p. 7): the integral of `h` in `EReal`, equal to `−∞` if the negative part of `h`
is not integrable, and to `∫ h⁺ − ∫ h⁻` otherwise. -/
noncomputable def extIntegral (h : ℝ → ℝ) : EReal :=
  if (∫⁻ y, ENNReal.ofReal (-h y)) < ⊤ then
    ((∫⁻ y, ENNReal.ofReal (h y) : ENNReal) : EReal) -
      ((∫⁻ y, ENNReal.ofReal (-h y) : ENNReal) : EReal)
  else ⊥

/-- Dealer 1's goal functional `J^P_d(P₁)` (p. 9), given dealer 1's schedule `P₁` and the
client's trade `n₁(y)` with dealer 1. -/
noncomputable def dealerValue (M : Params) (P₁ : ℝ → ℝ) (n₁ : ℝ → ℝ) : EReal :=
  extIntegral (fun y => (P₁ (n₁ y) - condMean M y * n₁ y - M.γd / 2 * n₁ y ^ 2) * dens M y)

/-- Symmetric Nash equilibrium (§3.2, p. 9): `P` is admissible, and for every `P₁` making
`(P₁, P, …, P)` compatible, dealer 1's goal functional under the deviation is at most her goal
functional under `(P, …, P)`, for the client's optimal responses. -/
def IsSymNE (M : Params) (P : ℝ → ℝ) : Prop :=
  Admissible M P ∧
  ∀ P₁ : ℝ → ℝ, Compatible M (devProfile M P₁ P) →
    ∀ r r' : ℝ → Fin M.K → ℝ,
      IsResponse M (devProfile M P₁ P) r → IsResponse M (devProfile M P P) r' →
      ∀ k : Fin M.K, k.val = 0 →
        dealerValue M P₁ (fun y => r y k) ≤ dealerValue M P (fun y => r' y k)

/-- The argument `p(n) + γc K n` of `F/f`, `F̄/f` and `g` in the ODE (3.8). -/
noncomputable def odeArg (M : Params) (p : ℝ → ℝ) (n : ℝ) : ℝ :=
  p n + M.γc * (M.K : ℝ) * n

/-- The common term `γd n − p(n) + g(p(n) + γc K n)` of (3.8). -/
noncomputable def odeCore (M : Params) (p : ℝ → ℝ) (n : ℝ) : ℝ :=
  M.γd * n - p n + condMean M (odeArg M p n)

/-- Numerator of (3.8): `(K − 1) γc (γd n − p(n) + g(p(n) + γc K n))`. -/
noncomputable def odeNum (M : Params) (p : ℝ → ℝ) (n : ℝ) : ℝ :=
  ((M.K : ℝ) - 1) * M.γc * odeCore M p n

/-- Denominator of (3.8) on `n < 0`: `(F/f)(p(n) + γc K n) − (γd n − p(n) + g(…))`. -/
noncomputable def odeDenNeg (M : Params) (p : ℝ → ℝ) (n : ℝ) : ℝ :=
  cdf M (odeArg M p n) / dens M (odeArg M p n) - odeCore M p n

/-- Denominator of (3.8) on `n > 0`: `−(F̄/f)(p(n) + γc K n) − (γd n − p(n) + g(…))`. -/
noncomputable def odeDenPos (M : Params) (p : ℝ → ℝ) (n : ℝ) : ℝ :=
  -(surv M (odeArg M p n) / dens M (odeArg M p n)) - odeCore M p n

/-- The ODE (3.8) for the marginal price `p = P'`, with nonvanishing denominators. -/
def ODEHolds (M : Params) (p : ℝ → ℝ) : Prop :=
  (∀ n < 0, odeDenNeg M p n ≠ 0 ∧ deriv p n = odeNum M p n / odeDenNeg M p n) ∧
  (∀ n > 0, odeDenPos M p n ≠ 0 ∧ deriv p n = odeNum M p n / odeDenPos M p n)

/-- Theorem 3.8's class (p. 10): `p` is increasing and continuously differentiable on `ℝ ∖ {0}`
and satisfies (3.8). The value `p 0` plays no role. -/
def IsODESol (M : Params) (p : ℝ → ℝ) : Prop :=
  StrictMonoOn p {0}ᶜ ∧ ContDiffOn ℝ 1 p {0}ᶜ ∧ ODEHolds M p

/-- Assumption 3.10 (p. 11), with (3.10) in the form `(−F̄/f)' − g' ≤ γd/γc` used by the proof
(B.57), and `P'_*(0∓)` the one-sided limits of `p` at `0`:
(3.9) `(F/f)' − g' ≤ γd/γc` on `(−∞, p(0−)]`, (3.10) `(−F̄/f)' − g' ≤ γd/γc` on `[p(0+), ∞)`. -/
def Assumption310 (M : Params) (p : ℝ → ℝ) : Prop :=
  (∀ c, Tendsto p (𝓝[<] 0) (𝓝 c) → ∀ y ≤ c,
      deriv (fun x => cdf M x / dens M x) y - deriv (condMean M) y ≤ M.γd / M.γc) ∧
  (∀ c, Tendsto p (𝓝[>] 0) (𝓝 c) → ∀ y, c ≤ y →
      deriv (fun x => -(surv M x / dens M x)) y - deriv (condMean M) y ≤ M.γd / M.γc)

/-- `h = f g` (p. 18). -/
noncomputable def hfun (M : Params) (y : ℝ) : ℝ :=
  dens M y * condMean M y

/-- `H(x) = ∫_{-∞}^x h` (p. 21). -/
noncomputable def Hcdf (M : Params) (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, hfun M y

/-- `H̄(x) = ∫_x^∞ h` (p. 21). -/
noncomputable def Hsurv (M : Params) (x : ℝ) : ℝ :=
  ∫ y in Set.Ioi x, hfun M y

open Classical in
/-- The inverse `p⁻¹` of a marginal price `p` on `ℝ ∖ {0}`, with the convention `p⁻¹(z) = 0`
when `z` is not a value `p(n)`, `n ≠ 0` (for an increasing solution of (3.8), exactly when
`z ∈ [p(0−), p(0+)]`, p. 21). -/
noncomputable def pinv (p : ℝ → ℝ) (z : ℝ) : ℝ :=
  if h : ∃ n, n ≠ 0 ∧ p n = z then h.choose else 0

/-- The type argument `z + γc n + γc (K − 1) x` of (B.51)–(B.52). -/
noncomputable def etaArg (M : Params) (n x z : ℝ) : ℝ :=
  z + M.γc * n + M.γc * ((M.K : ℝ) - 1) * x

/-- `η₋(n, x, z) = (γd n − z) F(·) + H(·)` (B.51). -/
noncomputable def etaNeg (M : Params) (n x z : ℝ) : ℝ :=
  (M.γd * n - z) * cdf M (etaArg M n x z) + Hcdf M (etaArg M n x z)

/-- `η₊(n, x, z) = −(γd n − z) F̄(·) − H̄(·)` (B.52). -/
noncomputable def etaPos (M : Params) (n x z : ℝ) : ℝ :=
  -(M.γd * n - z) * surv M (etaArg M n x z) - Hsurv M (etaArg M n x z)

end LiqProvision.Oligopoly


