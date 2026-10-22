-- Prove2me | Definitions.Def_FollowCrowd_Inference_Model
-- name    : FollowCrowd_Inference_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:32.430448+00:00
-- url     : https://prove2.me/theorems/aef63f2a-f9fa-420b-8ead-0bb2c47c2827
-- title:
--   §3–§4.2, pp. 6–10 — observable M/M/1 with unknown rate µH/µL: truncated law (2)–(3), belief (A-1), utility u, best response, JP^U, threshold profile p(v)
-- statement:
--   The model of Yang, Shang and Liu: an observable single-server queue whose service rate is unknown to the arriving customers.
--
--   1. **Primitives and standing assumptions.** The service rate $\mu$ equals $\mu_H$ with prior probability $\gamma$ and $\mu_L$ with probability $1-\gamma$, where $\mu_H > \mu_L > 0$ and $\gamma \in (0,1)$. Customers arrive as a Poisson process of rate $\lambda > 0$, receive reward $R$ from service and pay $C > 0$ per unit of time in the system. Assumption 2 requires $R - C/\mu_L > 0$. The maximal queue length is $\bar N = \lfloor R\mu_H/C\rfloor$, and $\rho_X = \lambda/\mu_X$ for $X \in \{H, L\}$.
--
--   2. **Joining vectors.** The other customers' behaviour is a vector $p^- = (1, p^-_1, p^-_2, \dots)$ with $p^-_i \in [0,1]$: a customer who sees $i$ customers joins with probability $p^-_i$.
--
--   3. **Steady-state law, (2)–(3).** Given $\mu = \mu_X$, the queue length is a birth–death process on $\{0,\dots,\bar N\}$ with birth rate $\lambda p^-_n$ and death rate $\mu_X$, whose stationary law is
--   $$\pi_X(n,p^-) = \frac{\rho_X^n\prod_{i=0}^{n-1}p^-_i}{\sum_{j=0}^{\bar N}\rho_X^j\prod_{i=0}^{j-1}p^-_i}, \qquad 0 \le n \le \bar N,$$
--   and $\pi_X(n,p^-) = 0$ for $n > \bar N$.
--
--   4. **Belief, (A-1).** The posterior probability of high capacity at queue length $n$ is
--   $$\theta_n(p^-) = \frac{\gamma\,\pi_H(0,p^-)}{\gamma\,\pi_H(0,p^-) + (1-\gamma)\,\pi_L(0,p^-)\,(\rho_L/\rho_H)^n}.$$
--
--   5. **Utility and best response.** With $E(\theta) = \theta/\mu_H + (1-\theta)/\mu_L$, the expected utility of joining at queue length $n$ is $u(n,p^-) = R - C(n+1)\,E(\theta_n(p^-))$. The tagged customer's best response is $\tilde p_n(p^-) = 1$ if $n = 0$ or $u(n,p^-) \ge 0$, and $0$ otherwise.
--
--   6. **Ex-ante joining probability.**
--   $$JP^U(p^-) = \sum_{n=0}^{\bar N}\tilde p_n(p^-)\bigl(\gamma\,\pi_H(n,p^-) + (1-\gamma)\,\pi_L(n,p^-)\bigr).$$
--
--   7. **Threshold profile.** For $v \ge 0$, the profile $p^-(v)$ joins at queue lengths $\le \lfloor v\rfloor$, joins with probability $v - \lfloor v\rfloor$ at $\lfloor v\rfloor + 1$, and balks above. At an integer $v = k$ it is the threshold-$k$ vector. We write $\theta_n(v)$, $u(n,v)$ and $JP^U(v)$ for the quantities under $p^-(v)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** States are natural numbers and joining vectors are functions $\mathbb N \to \mathbb R$, of which only the coordinates $0,\dots,\bar N - 1$ enter the law. $\bar N$ is `Nat.floor`. The belief is defined by (A-1) rather than by Bayes' rule (1), because (1) is $0/0$ at a state of probability zero (for example at $n \ge 2$ under $v = 0$, where the paper evaluates $\theta_n(0)$); the two agree wherever (1) is defined (the milestone on (A-1)). The paper allows any joining probability at $u(n,p^-) = 0$; the formalization selects $1$, the reading of Assumption 1 ("join when the expected utility gain is non-negative"). $JP^U$ is written as a sum over all states; by Proposition 1 it equals the paper's form $\sum_{n<m}\pi(n) + p_m\pi(m)$ with $p_m = 1$. The positivity of $\lambda$ and $C$ is added to the paper's stated assumptions; both are implicit in the paper ($\rho_X = \lambda/\mu_X$ is a traffic intensity and $\bar N$ divides by $C$).
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), pp. 6–10, §3, §4.1, §4.2, Assumptions 1–2, eqs. (1)–(3), JP^U p. 9, threshold profile p. 10; Online Appendix p. 1 (PDF 25), (A-1)

import Mathlib

namespace FollowCrowd.Inference

/-- The primitives of the model (Yang–Shang–Liu, §3, p. 6): reward `R`, per-unit-time waiting cost
`C`, prior probability `γ` that the capacity is high, Poisson arrival rate `lam` (λ), and the two
possible service rates `muH` (µH) and `muL` (µL). -/
structure Params where
  R : ℝ
  C : ℝ
  γ : ℝ
  lam : ℝ
  muH : ℝ
  muL : ℝ

/-- Standing assumptions (§3, p. 6): `µH > µL > 0`, `γ ∈ (0,1)`, Assumption 2 (`R − C/µL > 0`);
added: `λ > 0` (a Poisson rate, `ρX = λ/µX`) and `C > 0` (a waiting cost, `N̄ = ⌊RµH/C⌋`). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.muL ∧ P.muL < P.muH ∧ 0 < P.γ ∧ P.γ < 1 ∧ 0 < P.lam ∧ 0 < P.C ∧ P.C / P.muL < P.R

/-- The maximal queue length `N̄ = ⌊R µH / C⌋` (p. 6). -/
noncomputable def Nbar (P : Params) : ℕ := ⌊P.R * P.muH / P.C⌋₊

/-- The traffic intensity `ρX = λ / µX` (p. 8). -/
noncomputable def rho (P : Params) (mu : ℝ) : ℝ := P.lam / mu

/-- A joining vector of the other customers, `p⁻ = (1, p⁻₁, …)` with every `p⁻ᵢ ∈ [0,1]` (p. 7).
Only the coordinates `0, …, N̄ − 1` enter the law (2)–(3). -/
def IsJoinVec (p : ℕ → ℝ) : Prop :=
  p 0 = 1 ∧ ∀ i, 0 ≤ p i ∧ p i ≤ 1

/-- The unnormalized weight `ρX^n ∏_{i=0}^{n-1} p⁻ᵢ` of state `n` in (2). -/
noncomputable def weight (P : Params) (mu : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  rho P mu ^ n * ∏ i ∈ Finset.range n, p i

/-- The steady-state law `πX(n, p⁻)` of (2)–(3) on `{0, …, N̄}`, given `µ = mu`: the weight of
state `n` divided by `∑_{j=0}^{N̄} ρX^j ∏_{i<j} p⁻ᵢ` (the `1 + ∑_{j=1}^{N̄}` of (3)); `0` above `N̄`. -/
noncomputable def stat (P : Params) (mu : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ≤ Nbar P then weight P mu p n / ∑ j ∈ Finset.range (Nbar P + 1), weight P mu p j else 0

/-- The updated belief `θn(p⁻)` of high capacity at queue length `n`, by (A-1) (Online Appendix
p. 1): `γ πH(0,p⁻) / (γ πH(0,p⁻) + (1−γ) πL(0,p⁻) (ρL/ρH)^n)`. It equals Bayes' rule (1) wherever
state `n` has positive probability, and is defined at every `n`. -/
noncomputable def theta (P : Params) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  P.γ * stat P P.muH p 0 /
    (P.γ * stat P P.muH p 0 + (1 - P.γ) * stat P P.muL p 0 * (rho P P.muL / rho P P.muH) ^ n)

/-- The expected sojourn time under belief `θ`: `θ/µH + (1−θ)/µL`. -/
noncomputable def meanSojourn (P : Params) (θ : ℝ) : ℝ :=
  θ / P.muH + (1 - θ) / P.muL

/-- The expected utility of joining at queue length `n` (p. 8):
`u(n, p⁻) = R − C (n+1) [θn(p⁻)/µH + (1 − θn(p⁻))/µL]`. -/
noncomputable def util (P : Params) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  P.R - P.C * ((n : ℝ) + 1) * meanSojourn P (theta P p n)

/-- The tagged customer's (pure) best response (p. 8, Assumption 1): join (`1`) at the empty
queue and whenever `u(n, p⁻) ≥ 0`, balk (`0`) otherwise. At `u = 0` the page allows any
probability; Assumption 1 ("join when the expected utility gain is non-negative") selects `1`. -/
noncomputable def bestResp (P : Params) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 ∨ 0 ≤ util P p n then 1 else 0

/-- The ex-ante joining probability `JP^U(p⁻)` (p. 9), written as the sum over all states
`n ∈ {0, …, N̄}` of the best response times `γ πH(n,p⁻) + (1−γ) πL(n,p⁻)`. -/
noncomputable def JP (P : Params) (p : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nbar P + 1),
    bestResp P p n * (P.γ * stat P P.muH p n + (1 - P.γ) * stat P P.muL p n)

/-- The threshold joining profile `p⁻(v)`, `v ≥ 0` (p. 10): join at queue lengths `≤ ⌊v⌋`,
join with probability `v − ⌊v⌋` at `⌊v⌋ + 1`, balk above. At an integer `v = k` it is the
threshold-`k` vector (join at `0, …, k`, balk above). -/
noncomputable def thrProfile (v : ℝ) (i : ℕ) : ℝ :=
  if i ≤ ⌊v⌋₊ then 1 else if i = ⌊v⌋₊ + 1 then v - ⌊v⌋₊ else 0

/-- `θn(v)`: the belief under the threshold profile `p⁻(v)`. -/
noncomputable def thetaV (P : Params) (v : ℝ) (n : ℕ) : ℝ := theta P (thrProfile v) n

/-- `u(n, v)`: the utility under the threshold profile `p⁻(v)`. -/
noncomputable def utilV (P : Params) (v : ℝ) (n : ℕ) : ℝ := util P (thrProfile v) n

/-- `JP^U(v)`: the ex-ante joining probability under the threshold profile `p⁻(v)`. -/
noncomputable def JPV (P : Params) (v : ℝ) : ℝ := JP P (thrProfile v)

end FollowCrowd.Inference


