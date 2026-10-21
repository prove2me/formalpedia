-- Prove2me | Definitions.Def_RatingsAdvert_AdInterval_Model
-- name    : RatingsAdvert_AdInterval_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:04.679819+00:00
-- url     : https://prove2.me/theorems/ed95827d-7936-410e-8937-31b2003e6d41
-- title:
--   §3–§3.1.2, pp. 8–15 — two-period targeted-advertising game: demands (1), (4), average rating (2), inferred quality (3), firm profit Π, PBE in the Benchmark, AR and Reviews cases
-- statement:
--   This file sets up the basic model of Fainmesser, Lauga and Ofek (§3) with every second-generation consumer aware of the product ($\gamma = 1$).
--
--   **Parameters.** A model is a triple $(\tau, \beta, A)$: $\tau$ is the consumers' cost of location mismatch, $\beta$ their marginal value of quality, and $A : \mathbb R \to \mathbb R$ the cost of advertising to an interval of size $z$. The *standing assumptions* of the section are
--
--   1. $0 < \tau < 1/5$ and $0 < \beta < 1/5$;
--   2. $A$ is twice continuously differentiable, $A(0) = 0$, and for every $z \in [0,1]$, $A'(z) > 0$ and $A''(z) > \tau/\beta$;
--   3. $A''(1) > 0.4$.
--
--   The *interiority* condition says that the advertising first-order conditions (7) and (8) have their roots inside $(0,1)$:
--   $$A'(0) < \Big(\frac{1+\beta}{2}\Big)^2 - \frac{\tau(1+\beta-\tau)}{2}, \qquad \Big(\frac{1+\beta-\tau}{2}\Big)^2 < A'(1).$$
--
--   **Demands and inference.** The firm advertises to an interval of size $z \in [0,1]$ at first-period price $p_1$; first-generation consumers do not see $z$ and hold a belief $z^e$. Quality $q$ is uniform on $[0,2]$. With these, first-period demand (1), the average net utility of first-generation buyers (2) and the second-period demands (4) are
--   $$D_1(z,p_1) = z(1+\beta - z^e\tau - p_1), \qquad \mu_1(z) = \frac{1 + \beta(2q-1) - (2z - z^e)\tau - p_1}{2},$$
--   $$D^0_2(p_2) = 1+\beta-\tau-p_2, \qquad D^{AR}_2(p_2) = 1+\beta q^e-\tau-p_2, \qquad D^R_2(p_2) = 1+\beta q-\tau-p_2 .$$
--   In the Average Rating (AR) case second-generation consumers infer quality from $\mu_1$, using their belief $z^e$; by (3) and footnote 10 the inferred quality is
--   $$q^e = \min\Big\{\max\Big\{0, \frac{\beta q - \tau(z - z^e)}{\beta}\Big\}, 2\Big\}.$$
--
--   **Profit and equilibrium.** The firm's total profit is $\Pi = p_1 D_1(z,p_1) + E_q\big(p_2 D_2(p_2)\big) - A(z)$, where $E_q f = \tfrac12\int_0^2 f(q)\,dq$. The second-period price is a number in the Benchmark case (nothing is learned), a function of realized quality $q$ in the Reviews case, and a function of inferred quality $q^e$ in the AR case. A triple $(z, p_1, p_2)$ is a pure-strategy perfect Bayesian equilibrium (PBE) of a case if
--
--   1. $z \in [0,1]$;
--   2. $p_2$ maximizes second-period profit $p\,D_2(p)$ of that case at every information value in $[0,2]$ (on and off the equilibrium path);
--   3. $(z,p_1)$ maximizes $\Pi$ over all $z' \in [0,1]$ and all prices $p'$, with consumers' belief held at the equilibrium value $z^e = z$ (footnote 11). In the AR case a deviation $z'$ changes the inferred quality to $q^e = \min\{\max\{0, (\beta q - \tau(z'-z))/\beta\}, 2\}$.
--
--   This is the common model of every statement of the mission.
--
--   **Formalization Note.** The closed forms (1), (2), (4) are derived in the paper's Technical Appendix, which is not part of the source; they are taken here as the definition of the model, for every real price, as the paper's first-order analysis uses them. The positivity of $\tau$ and $\beta$, the twice continuous differentiability of $A$ and the interiority condition are added: the page divides by $\beta$, uses $A'$ and $A''$, and assumes $A$ "sufficiently convex … to guarantee that the solution is interior" without quantifying it. $E_q$ is an interval integral divided by 2; at an equilibrium the integrand is continuous on $[0,2]$.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), pp. 8–15 (PDF 10–17), §3, §3.1.1–3.1.2, eqs. (1)–(4), footnotes 10–11

import Mathlib

namespace RatingsAdvert.AdInterval

/-- Parameters of the basic model (§3, pp. 8–11): `tau` is τ, the location-mismatch cost;
`beta` is β, the marginal sensitivity to quality; `A` is the advertising cost `A(z)`. -/
structure Params where
  tau : ℝ
  beta : ℝ
  A : ℝ → ℝ

/-- Standing assumptions of §3 (pp. 10–11): `τ, β < 1/5`; `A(0) = 0`, `A′(z) > 0`,
`A″(z) > τ/β` on `[0,1]`, `A″(1) > 0.4`. Added: `0 < τ`, `0 < β`, and `A` twice continuously
differentiable (the page uses `A′`, `A″`). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.tau ∧ P.tau < 1 / 5 ∧ 0 < P.beta ∧ P.beta < 1 / 5 ∧ ContDiff ℝ 2 P.A ∧ P.A 0 = 0 ∧
    (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < deriv P.A z) ∧
    (∀ z ∈ Set.Icc (0 : ℝ) 1, P.tau / P.beta < deriv (deriv P.A) z) ∧
    (2 / 5 : ℝ) < deriv (deriv P.A) 1

/-- Added, disclosed: "sufficiently convex … to guarantee that the solution is interior" (p. 10),
stated as: the first-order conditions (7) and (8) have their roots in `(0,1)`. -/
def Params.Interior (P : Params) : Prop :=
  deriv P.A 0 < ((1 + P.beta) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 ∧
    ((1 + P.beta - P.tau) / 2) ^ 2 < deriv P.A 1

/-- First-period demand (1): `D1(z, p1) = z(1 + β − z^e τ − p1)`; `z` actual interval,
`ze` the consumers' belief. -/
def D1 (P : Params) (z ze p1 : ℝ) : ℝ := z * (1 + P.beta - ze * P.tau - p1)

/-- Average net utility of first-generation buyers (2):
`μ1(z) = (1 + β(2q − 1) − (2z − z^e)τ − p1)/2`. -/
noncomputable def mu1 (P : Params) (q z ze p1 : ℝ) : ℝ :=
  (1 + P.beta * (2 * q - 1) - (2 * z - ze) * P.tau - p1) / 2

/-- Quality inferred from the average rating, (3) with footnote 10's clamp:
`q^e = min{max{0, (βq − τ(z − z^e))/β}, 2}`; `z` actual interval, `ze` the belief. -/
noncomputable def qe (P : Params) (q z ze : ℝ) : ℝ :=
  min (max 0 ((P.beta * q - P.tau * (z - ze)) / P.beta)) 2

/-- Second-period demand in the Benchmark case (4): `D^0_2(p2) = 1 + β − τ − p2`. -/
def D2Bench (P : Params) (p2 : ℝ) : ℝ := 1 + P.beta - P.tau - p2

/-- Second-period demand when quality information `x` is known (4): `x = q^e` gives `D^AR_2`,
`x = q` gives `D^R_2`: `1 + βx − τ − p2`. -/
def D2Info (P : Params) (x p2 : ℝ) : ℝ := 1 + P.beta * x - P.tau - p2

/-- Expectation over quality `q ~ U[0,2]`: `E_q f = (1/2) ∫₀² f(q) dq`. -/
noncomputable def expQ (f : ℝ → ℝ) : ℝ := (∫ q in (0 : ℝ)..2, f q) / 2

/-- Firm's total profit `Π` in the Benchmark case for first-period choice `(z, p1)` against the
belief `ze`, with second-period price `p2` (a constant). -/
def piBench (P : Params) (p2 : ℝ) (ze z p1 : ℝ) : ℝ :=
  p1 * D1 P z ze p1 + p2 * D2Bench P p2 - P.A z

/-- Firm's total expected profit `Π` in the Reviews case; `p2 : ℝ → ℝ` is the second-period
price as a function of the realized quality. -/
noncomputable def piRev (P : Params) (p2 : ℝ → ℝ) (ze z p1 : ℝ) : ℝ :=
  p1 * D1 P z ze p1 + expQ (fun q => p2 q * D2Info P q (p2 q)) - P.A z

/-- Firm's total expected profit `Π` in the AR case; `p2 : ℝ → ℝ` is the second-period price as
a function of the inferred quality `q^e`, which depends on the actual `z` and the belief `ze`. -/
noncomputable def piAR (P : Params) (p2 : ℝ → ℝ) (ze z p1 : ℝ) : ℝ :=
  p1 * D1 P z ze p1 +
    expQ (fun q => p2 (qe P q z ze) * D2Info P (qe P q z ze) (p2 (qe P q z ze))) - P.A z

/-- Pure-strategy PBE, Benchmark case: `p2` is optimal for `D^0_2`, and `(z, p1)` maximizes `Π`
over all `z' ∈ [0,1]`, `p'` with the consumers' belief fixed at the equilibrium `z`. -/
def IsPBEBench (P : Params) (z p1 p2 : ℝ) : Prop :=
  z ∈ Set.Icc (0 : ℝ) 1 ∧ (∀ p, p * D2Bench P p ≤ p2 * D2Bench P p2) ∧
    ∀ z' ∈ Set.Icc (0 : ℝ) 1, ∀ p', piBench P p2 z z' p' ≤ piBench P p2 z z p1

/-- Pure-strategy PBE, Reviews case: `p2 x` is optimal for `D^R_2` at every quality `x ∈ [0,2]`,
and `(z, p1)` maximizes `Π` with the belief fixed at `z`. -/
def IsPBERev (P : Params) (z p1 : ℝ) (p2 : ℝ → ℝ) : Prop :=
  z ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ p, p * D2Info P x p ≤ p2 x * D2Info P x (p2 x)) ∧
    ∀ z' ∈ Set.Icc (0 : ℝ) 1, ∀ p', piRev P p2 z z' p' ≤ piRev P p2 z z p1

/-- Pure-strategy PBE, AR case: `p2 x` is optimal for `D^AR_2` at every inferred quality
`x ∈ [0,2]`, and `(z, p1)` maximizes `Π` with the belief fixed at `z` (a deviation `z'` moves the
inferred quality to `q^e = (βq − τ(z' − z))/β`, clamped). -/
def IsPBEAR (P : Params) (z p1 : ℝ) (p2 : ℝ → ℝ) : Prop :=
  z ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ p, p * D2Info P x p ≤ p2 x * D2Info P x (p2 x)) ∧
    ∀ z' ∈ Set.Icc (0 : ℝ) 1, ∀ p', piAR P p2 z z' p' ≤ piAR P p2 z z p1

end RatingsAdvert.AdInterval


