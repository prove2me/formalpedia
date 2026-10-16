-- Prove2me | Definitions.Def_CourierDispatch_Exogenous_Setting
-- name    : CourierDispatch_Exogenous_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:41.051349+00:00
-- url     : https://prove2.me/theorems/ae7d3243-3721-42fe-ab23-a1644c8ca50c
-- title:
--   §3, pp. 7–12 — the disk delivery model: μ_D, C_D (4)–(6), μ_B (9), the C_B bracket (10), the expected waits W_D (5), W_B (12), the revenue (2) and the bracket of (A.1)
-- statement:
--   A vendor sits at the centre of a disk of radius $r>0$ and serves delivery orders with one courier of unit speed. Write $\lambda$ for the demand rate, $c$ for the customers' wait-cost rate, and $\Lambda r^2$ for the potential arrival rate. This file fixes the closed-form objects of the model.
--
--   1. **Dedicated delivery** (one order per round trip, an M/G/1 queue): service rate and variability
--   $$\mu_D=\frac{3}{4r},\qquad C_D=\frac98 .$$
--   2. **Batch delivery** (two orders per trip): service rate
--   $$\mu_B=\frac{45\pi}{4r(32+15\pi)} .$$
--   3. The normalized stability bounds $T_1=\mu_D r=\tfrac34$ and $T_2=2\mu_B r=\dfrac{45\pi}{2(32+15\pi)}\approx 0.8934$: for positive demand, dedicated delivery uses $0<\lambda r<T_1$ and batch delivery uses $0<\lambda r<T_2$. At zero demand, the batch wait diverges.
--   4. The batch variability coefficient $C_B$, which the paper obtains only numerically ($C_B\approx 0.583$), is represented by a real parameter. The predicate CBRange states the disclosed bracket $0.58\le C_B\le 0.59$; a theorem must assume it when needed.
--   5. The **expected waits**, as the paper defines them:
--   $$W_D(\lambda,\mu,C)=\frac{\lambda}{\mu(\mu-\lambda)}\cdot\frac C2,\qquad W_B(\lambda,\mu,C)=\frac1{2\lambda}+\frac{\lambda}{\mu(2\mu-\lambda)}\cdot\frac C2+\frac r3 ,$$
--   where $r/3=\mathbb E[X_D]/4$ is the expected extra delay of the second customer in a batch.
--   6. The **revenue rate** at positive demand rate $\lambda\le\Lambda r^2$ and expected wait $w$:
--   $$V(\lambda,w)=\lambda\Big[F^{-1}\Big(1-\frac{\lambda}{\Lambda r^2}\Big)-c\,w\Big],$$
--   with $F$ the c.d.f. of the customers' valuations.
--   7. The bracket of (A.1),
--   $$f_A(a)=\frac{a^2C_D}{2T_1(T_1-a)}-\frac12-\frac{a^2C_B}{T_2(T_2-a)}-\frac a3 ,$$
--   so that the paper's $f(a)$ equals $f_A(a)/\lambda$.
--
--   These objects are shared by every statement of the mission: the threshold results compare $W_D(\lambda,\mu_D,C_D)$ with $W_B(\lambda,\mu_B,C_B)$ and the corresponding revenues.
--
--   **Formalization Note** `lam` is $\lambda$ and `Lam` is $\Lambda$. The inverse c.d.f. $F^{-1}$ is represented by a supplied function `Q : ℝ → ℝ`. $W_B$ takes the radius $r$ as an explicit first argument. The waits are total functions on $\mathbb R$; at $\lambda=\mu$ in $W_D$, or $\lambda=0$ and $\lambda=2\mu$ in $W_B$, Lean's division by zero gives values outside the queueing model. The bracket $0.58\le C_B\le 0.59$ replaces the paper's numerical value $0.583$ and contains it.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), pp. 8–12, (2), (4)–(6), (9), (10), (12); Online Appendix p. 1, (A.1)–(A.2)

import Mathlib

namespace CourierDispatch.Exogenous

/-- Dedicated service rate `μ_D = 1 / E[X_D] = 3 / (4 r)` on a disk of radius `r`
(Chen, Hu, SSRN 3675063, p. 10, (4)). -/
noncomputable def muD (r : ℝ) : ℝ := 3 / (4 * r)

/-- `C_D = 1 + (E[X_D²] − E[X_D]²) / E[X_D]² = 9/8` (p. 10, (6)). -/
noncomputable def CD : ℝ := 9 / 8

/-- Batch service rate `μ_B = 1 / E[X_B] = 45π / (4 r (32 + 15π))` (p. 11, (9)). -/
noncomputable def muB (r : ℝ) : ℝ := 45 * Real.pi / (4 * r * (32 + 15 * Real.pi))

/-- `T₁ = μ_D r = 3/4` (Online Appendix p. 1, (A.2)): dedicated is stable iff `λ r < T₁`. -/
noncomputable def TD : ℝ := 3 / 4

/-- `T₂ = 2 μ_B r = 45π / (2 (32 + 15π))` (Online Appendix p. 1, (A.2)): batch is stable iff
`λ r < T₂`. -/
noncomputable def TB : ℝ := 45 * Real.pi / (2 * (32 + 15 * Real.pi))

/-- The standing bracket on the batch variability coefficient `C_B ≈ 0.583` (p. 11, (10)),
which the paper obtains only by numerical integration (footnote 5): `0.58 ≤ C_B ≤ 0.59`. -/
def CBRange (CB : ℝ) : Prop := 58 / 100 ≤ CB ∧ CB ≤ 59 / 100

/-- Expected wait under dedicated delivery (p. 10, (5)):
`W_D(λ, μ, C) := λ / (μ (μ − λ)) · C / 2`. Here `lam` is `λ`. -/
noncomputable def WD (lam mu C : ℝ) : ℝ := lam / (mu * (mu - lam)) * (C / 2)

/-- Expected wait under batch delivery (p. 12, (12)):
`W_B(λ, μ, C) := 1/(2λ) + λ / (μ (2μ − λ)) · C / 2 + r / 3`, where `r / 3 = E[X_D] / 4`.
The radius `r` is an explicit argument. -/
noncomputable def WB (r lam mu C : ℝ) : ℝ :=
  1 / (2 * lam) + lam / (mu * (2 * mu - lam)) * (C / 2) + r / 3

/-- Revenue rate (p. 8, (2)): `V(λ, w) = λ [F⁻¹(1 − λ/(Λ r²)) − c w]`, where `Q` stands for the
inverse c.d.f. `F⁻¹` of the valuations and `Lam` for `Λ`. -/
noncomputable def V (Q : ℝ → ℝ) (Lam r c lam w : ℝ) : ℝ :=
  lam * (Q (1 - lam / (Lam * r ^ 2)) - c * w)

/-- The bracket of (A.1) (Online Appendix p. 1), with `T₁ = TD`, `T₂ = TB`, `C₁ = CD`, `C₂ = CB`:
`a² C₁ / (2 T₁ (T₁ − a)) − 1/2 − a² C₂ / (T₂ (T₂ − a)) − a/3`.
The paper's `f(a)` is `(1/λ)` times this bracket. -/
noncomputable def fA (CB a : ℝ) : ℝ :=
  a ^ 2 * CD / (2 * TD * (TD - a)) - 1 / 2 - a ^ 2 * CB / (TB * (TB - a)) - a / 3

end CourierDispatch.Exogenous


