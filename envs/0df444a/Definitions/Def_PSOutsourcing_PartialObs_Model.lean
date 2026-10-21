-- Prove2me | Definitions.Def_PSOutsourcing_PartialObs_Model
-- name    : PSOutsourcing_PartialObs_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:19.710003+00:00
-- url     : https://prove2.me/theorems/d7cb1857-6c1f-48aa-86d7-53c7d85043ef
-- title:
--   §3, §5, pp. 8–20 — service cost and revenue, lognormal belief drift d = ξd^b, benchmark payment, per-period value of outsourcing, erf
-- statement:
--   This file fixes the single-period model of product service outsourcing under partial observability used in §5 of Wang, Li, Ma & Zhang.
--
--   **Parameters.** A parameter record $P$ collects: the base unit cost $C$, the environment sensitivity $\beta$, the provider's cost efficiency $\alpha$, the satisfaction rate $\lambda$, the expected penalty $\pi$ of an unsatisfied service encounter, the product values $v$ (in-house) and $v^o$ (outsourced), the fixed target resource level $\bar k$, and the brand's belief $d^b$ about the service environment. The **standing assumptions** are
--   $$
--   C>0,\quad \beta>0,\quad 0<\alpha\le 1,\quad \lambda>0,\quad \pi\ge 0,\quad v\le v^o,\quad \bar k>0,\quad d^b>0 .
--   $$
--
--   **Model primitives.** Customer satisfaction is $\theta(k)=1-e^{-\lambda k}$; the in-house resource cost is $c(k,d)=C\,k(1+\beta d)$ and the provider's cost is $c^S(k,d)=\alpha\,c(k,d)$. Revenues are $R(k)=v-\pi(1-\theta(k))$ (eq. (1)) and $R^o(k)=v^o-\pi(1-\theta(k))$. The period profit under direct service is $G(k,d)=R(k)-c(k,d)$, and under outsourcing with payment $w$ it is $G^o(k,w)=R^o(k)-w$.
--
--   **The error function** is $\operatorname{erf}(x)=\frac{2}{\sqrt\pi}\int_0^x e^{-t^2}\,dt$.
--
--   **Partial observability.** The unobserved cumulative shock $\xi^b$ is lognormal with mean $1$ and variance parameter $s^2$ (the variance of $\ln\xi^b$). It is represented through a standard normal variable $Z\sim N(0,1)$ as
--   $$
--   \xi_s(Z)=\exp\!\big(sZ-s^2/2\big),
--   $$
--   and the true environment is $d=\xi_s(Z)\,d^b$.
--
--   **Benchmark payment** (proof of Proposition 4(a)): the brand pays $c^S(\bar k,d^b)$ when $d\le d^b$ and $c^S(\bar k,d)$ when $d>d^b$.
--
--   **Value of outsourcing.** For a variance parameter $s$,
--   $$
--   \Delta(s)=\mathbb E\big[G^o(\bar k,w(d))-G(\bar k,d)\big],\qquad \Delta_{\mathrm{full}}(s)=\mathbb E\big[G^o(\bar k,c^S(\bar k,d))-G(\bar k,d)\big],
--   $$
--   the expectation being over $Z\sim N(0,1)$ with $d=\xi_s(Z)d^b$; $w(d)$ is the benchmark payment and $\Delta_{\mathrm{full}}$ uses the full-observability payment. Further, $\operatorname{driftProb}(s,X)=\mathbb P(d^b-d\ge X)$, and
--   $$
--   \operatorname{condLoss}(s)=\frac{1}{\mathbb P(\xi_s\le 1)}\int_{\{\xi_s\le 1\}}\big(c^S(\bar k,d^b)-c^S(\bar k,d)\big)\,d\mathbb P ,
--   $$
--   the conditional expected overpayment given $d\le d^b$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** All quantities are real numbers. The paper allows $\beta\ge0$; the standing predicate requires $\beta>0$ and $\bar k>0$, without which nothing depends on the environment and Proposition 4(b) fails. $\Delta$ is the expected per-period value of outsourcing in the §5 benchmark with the fixed target level $\bar k$ (p. 18): with $\bar k$ fixed there is no decision left in a period, and the proof of Proposition 4 argues period by period. The tie $d=d^b$ has probability zero; the payment rule puts it on the $d\le d^b$ side.
-- source:
--   Wang, Li, Ma & Zhang, Product service outsourcing: impact of environment uncertainty and partial observability, accepted manuscript (MSOM 2024, doi:10.1287/msom.2022.0222), pp. 8–20 (PDF 8–20) and pp. A-6–A-7 (PDF 38–39); §3.1 p. 8 (θ), p. 9 (c(k,d)), eq. (1) p. 10, §3.3 p. 12 (d_i = ξ^b_i d^b_i), §3.6 pp. 13–15 (G, c^S = αc, v^o ≥ v, R^o, G^o), p. 18 (k_i = k̄), §5 p. 19, proofs of Lemma 3 and Proposition 4

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

/-- The error function `erf x = (2/√π) ∫₀ˣ e^{-t²} dt` (not in Mathlib). -/
noncomputable def erf (x : ℝ) : ℝ := 2 / Real.sqrt Real.pi * ∫ t in (0:ℝ)..x, Real.exp (-t ^ 2)

/-- The model parameters of §3 (pp. 8–15) and p. 18 of Wang, Li, Ma & Zhang. -/
structure Params where
  /-- `C`, the base unit cost of the resource. -/
  C : ℝ
  /-- `β`, the sensitivity of resource cost to the service environment. -/
  β : ℝ
  /-- `α`, the third-party provider's cost efficiency, `c^S = α c`. -/
  α : ℝ
  /-- `λ` in `θ(k) = 1 - e^{-λk}`. -/
  lam : ℝ
  /-- `π`, the expected penalty of an unsatisfied service encounter. -/
  pen : ℝ
  /-- `v`, the product value under direct (in-house) service. -/
  v : ℝ
  /-- `v^o`, the product value under outsourcing. -/
  vo : ℝ
  /-- `k̄`, the fixed target resource level. -/
  kbar : ℝ
  /-- `d^b_i`, the brand's belief about the service environment. -/
  db : ℝ

/-- Standing assumptions of §3 and §5. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.C ∧ 0 < P.β ∧ 0 < P.α ∧ P.α ≤ 1 ∧ 0 < P.lam ∧ 0 ≤ P.pen ∧ P.v ≤ P.vo ∧
    0 < P.kbar ∧ 0 < P.db

/-- Expected customer satisfaction `θ(k) = 1 - e^{-λk}`. -/
noncomputable def theta (P : Params) (k : ℝ) : ℝ := 1 - Real.exp (-(P.lam * k))

/-- In-house resource cost `c(k,d) = C·k(1 + βd)`. -/
def cost (P : Params) (k d : ℝ) : ℝ := P.C * k * (1 + P.β * d)

/-- Provider's resource cost `c^S(k,d) = α c(k,d)`. -/
def costS (P : Params) (k d : ℝ) : ℝ := P.α * cost P k d

/-- Revenue under direct service, eq. (1): `R(k) = v - π(1 - θ(k))`. -/
noncomputable def rev (P : Params) (k : ℝ) : ℝ := P.v - P.pen * (1 - theta P k)

/-- Revenue under outsourcing: `R^o(k) = v^o - π(1 - θ(k))`. -/
noncomputable def revO (P : Params) (k : ℝ) : ℝ := P.vo - P.pen * (1 - theta P k)

/-- Period profit under direct service: `G(k,d) = R(k) - c(k,d)`. -/
noncomputable def G (P : Params) (k d : ℝ) : ℝ := rev P k - cost P k d

/-- Period profit under outsourcing with payment `w`: `G^o(k,w) = R^o(k) - w`. -/
noncomputable def Go (P : Params) (k w : ℝ) : ℝ := revO P k - w

/-- `ξ^b_i`: the mean-one lognormal with variance parameter `s²`, as a function of a
standard normal draw `z`: `ξ_s(z) = exp(s z - s²/2)`. -/
noncomputable def xi (s z : ℝ) : ℝ := Real.exp (s * z - s ^ 2 / 2)

/-- Benchmark payment (proof of Proposition 4(a)): the brand pays `c^S(k̄, d^b)`, and pays
`c^S(k̄, d)` when the true environment `d` exceeds the belief `d^b`. -/
noncomputable def payment (P : Params) (d : ℝ) : ℝ :=
  if d ≤ P.db then costS P P.kbar P.db else costS P P.kbar d

/-- `Δ`: expected per-period value of outsourcing under partial observability with variance
parameter `s²`, the true environment being `d = ξ_s · d^b`. -/
noncomputable def delta (P : Params) (s : ℝ) : ℝ :=
  ∫ z, (Go P P.kbar (payment P (xi s z * P.db)) - G P P.kbar (xi s z * P.db))
    ∂(gaussianReal 0 1)

/-- The same expected per-period value under full observability (payment `c^S(k̄, d)`). -/
noncomputable def deltaFull (P : Params) (s : ℝ) : ℝ :=
  ∫ z, (Go P P.kbar (costS P P.kbar (xi s z * P.db)) - G P P.kbar (xi s z * P.db))
    ∂(gaussianReal 0 1)

/-- `P(d^b - d ≥ X | s)`, with `d = ξ_s · d^b`. -/
noncomputable def driftProb (P : Params) (s X : ℝ) : ℝ :=
  (gaussianReal 0 1).real {z | X ≤ P.db - xi s z * P.db}

/-- `E[c^S(k̄,d^b) - c^S(k̄,d) | d ≤ d^b]`, i.e. `(1/F(1)) ∫_{ξ ≤ 1} (…) dF`. -/
noncomputable def condLoss (P : Params) (s : ℝ) : ℝ :=
  (∫ z in {z | xi s z ≤ 1}, (costS P P.kbar P.db - costS P P.kbar (xi s z * P.db))
      ∂(gaussianReal 0 1))
    / (gaussianReal 0 1).real {z | xi s z ≤ 1}

end PSOutsourcing.PartialObs


