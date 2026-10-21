-- Prove2me | Definitions.Def_PrivAcq_Central_Model
-- name    : PrivAcq_Central_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:35.264995+00:00
-- url     : https://prove2.me/theorems/3cc73b5e-3b0c-4dc4-8413-6b008855964c
-- title:
--   §2–§4.1, pp. 7–18 — data acquisition: type law, virtual cost ψ, class (22), MSE, cost (14), IC (17), IR (18), objective (16), program (23)
-- statement:
--   This file sets up the central-privacy data acquisition model of Fallah, Makhdoumi, Malekian and Ozdaglar.
--
--   **Users and types.** There are $n$ users. User $i$ has a privacy sensitivity (type) $c_i$, drawn independently from a distribution with density $f_i$ on an interval $[a_i, b_i]$ and cumulative distribution function $F_i(c) = \int_{a_i}^{c} f_i(x)\,dx$. The standing assumptions are $n > 0$, a common data variance $\mathrm{VAR} > 0$, and for each $i$: $0 < a_i < b_i$, $f_i$ continuous and strictly positive on $[a_i, b_i]$, $\int_{a_i}^{b_i} f_i = 1$. The type space is $\prod_i [a_i, b_i]$ and the type law is the product of the laws of the $c_i$. The **virtual cost** is
--   $$
--   \psi_i(c) = c + \frac{F_i(c)}{f_i(c)},
--   $$
--   and **Assumption 1** states that each $\psi_i$ is increasing on $[a_i, b_i]$.
--
--   **Mechanisms of class (22).** A direct mechanism specifies, as functions of the reported profile $c$, estimator weights $w_i(c)$, a Laplace parameter $\eta(c)$ (the estimator is $\hat\theta = \sum_i w_i(c) x_i + \mathrm{Laplace}(1/\eta(c))$), privacy losses $\varepsilon_i(c)$ and payments $t_i(c)$. Its mean square error is
--   $$
--   \mathrm{MSE}(c) = \frac{2}{\eta(c)^2} + \sum_{i=1}^n w_i(c)^2\,\mathrm{VAR}.
--   $$
--   An allocation $(w,\eta,\varepsilon)$ is admissible if it is measurable, and on every type profile $\eta(c) > 0$, $w_i(c) \ge 0$, $\sum_i w_i(c) = 1$ and $\eta(c) w_i(c) \le \varepsilon_i(c)$ (the constraints of (22)); the privacy losses are bounded; and the MSE is integrable under the type law, also with any one coordinate fixed to a report. An admissible mechanism additionally has measurable payments, integrable in the same sense.
--
--   **Interim quantities and constraints.** With the others reporting truthfully, user $i$ who reports $r$ faces the interim MSE $h_i(r) = \mathbb E_{c_{-i}}[\mathrm{MSE}(r, c_{-i})]$, the interim privacy loss $\bar\varepsilon_i(r) = \mathbb E_{c_{-i}}[\varepsilon_i(r, c_{-i})]$ and the interim payment $\bar t_i(r) = \mathbb E_{c_{-i}}[t_i(r, c_{-i})]$. The cost (14) of a user of type $c_i$ reporting $r$ is
--   $$
--   \mathrm{cost}_i(r, c_i) = \mathbb E_{c_{-i}}\big[\mathrm{MSE}(r, c_{-i}) + c_i\,\varepsilon_i(r, c_{-i}) - t_i(r, c_{-i})\big].
--   $$
--   Incentive compatibility (17) requires $\mathrm{cost}_i(c_i, c_i) \le \mathrm{cost}_i(r, c_i)$ for all types and reports in $[a_i, b_i]$; individual rationality (18) requires $\mathrm{cost}_i(c_i, c_i) \le \mathrm{VAR}$, the cost (15) of not participating. The platform's objective (16) is $\mathbb E_c[\mathrm{MSE}(c) + \sum_i t_i(c)]$.
--
--   **Program (23).** For a type profile $c$ and $y \in \mathbb R^n$ with $y \ge 0$ and $\sum_j y_j > 0$,
--   $$
--   \mathrm{obj}_{23}(c, y) = \frac{n+1}{\big(\sum_{j=1}^n y_j\big)^2}\Big(2 + \sum_{i=1}^n y_i^2\,\mathrm{VAR}\Big) + \sum_{i=1}^n \psi_i(c_i)\, y_i ,
--   $$
--   and $y$ is optimal if it minimizes $\mathrm{obj}_{23}(c,\cdot)$ over this feasible set.
--
--   **Payments (19) and the mechanism of Theorem 3.** For an allocation $(w,\eta,\varepsilon)$, the payment rule (19) with $d_i = 0$ in ex post form is $t_i(c) = \mathrm{MSE}(c) - \mathrm{VAR} + c_i\varepsilon_i(c) + \int_{c_i}^{b_i} \varepsilon_i(z, c_{-i})\,dz$. Given a selection $y^*(c)$ of optimal solutions of (23), the mechanism of Theorem 3 uses $\varepsilon^*_i(c) = y^*_i(c)$, $\eta^*(c) = \sum_j y^*_j(c)$, $w^*_i(c) = y^*_i(c)/\sum_j y^*_j(c)$ and these payments.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The paper takes $c_i \in \mathbb R_+$ and integrates to $\infty$; here types have compact support $[a_i,b_i]$ with $a_i > 0$ and continuous positive density, so that $\psi_i$ is defined and (23) attains its minimum; $\int_{c_i}^{\infty}$ becomes $\int_{c_i}^{b_i}$. The paper's Definition 3 asks $\varepsilon, t$ to be differentiable and $t \ge 0$; neither is imposed (the optimal $\varepsilon^*$ has kinks and optimal payments can be negative); measurability, bounded $\varepsilon$ and integrability are imposed instead. $w \ge 0$ and $\eta > 0$ are made explicit in class (22) ($\varepsilon_i = w_i\eta$ is the privacy level of Lemma 2 only for $w_i \ge 0$). The guard $\sum_j y_j > 0$ excludes $y = 0$, where Lean's $1/0 = 0$ would give a junk value. Interim expectations $\mathbb E_{c_{-i}}[g(r, c_{-i})]$ are written $\int g(\mathrm{update}(c, i, r))\,d(\text{type law})(c)$. The MSE is the closed form of p. 18, justified by the milestone `PrivAcq.Central.mse_linear_estimator`. Assumption 1's "increasing" is read as strictly increasing.
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, pp. 7–18: §2 p. 7 (data model), Definition 3 and (14) p. 14, (15)–(18) p. 15, interim quantities and (19) p. 16, ψ p. 17, (22) and Assumption 1 p. 17, (23) and the MSE display p. 18; payments: proof of Theorem 3, p. 45

import Mathlib

namespace PrivAcq.Central

open MeasureTheory

/-- The primitives of the data-acquisition model (§2 p. 7, §3 p. 13): the common variance `var`
of the data noise, and for each user `i` the support `[a i, b i]` and the density `f i` of the
privacy sensitivity `c_i`. -/
structure Setting (n : ℕ) where
  var : ℝ
  a : Fin n → ℝ
  b : Fin n → ℝ
  f : Fin n → ℝ → ℝ

variable {n : ℕ}

/-- Standing assumptions: at least one user, positive variance, and for each user a compact type
support `[a i, b i]` with `0 < a i < b i` on which `f i` is a continuous positive probability
density. -/
def Setting.Standing (S : Setting n) : Prop :=
  0 < n ∧ 0 < S.var ∧ ∀ i : Fin n, 0 < S.a i ∧ S.a i < S.b i ∧
    ContinuousOn (S.f i) (Set.Icc (S.a i) (S.b i)) ∧
    (∀ c ∈ Set.Icc (S.a i) (S.b i), 0 < S.f i c) ∧ ∫ x in S.a i..S.b i, S.f i x = 1

/-- The type space `∏ i [a i, b i]`. -/
def Setting.types (S : Setting n) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => Set.Icc (S.a i) (S.b i)

/-- The cumulative distribution function `F_i(c) = ∫_{a_i}^{c} f_i`. -/
noncomputable def Setting.cdf (S : Setting n) (i : Fin n) (c : ℝ) : ℝ :=
  ∫ x in S.a i..c, S.f i x

/-- The virtual cost `ψ_i(c) = c + F_i(c) / f_i(c)` (p. 17). -/
noncomputable def Setting.ψ (S : Setting n) (i : Fin n) (c : ℝ) : ℝ :=
  c + S.cdf i c / S.f i c

/-- Assumption 1 (p. 17): every virtual cost is (strictly) increasing on the type support. -/
def Setting.Assumption1 (S : Setting n) : Prop :=
  ∀ i : Fin n, StrictMonoOn (S.ψ i) (Set.Icc (S.a i) (S.b i))

/-- The law of the type profile `c = (c_1, …, c_n)`: independent coordinates, `c_i` with density
`f i` on `[a i, b i]`. -/
noncomputable def Setting.typeLaw (S : Setting n) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => (volume.restrict (Set.Icc (S.a i) (S.b i))).withDensity
    fun c => ENNReal.ofReal (S.f i c)

/-- A direct mechanism with an estimator of the central class (22): as functions of the reported
type profile, the estimator weights `w`, the Laplace parameter `η` (noise `Laplace(1/η)`), the
privacy losses `ε` and the payments `t`. -/
structure Mech (n : ℕ) where
  w : (Fin n → ℝ) → Fin n → ℝ
  η : (Fin n → ℝ) → ℝ
  ε : (Fin n → ℝ) → Fin n → ℝ
  t : (Fin n → ℝ) → Fin n → ℝ

/-- The mean square error of the estimator `∑ w_i(c) x_i + Laplace(1/η(c))` (p. 18):
`MSE(c) = 2/η(c)² + ∑ w_i(c)² var`. -/
noncomputable def mse (S : Setting n) (M : Mech n) (c : Fin n → ℝ) : ℝ :=
  2 / (M.η c) ^ 2 + ∑ i, (M.w c i) ^ 2 * S.var

/-- Admissible allocation of class (22): measurable weights, Laplace parameter and privacy losses;
on every type profile `η > 0`, `w ≥ 0`, `∑ w = 1`, `η w_i ≤ ε_i`; privacy losses bounded; the MSE
integrable under the type law, also with any one coordinate fixed to a report. -/
def AdmissibleAlloc (S : Setting n) (M : Mech n) : Prop :=
  Measurable M.w ∧ Measurable M.η ∧ Measurable M.ε ∧
  (∀ c ∈ S.types, 0 < M.η c ∧ (∀ i, 0 ≤ M.w c i) ∧ ∑ i, M.w c i = 1 ∧
      ∀ i, M.η c * M.w c i ≤ M.ε c i) ∧
  (∃ B : ℝ, ∀ c ∈ S.types, ∀ i, M.ε c i ≤ B) ∧
  Integrable (mse S M) S.typeLaw ∧
  ∀ i : Fin n, ∀ r ∈ Set.Icc (S.a i) (S.b i),
    Integrable (fun c => mse S M (Function.update c i r)) S.typeLaw

/-- Admissible mechanism: an admissible allocation together with measurable payments that are
integrable under the type law, also with any one coordinate fixed to a report. -/
def Admissible (S : Setting n) (M : Mech n) : Prop :=
  AdmissibleAlloc S M ∧ Measurable M.t ∧ (∀ i, Integrable (fun c => M.t c i) S.typeLaw) ∧
  ∀ i : Fin n, ∀ r ∈ Set.Icc (S.a i) (S.b i),
    Integrable (fun c => M.t (Function.update c i r) i) S.typeLaw

/-- Interim expected MSE `h_i(r) = E_{c₋ᵢ}[MSE(r, c₋ᵢ)]`. -/
noncomputable def interimMse (S : Setting n) (M : Mech n) (i : Fin n) (r : ℝ) : ℝ :=
  ∫ c, mse S M (Function.update c i r) ∂S.typeLaw

/-- Interim privacy loss `ε̄_i(r) = E_{c₋ᵢ}[ε_i(r, c₋ᵢ)]` (p. 16). -/
noncomputable def interimEps (S : Setting n) (M : Mech n) (i : Fin n) (r : ℝ) : ℝ :=
  ∫ c, M.ε (Function.update c i r) i ∂S.typeLaw

/-- Interim payment `t̄_i(r) = E_{c₋ᵢ}[t_i(r, c₋ᵢ)]` (p. 16). -/
noncomputable def interimPay (S : Setting n) (M : Mech n) (i : Fin n) (r : ℝ) : ℝ :=
  ∫ c, M.t (Function.update c i r) i ∂S.typeLaw

/-- The cost (14) of user `i` with true type `ci` who reports `r` while the others report truthfully:
`E_{c₋ᵢ}[MSE(r, c₋ᵢ) + ci ε_i(r, c₋ᵢ) − t_i(r, c₋ᵢ)]`. -/
noncomputable def interimCost (S : Setting n) (M : Mech n) (i : Fin n) (r ci : ℝ) : ℝ :=
  ∫ c, (mse S M (Function.update c i r) + ci * M.ε (Function.update c i r) i
      - M.t (Function.update c i r) i) ∂S.typeLaw

/-- Incentive compatibility (17), for types and reports in the support. -/
def IC (S : Setting n) (M : Mech n) : Prop :=
  ∀ i : Fin n, ∀ ci ∈ Set.Icc (S.a i) (S.b i), ∀ r ∈ Set.Icc (S.a i) (S.b i),
    interimCost S M i ci ci ≤ interimCost S M i r ci

/-- Individual rationality (18): truthful participation costs at most the outside option `var`
of (15). -/
def IR (S : Setting n) (M : Mech n) : Prop :=
  ∀ i : Fin n, ∀ ci ∈ Set.Icc (S.a i) (S.b i), interimCost S M i ci ci ≤ S.var

/-- The platform's objective (16): `E_c[MSE(c) + ∑ t_i(c)]`. -/
noncomputable def objective (S : Setting n) (M : Mech n) : ℝ :=
  ∫ c, (mse S M c + ∑ i, M.t c i) ∂S.typeLaw

/-- The objective of program (23) at the type profile `c`:
`(n+1)/(∑ y_j)² · (2 + ∑ y_i² var) + ∑ ψ_i(c_i) y_i`. -/
noncomputable def obj23 (S : Setting n) (c y : Fin n → ℝ) : ℝ :=
  ((n : ℝ) + 1) / (∑ j, y j) ^ 2 * (2 + ∑ i, (y i) ^ 2 * S.var) + ∑ i, S.ψ i (c i) * y i

/-- Feasible set of (23): `y ≥ 0`, with `∑ y > 0` so that the objective is defined. -/
def feas23 : Set (Fin n → ℝ) := {y | (∀ i, 0 ≤ y i) ∧ 0 < ∑ j, y j}

/-- `y` is an optimal solution of (23) at the type profile `c`. -/
def IsOpt23 (S : Setting n) (c y : Fin n → ℝ) : Prop :=
  y ∈ feas23 ∧ ∀ y' ∈ (feas23 : Set (Fin n → ℝ)), obj23 S c y ≤ obj23 S c y'

/-- The mechanism `M` with its payments replaced by the ex post form of (19) with `d_i = 0`:
`t_i(c) = MSE(c) − var + c_i ε_i(c) + ∫_{c_i}^{b_i} ε_i(z, c₋ᵢ) dz`. -/
noncomputable def withPayments (S : Setting n) (M : Mech n) : Mech n where
  w := M.w
  η := M.η
  ε := M.ε
  t c i := mse S M c - S.var + c i * M.ε c i +
    ∫ z in c i..S.b i, M.ε (Function.update c i z) i

/-- The mechanism of Theorem 3 built from a selection `ystar` of solutions of (23):
`ε_i(c) = y*_i(c)`, `η(c) = ∑ y*_j(c)`, `w_i(c) = y*_i(c) / ∑ y*_j(c)`, payments (19) with `d_i = 0`. -/
noncomputable def optMech (S : Setting n) (ystar : (Fin n → ℝ) → Fin n → ℝ) : Mech n :=
  withPayments S
    { w := fun c i => ystar c i / ∑ j, ystar c j
      η := fun c => ∑ j, ystar c j
      ε := ystar
      t := fun _ _ => 0 }

end PrivAcq.Central


