-- Prove2me | Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
-- name    : LostSalesExpGap_ConstOrder_ConstantOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:44.767224+00:00
-- url     : https://prove2.me/theorems/149e93d7-5b77-4142-bd47-ad2c45cea975
-- title:
--   Sec. 2.2–2.3, Sec. 3, pp. 6–7, 10–11 — the constant-order policy π_r, C(π_r), E[I^r_∞], E[I^r_L], C_L(r), r_L, r∞, φ, γ, 1/ϑ, g, 𝔣_d
-- statement:
--   This file sets up the objects of Xin and Goldberg's analysis of constant-order policies for the periodic-review lost-sales inventory model with lead time $L\ge1$.
--
--   **The model.** Demands $D_1,D_2,\dots$ are i.i.d. copies of a nonnegative random variable $D$ with law $\mathcal D$, finite mean $\mathbb E[D]>0$; $h>0$ is the unit holding cost and $p>0$ the unit lost-sales penalty. The system starts empty ($I_1=0$, $\mathbf x_1=\mathbf 0$). In each period the oldest pipeline order arrives, a new order is placed, demand is realized, and the cost $C_t=h(I_t+x_{1,t}-D_t)^++p(I_t+x_{1,t}-D_t)^-$ is incurred. The long-run average cost of a policy $\pi$ is $C(\pi)=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\mathbb E[C^\pi_t]$ and $\mathrm{OPT}(L)=\inf_\pi C(\pi)$. All of this is the published model `CappedBaseStock`.
--
--   **Constant-order policies.** For $r\ge0$, the policy $\pi_r$ orders $r$ in every period; $C(\pi_r)$ is its long-run average cost, in $[0,\infty]$. With $S_j=\sum_{i=1}^jD_i$,
--   $$
--   I^r_\infty=\sup_{j\ge0}(jr-S_j),\qquad I^r_L=\max_{j=0,\dots,L}(jr-S_j),\qquad C_L(r)=h\,\mathbb E[I^r_L]+p\,\mathbb E[D]-p\,r .
--   $$
--   $\mathbb E[I^r_\infty]\in[0,\infty]$ and $\mathbb E[I^r_L]$ is a finite real.
--
--   **Best constants.** $r_\infty$ is the infimum of the set of minimizers of $C(\pi_r)$ over $0\le r\le\mathbb E[D]$, and $r_L$ is the infimum of the set of minimizers of $C_L(r)$ over the same interval.
--
--   **The rate.** For $\theta\ge0$,
--   $$
--   \phi(\theta)=e^{\theta r_\infty}\,\mathbb E[e^{-\theta D}],\qquad \gamma=\inf_{\theta\ge0}\phi(\theta),
--   $$
--   and $\vartheta$ is the supremum of the minimizers of $\phi$ on $[0,\infty)$, with $\vartheta=\infty$ when the infimum is not attained; the file records $1/\vartheta$, with $1/\infty=0$.
--
--   **Newsvendor cost.** $g=\inf_{x\in\mathbb R}\mathbb E[h(x-D)^++p(x-D)^-]$.
--
--   **Observation 1's function.** For $\mathbf d,\boldsymbol\chi\in\mathbb R^L$ and $I\in\mathbb R$,
--   $$
--   \mathfrak f_{\mathbf d}(\chi_1,\dots,\chi_L,I)=\max_{j=0,\dots,L}\Big(\sum_{i=1}^j(\chi_{L+1-i}-d_{L+1-i})+\delta_{j,L}I\Big).
--   $$
--
--   **Exponential-demand constants.** $\tau_{p,h}=\sqrt{h/(2p+h)}$ and $\gamma_{p,h}=(1-\tau_{p,h})e^{\tau_{p,h}}$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Time is zero-based and a demand path $d:\mathbb N\to[0,\infty)$ has $d(i-1)=D_i$. $C(\pi_r)$ is the model's `policyCost` of the constant policy, not formula (3); $\mathbb E[I^r_\infty]$ is a lower integral in $[0,\infty]$ of the published `supWalk`; $\mathbb E[I^r_L]$ is a Bochner integral of the published `finiteInventory`, whose integrand lies in $[0,Lr]$. $r_\infty$ and $r_L$ are `sInf` of the argmin sets; that these sets are nonempty is a theorem of the mission, not an assumption. $\gamma$ is an infimum over $[0,\infty)$ of values $\ge0$. $1/\vartheta$ is $(\sup S)^{-1}$ for the minimizer set $S$ when $S$ is nonempty and bounded, and $0$ otherwise (the paper's $\vartheta=\infty$ and $1/\infty=0$, p. 6). The objects are defined from the full parameter record (which includes $L$); that $r_\infty,\gamma,\vartheta$ do not depend on $L$ follows from eq. (3) and the existence result of Sec. 2.2.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Sec. 2.1–2.3, pp. 4–7; Sec. 3, pp. 10–11; Sec. 5.1, p. 15

import Mathlib
import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model
import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-!
Xin & Goldberg, *Optimality gap of constant-order policies decays exponentially in the lead time
for lost sales models*, arXiv:1409.1499v2, Sec. 2.1–2.3 (pp. 4–7), Sec. 3 (pp. 10–11): the
constant-order policy `π_r` and its long-run cost `C(π_r)`, the expectations `E[I^r_∞]` and
`E[I^r_L]`, the finite-horizon cost `C_L(r)`, the best constants `r∞` and `r_L`, the function `φ`,
the rate `γ`, the reciprocal `1/ϑ`, the newsvendor cost `g`, and the function `𝔣_d` of
Observation 1.

The lost-sales system is the published `CappedBaseStock` model: `P : DemandLaw` is the demand law
𝒟 (a probability law on `[0, ∞)` with finite positive mean), `c : Parameters` carries the lead
time `c.L = L ≥ 1`, the holding cost `c.h = h > 0` and the lost-sales penalty `c.p = p > 0`. Time
is zero-based (Lean period `t` is the paper's period `t + 1`), the system starts empty, and a
demand path `d : ℕ → ℝ≥0` has `d (i - 1) = D_i`.
-/

/-- The constant-order policy `π_r` (p. 6): it orders `r` in every period, whatever the history. -/
def constOrderPolicy (r : ℝ≥0) : CappedBaseStock.AdmissiblePolicy :=
  ⟨fun _ _ => r, fun _ => measurable_const⟩

/-- `C(π_r)` (p. 5), the long-run average cost of `π_r` from the empty initial state, in `[0, ∞]`.
It is the model's `policyCost`, not formula (3). Only `r ∈ [0, E[D]]` is ever used; a negative `r`
is read as `0`. -/
def constCost (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) (r : ℝ) : ℝ≥0∞ :=
  CappedBaseStock.policyCost P c (constOrderPolicy r.toNNReal)

/-- `E[I^r_∞] = E[sup_{j ≥ 0} (j r − Σ_{i=1}^j D_i)]` (p. 6), a lower integral in `[0, ∞]`. -/
def EIinf (P : CappedBaseStock.DemandLaw) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, LostSalesConstantOrder.LargeLeadTime.supWalk r.toNNReal d
    ∂CappedBaseStock.demandPathLaw P

/-- `E[I^r_m] = E[max_{j=0,…,m} (j r − Σ_{i=1}^j D_i)]` (p. 11). The integrand is `≥ 0` and, for
`r ≥ 0`, at most `m r`, so the Bochner integral is the true expectation. -/
def EIL (P : CappedBaseStock.DemandLaw) (r : ℝ) (m : ℕ) : ℝ :=
  ∫ d, CappedBaseStock.finiteInventory d r m ∂CappedBaseStock.demandPathLaw P

/-- `C_m(r) = h E[I^r_m] + p E[D] − p r` (p. 11). -/
def CL (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) (r : ℝ) (m : ℕ) : ℝ :=
  c.h * EIL P r m + c.p * CappedBaseStock.mean P - c.p * r

/-- The set of minimizers of `C_m(r)` over `0 ≤ r ≤ E[D]` (p. 11). -/
def argminCL (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) (m : ℕ) : Set ℝ :=
  {r | r ∈ Set.Icc 0 (CappedBaseStock.mean P) ∧
    ∀ r' ∈ Set.Icc 0 (CappedBaseStock.mean P), CL P c r m ≤ CL P c r' m}

/-- `r_m`, the infimum of the set of minimizers of `C_m(r)` over `[0, E[D]]` (p. 11). -/
def rL (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) (m : ℕ) : ℝ :=
  sInf (argminCL P c m)

/-- The set of optimal constant-order levels, `argmin_{0 ≤ r ≤ E[D]} C(π_r)` (p. 7), the costs
compared in `[0, ∞]`. -/
def argminConst (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) : Set ℝ :=
  {r | r ∈ Set.Icc 0 (CappedBaseStock.mean P) ∧
    ∀ r' ∈ Set.Icc 0 (CappedBaseStock.mean P), constCost P c r ≤ constCost P c r'}

/-- `r∞`, the infimum of the set of optimal constant-order levels (p. 7). -/
def rInf (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) : ℝ :=
  sInf (argminConst P c)

/-- `φ(θ) = exp(θ r∞) E[exp(−θ D)]` (p. 7), used for `θ ≥ 0`, where the integrand lies in `(0, 1]`. -/
def phi (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) (θ : ℝ) : ℝ :=
  Real.exp (θ * rInf P c) * ∫ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ∂P.law

/-- `γ = inf_{θ ≥ 0} φ(θ)` (p. 7), an infimum over a nonempty index set of values `≥ 0`. -/
def gamma (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) : ℝ :=
  ⨅ θ : Set.Ici (0 : ℝ), phi P c θ

/-- The set of minimizers of `φ` on `[0, ∞)` (p. 7). -/
def phiMinimizers (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) : Set ℝ :=
  {θ | 0 ≤ θ ∧ phi P c θ = gamma P c}

open Classical in
/-- `1/ϑ` (p. 7), where `ϑ` is the supremum of the minimizers of `φ` on `[0, ∞)` and `ϑ = ∞` when
the infimum `γ` is not attained. With the paper's convention `1/∞ = 0` (p. 6): `1/ϑ = 0` when the
set of minimizers is empty (`ϑ = ∞` by definition) or unbounded (its supremum is `∞`). -/
def varthetaInv (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) : ℝ :=
  if (phiMinimizers P c).Nonempty ∧ BddAbove (phiMinimizers P c) then
    (sSup (phiMinimizers P c))⁻¹
  else 0

/-- `g = inf_{x ∈ ℝ} E[h (x − D)^+ + p (x − D)^−]` (p. 7), with `(x − D)^− = max(D − x, 0)`. The
integrand is integrable (it is at most `(h + p)(|x| + D)`) and `≥ 0`. -/
def gNV (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) : ℝ :=
  ⨅ x : ℝ, ∫ d : ℝ≥0, (c.h * max (x - (d : ℝ)) 0 + c.p * max ((d : ℝ) - x) 0) ∂P.law

/-- Entry `k` (zero-based) of a vector of length `L`, `0` beyond it. `vget v (k - 1)` is the paper's
`v_k`. -/
def vget {L : ℕ} (v : Fin L → ℝ) (k : ℕ) : ℝ :=
  if h : k < L then v ⟨k, h⟩ else 0

/-- `𝔣_d(χ_1, …, χ_L, I) = max_{j=0,…,L} (Σ_{i=1}^j (χ_{L+1−i} − d_{L+1−i}) + δ_{j,L} I)` (p. 10).
Here `χ_{L+1−i}` is `vget χ (L - i)` and `d_{L+1−i}` is `vget d (L - i)`. -/
def fObs (L : ℕ) (d χ : Fin L → ℝ) (I : ℝ) : ℝ :=
  (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (fun j =>
    (∑ i ∈ Finset.Icc 1 j, (vget χ (L - i) - vget d (L - i))) + if j = L then I else 0)

/-- The first `L` demands `(D_1, …, D_L)` of a demand path, as a real vector. -/
def firstDemands (L : ℕ) (d : CappedBaseStock.DemandPath) : Fin L → ℝ :=
  fun k => (d k : ℝ)

/-- `τ_{p,h} = √(h/(2p + h))` (Sec. 5.1, p. 15), the constant of the exponential-demand example. -/
def tauPH (c : CappedBaseStock.Parameters) : ℝ :=
  Real.sqrt (c.h / (2 * c.p + c.h))

/-- `γ_{p,h} = (1 − τ_{p,h}) exp(τ_{p,h})` (Sec. 5.1, p. 15). -/
def gammaPH (c : CappedBaseStock.Parameters) : ℝ :=
  (1 - tauPH c) * Real.exp (tauPH c)

end LostSalesExpGap.ConstOrder


