-- Prove2me | Definitions.Def_PerturbedWF_Supplement_KServer
-- name    : PerturbedWF_Supplement_KServer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:04:29.227694+00:00
-- url     : https://prove2.me/theorems/ad23bd64-e0b1-49cf-b2c5-85a18d3cfc3e
-- title:
--   Weighted paging and $k$-server: the work function (8.1), the exponential density (8.2) and the algorithm
-- statement:
--   Let $[n]$ be a finite set of points with a distance $d$, and let $\mathcal C=\{x\in\mathbb Z^n_{\ge0}:\sum_i x_i=k\}$ be the configurations of $k$ servers (multisets of $k$ points); write $r\in x$ for $x_r\ge1$ and $\|\cdot\|$ for the transportation norm of $d$. Given an initial configuration $X_0\in\mathcal C$ and requests $r_1,r_2,\ldots\in[n]$, the **work function** is $W_0(x)=\|x-X_0\|$ and
--   $$W_t(x)=\min_{y\in\mathcal C:\ r_t\in y}\big\{W_{t-1}(y)+\|x-y\|\big\},\qquad(8.1)$$
--   and the offline optimum after $T$ requests is $\mathrm{OPT}=\min_{x\in\mathcal C}W_T(x)$.
--
--   For $\kappa>0$ the **exponential density** on $[-1,1]$ is
--   $$\rho(s)=\frac{\alpha}{\kappa}\,e^{\alpha(s+1)},\qquad \alpha=\tfrac12\ln(\kappa+1),\qquad(8.2)$$
--   and the sampling law on $[-1,1]^E$ draws the coordinates $q_e$ independently with density $\rho$.
--
--   Given a matrix $A\in\mathbb R^{n\times E}$ and $v=Aq$, a **run** of the algorithm of §8.2.1 / §8.3.1 starts at $X_0$ and, when $r_t$ is requested, moves to any
--   $$X_t\in\arg\max_{x\in\mathcal C:\ r_t\in x}\big\{\langle v,x\rangle-W_{t-1}(x)\big\}.$$
--
--   These objects are shared by the weighted-paging theorem (Theorem 8.3) and the $k$-server theorem (Theorem 8.9).
--
--   **Formalization Note** The minima in (8.1) and in OPT are real infima over finite sets (nonempty as soon as $k\ge1$). The sampling law is Lebesgue measure on the cube $[-1,1]^E$ with the product density $\prod_e\rho(q_e)$. A run (`IsKServerRun`) allows every maximizer at every $q$ in the cube; no tie-breaking rule or measurability is imposed.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §8.1 'Common preliminaries', pp.20–21 (PDF pp.21–22), eqs. (8.1), (8.2); §8.2.1, p.22 (PDF p.23); §8.3.1, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_PerturbedWF_WClass

namespace PerturbedWF.Supplement

open MeasureTheory

/-!
# Weighted paging and k-server: the common framework of §8.1

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §8.1 "Common preliminaries", pp.20–21 (PDF pp.21–22):
configurations, problem definition, the work function (8.1), the exponential density (8.2); the
algorithms of §8.2.1, p.22 (PDF p.23) and §8.3.1, p.25 (PDF p.26).

The configurations are `kConfig ι k = {x ∈ ℤⁿ_{≥0} : ∑ x_i = k}` (multisets of `k` points); `r ∈ x`
means `x_r ≥ 1`. The request at time `t` is a point `r_t`, and an algorithm moves to `X_t ∈ C` with
`r_t ∈ X_t`, paying the movement cost `‖X_t − X_{t−1}‖` (transportation norm of a metric `d`).

**Formalization Note.**
* `ksWork d k X₀ r t x` is the work function: `W_0(x) = ‖x − X₀‖` and
  (8.1) `W_t(x) = min_{y ∈ C, r_t ∈ y} {W_{t−1}(y) + ‖x − y‖}`, written as a real infimum over the
  finite set `{y ∈ C : y_{r_t} ≥ 1}` (nonempty when `k ≥ 1` and there is a point), where it is the
  minimum. Requests are a sequence `r : ℕ → ι` used at times `t = 1, …, N` (index `0` unused).
* `ksOPT d k X₀ r N = min_{x ∈ C} W_N(x)`, a real infimum over the finite set `C`.
* `expDensity κ s = (α/κ) e^{α(s+1)}`, `α = ½ ln(κ+1)` (8.2), a probability density on `[−1, 1]`
  for `κ > 0`. `expLaw E κ` is the law of `q ∈ [−1, 1]^E` with i.i.d. coordinates of density
  `ρ`: Lebesgue measure on the cube with the product density `∏_e ρ(q_e)`.
* The matrix `A : ι → E → ℝ` (row `i` is `A_i`) gives `v = Aq`, `v_i = ∑_e A_{i,e} q_e`
  (`matVecE`). `IsKServerRun` is every run of the algorithm of §8.2.1/§8.3.1: `X_0 = X₀`, and for
  `1 ≤ t ≤ N` and every `q` in the cube, `X_t(q) ∈ C`, `r_t ∈ X_t(q)`, and `X_t(q)` maximizes
  `⟨Aq, x⟩ − W_{t−1}(x)` over `{x ∈ C : r_t ∈ x}`. No tie-breaking and no measurability in `q`
  is imposed.
-/

/-- The work function (8.1): `W_0(x) = ‖x − X₀‖`,
`W_{t+1}(x) = min_{y ∈ C, r_{t+1} ∈ y} {W_t(y) + ‖x − y‖}`. -/
noncomputable def ksWork {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (k : ℕ)
    (X₀ : ι → ℝ) (r : ℕ → ι) : ℕ → (ι → ℝ) → ℝ
  | 0, x => transNorm d (x - X₀)
  | t + 1, x => ⨅ y : {y : ι → ℝ // y ∈ kConfig ι k ∧ 1 ≤ y (r (t + 1))},
      ksWork d k X₀ r t y + transNorm d (x - y)

/-- The offline optimum `OPT = min_{x ∈ C} W_N(x)` after `N` requests. -/
noncomputable def ksOPT {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (k : ℕ)
    (X₀ : ι → ℝ) (r : ℕ → ι) (N : ℕ) : ℝ :=
  ⨅ x : kConfig ι k, ksWork d k X₀ r N x

/-- The exponential density (8.2) on `[−1, 1]`: `ρ(s) = (α/κ) exp(α(s + 1))`,
`α = ½ ln(κ + 1)`. -/
noncomputable def expDensity (κ s : ℝ) : ℝ :=
  Real.log (κ + 1) / 2 / κ * Real.exp (Real.log (κ + 1) / 2 * (s + 1))

/-- The law of `q ∈ [−1, 1]^E` whose coordinates are independent with density `expDensity κ`. -/
noncomputable def expLaw (E : Type) [Fintype E] (κ : ℝ) : Measure (E → ℝ) :=
  (volume.restrict (Set.Icc (-1 : E → ℝ) 1)).withDensity
    (fun q => ENNReal.ofReal (∏ e, expDensity κ (q e)))

/-- `Aq`: the vector `i ↦ ∑_e A i e * q e`. -/
def matVecE {ι E : Type} [Fintype E] (A : ι → E → ℝ) (q : E → ℝ) : ι → ℝ :=
  fun i => ∑ e, A i e * q e

/-- `X` is a run of the algorithm of §8.2.1 / §8.3.1 with matrix `A` on the requests `r` up to
time `N`: `X_0 = X₀`, and for `1 ≤ t ≤ N` and every `q ∈ [−1, 1]^E`,
`X_t(q) ∈ argmax_{x ∈ C : r_t ∈ x} {⟨Aq, x⟩ − W_{t−1}(x)}`. -/
def IsKServerRun {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] (d : ι → ι → ℝ) (k : ℕ)
    (X₀ : ι → ℝ) (r : ℕ → ι) (A : ι → E → ℝ) (N : ℕ) (X : ℕ → (E → ℝ) → (ι → ℝ)) : Prop :=
  (∀ q, X 0 q = X₀) ∧
    ∀ t ∈ Finset.Icc 1 N, ∀ q ∈ Set.Icc (-1 : E → ℝ) 1,
      X t q ∈ kConfig ι k ∧ 1 ≤ X t q (r t) ∧
      ∀ y ∈ kConfig ι k, 1 ≤ y (r t) →
        dot (matVecE A q) y - ksWork d k X₀ r (t - 1) y ≤
          dot (matVecE A q) (X t q) - ksWork d k X₀ r (t - 1) (X t q)

end PerturbedWF.Supplement


