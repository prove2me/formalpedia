-- Prove2me | Definitions.Def_PerturbedWF_Supplement_KTaxi
-- name    : PerturbedWF_Supplement_KTaxi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:05:18.640378+00:00
-- url     : https://prove2.me/theorems/73a3b487-e9cd-4e87-9fc9-3354d13c64d5
-- title:
--   The $k$-taxi problem: the work function (5.1) and the algorithm of §5.1
-- statement:
--   In the **$k$-taxi problem** the configurations are $\mathcal C=\{x\in\mathbb Z^n_{\ge0}:\sum_i x_i=k\}$ (multisets of $k$ taxis on the points $[n]$ of a metric space). Starting from $X_0\in\mathcal C$, the request at time $t$ is an ordered pair $(r_t,s_t)\in[n]\times[n]$; the algorithm moves to a configuration $Y_t$ with $r_t\in Y_t$ (i.e. $Y_{t,r_t}\ge1$), and then the taxi is carried from $r_t$ to $s_t$:
--   $$X_t=Y_t+\delta_t,\qquad \delta_t=e_{s_t}-e_{r_t}.$$
--   The cost at time $t$ is $\|X_{t-1}-Y_t\|$; the carried move is free. The **work function** is $W_0(x)=\|x-X_0\|$ and
--   $$W_t(x)=\min_{y\in\mathcal C:\ r_t\in y}\big\{W_{t-1}(y)+\|y+\delta_t-x\|\big\},\qquad(5.1)$$
--   with $\mathrm{OPT}=\min_{x\in\mathcal C}W_T(x)$.
--
--   The **algorithm of §5.1** takes vectors $A_i\in\mathbb R^m$, samples $q$ uniformly from $[-1,1]^m$, sets $v=Aq$, and at time $t$ moves to any $Y_t\in\arg\max_{y\in\mathcal C:\,r_t\in y}\{\langle v,y\rangle-W_{t-1}(y)\}$, then sets $X_t=Y_t+\delta_t$.
--
--   **Formalization Note** Requests are two sequences $r,s$ used at times $1,\ldots,N$. The minima are real infima over finite sets. A run (`IsKTaxiRun`) allows every maximizer at every $q$ in the cube.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §5 'Configurations', 'Problem definition', 'Work function', pp.14–15 (PDF pp.15–16), eq. (5.1); §5.1 'Algorithm', p.15 (PDF p.16)

import Mathlib
import Definitions.Def_PerturbedWF_Algorithm

namespace PerturbedWF.Supplement

/-!
# The k-taxi problem: work function (5.1) and the algorithm of §5.1

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §5 "k-taxi", pp.14–15 (PDF pp.15–16): configurations,
problem definition, the work function (5.1); §5.1 "Algorithm", p.15 (PDF p.16).

The configurations are `kConfig ι k` (multisets of `k` taxis); `r ∈ x` means `x_r ≥ 1`. The request
at time `t` is an ordered pair `(r_t, s_t)`; the algorithm moves to `Y_t ∋ r_t` at cost
`‖X_{t−1} − Y_t‖`, and then `X_t = Y_t + δ_t`, `δ_t = e_{s_t} − e_{r_t}` (the carried move is free).

**Formalization Note.**
* Requests are two sequences `r s : ℕ → ι` used at times `t = 1, …, N` (index `0` unused);
  `r_t = s_t` is allowed.
* `ktWork d k X₀ r s t x` is the work function: `W_0(x) = ‖x − X₀‖` and
  (5.1) `W_t(x) = min_{y ∈ C, r_t ∈ y} {W_{t−1}(y) + ‖y + δ_t − x‖}`, a real infimum over the
  finite set `{y ∈ C : y_{r_t} ≥ 1}`, where it is the minimum.
* `ktOPT = min_{x ∈ C} W_N(x)`.
* `IsKTaxiRun` is every run of §5.1 with vectors `A_i` (`v = Aq`, `q` in the cube `[−1, 1]^m`):
  `X_0 = X₀`; for `1 ≤ t ≤ N` and every `q` in the cube, `Y_t(q)` is any maximizer of
  `⟨Aq, y⟩ − W_{t−1}(y)` over `{y ∈ C : r_t ∈ y}`, and `X_t(q) = Y_t(q) + δ_t`. No tie-breaking
  and no measurability in `q` is imposed.
-/

/-- `δ_t = e_{s_t} − e_{r_t}`. -/
def taxiShift {ι : Type} [DecidableEq ι] (r s : ℕ → ι) (t : ℕ) : ι → ℝ :=
  Pi.single (s t) (1 : ℝ) - Pi.single (r t) (1 : ℝ)

/-- The k-taxi work function (5.1): `W_0(x) = ‖x − X₀‖`,
`W_{t+1}(x) = min_{y ∈ C, r_{t+1} ∈ y} {W_t(y) + ‖y + δ_{t+1} − x‖}`. -/
noncomputable def ktWork {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (k : ℕ)
    (X₀ : ι → ℝ) (r s : ℕ → ι) : ℕ → (ι → ℝ) → ℝ
  | 0, x => transNorm d (x - X₀)
  | t + 1, x => ⨅ y : {y : ι → ℝ // y ∈ kConfig ι k ∧ 1 ≤ y (r (t + 1))},
      ktWork d k X₀ r s t y + transNorm d ((y : ι → ℝ) + taxiShift r s (t + 1) - x)

/-- The offline optimum of k-taxi, `OPT = min_{x ∈ C} W_N(x)`. -/
noncomputable def ktOPT {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (k : ℕ)
    (X₀ : ι → ℝ) (r s : ℕ → ι) (N : ℕ) : ℝ :=
  ⨅ x : kConfig ι k, ktWork d k X₀ r s N x

/-- `(X, Y)` is a run of the k-taxi algorithm of §5.1 with vectors `A` up to time `N`. -/
def IsKTaxiRun {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (d : ι → ι → ℝ) (k : ℕ)
    (X₀ : ι → ℝ) (r s : ℕ → ι) (A : ι → Fin m → ℝ) (N : ℕ)
    (X Y : ℕ → (Fin m → ℝ) → (ι → ℝ)) : Prop :=
  (∀ q, X 0 q = X₀) ∧
    ∀ t ∈ Finset.Icc 1 N, ∀ q ∈ Set.Icc (-1 : Fin m → ℝ) 1,
      Y t q ∈ kConfig ι k ∧ 1 ≤ Y t q (r t) ∧
      (∀ y ∈ kConfig ι k, 1 ≤ y (r t) →
        dot (matVec A q) y - ktWork d k X₀ r s (t - 1) y ≤
          dot (matVec A q) (Y t q) - ktWork d k X₀ r s (t - 1) (Y t q)) ∧
      X t q = Y t q + taxiShift r s t

end PerturbedWF.Supplement


