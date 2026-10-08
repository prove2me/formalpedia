-- Prove2me | Definitions.Def_BootRobust_Perf_Setting
-- name    : BootRobust_Perf_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:33.742325+00:00
-- url     : https://prove2.me/theorems/28364bd6-3871-439a-bd9b-6ceecce842ca
-- title:
--   pp. 6–15 — support Ωₙ, Dₙ, D_{n,n}, neighbourhood chain, LP (22), D^j_n (23), estimator (18), robust budgets (24)–(26), B (27), r^j_n (29), bootstrap law (14)
-- statement:
--   This file fixes the finite setting of Bertsimas and Van Parys, *Bootstrap robust prescriptive analytics*, in which every result of the mission is stated.
--
--   **Support and distributions.** The distinct training points form a finite set $\Omega_n$ (a finite type $\iota$). A distribution on $\Omega_n$ is a vector $D\in\mathbb R^{\Omega_n}$ in the standard simplex; these form $\mathcal D_n$. The mass of $D$ on a set $S$ is $\sum_{i\in S}D_i$. The **bootstrap distributions** are
--   $$\mathcal D_{n,n}=\{D\in\mathcal D_n:\ n\,D_i\in\{0,1,\dots,n\}\ \ \forall i\in\Omega_n\}.$$
--
--   **Neighbourhoods and the estimator.** The neighbourhoods $N^j_n(x_0)$ of the context $x_0$ are a nested chain $N^0\subseteq N^1\subseteq\dots$ of subsets of $\Omega_n$; positive weights $w_i=w_n(\bar x,x_0)$ and real losses $\ell_i=L(\bar z,\bar y)$ are given. The estimator (18) of a distribution $D$ is the weighted average
--   $$E^n_D=\frac{\sum_{i\in N^{j^*}}\ell_i\,w_i\,D_i}{\sum_{i\in N^{j^*}}w_i\,D_i},$$
--   where $N^{j^*}$ is the smallest neighbourhood with $D$-mass at least $k/n$ (the smallest neighbourhood holding at least $k$ of the $n$ observations). The Nadaraya–Watson estimator (19) is the same average over all of $\Omega_n$.
--
--   **Partial estimators (22) and their domains (23).** For $j\in[n]$, $E^{n,j}_D$ is the supremum of $\sum_{i\in N^j}w_i\ell_iP_i$ over $s>0$ and $P\ge 0$ with $sD_i=P_i$ for all $i$, $\sum_iP_i=s$, $\sum_{i\in N^j}w_iP_i=1$, $\sum_{i\in N^j}P_i\ge\frac kn s$ and $\sum_{i\in N^{j-1}}P_i\le\frac{k-1}{n}s$; it is $-\infty$ when these constraints are infeasible. The domain set is
--   $$\mathcal D^j_n=\Big\{D\in\mathcal D_n:\ \sum_{i\in N^{j-1}}D_i\le\tfrac{k-1}{n},\ \ \tfrac kn\le\sum_{i\in N^j}D_i\Big\}.$$
--
--   **Bootstrap distance, budgets and radii.** The bootstrap distance (27) is $B(D,D')=\sum_iD_i\log(D_i/D'_i)$, with $0\log 0=0$ and $B(D,D')=+\infty$ if $D'_i=0<D_i$ for some $i$. The partial robust budget is $c^j_n=\sup\{E^{n,j}_D:\ D\in\mathcal D_n,\ B(D,D_{\mathrm{tr}})\le r\}$, the robust budget (26) is $\max_{j\in[n]}c^j_n$, and the minimum radius (29) is $r^j_n=\inf\{B(D,D_{\mathrm{tr}}):D\in\mathcal D^j_n\}$. The robust Nadaraya–Watson budget is $\sup\{E_D:\ D\in\mathcal D_n,\ B(D,D_{\mathrm{tr}})\le r\}$ with $E_D$ the Nadaraya–Watson estimator. The sets $C_j=\{D\in\mathcal D^j_n: E^{n,j}_D>\bar c\}$ of the proof of Theorem 6 are defined for a threshold $\bar c\in[-\infty,+\infty]$.
--
--   **Bootstrap.** The bootstrap law (14) is the law of $n$ independent draws from $D_{\mathrm{tr}}$ (the $n$-fold product measure on $\Omega_n^n$), and the empirical distribution of draws $\omega$ gives each point its frequency divided by $n$. Finally $\exp(-n\cdot x)$ is extended to $x=+\infty$ by the value $0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Covariates, responses, the context $x_0$ and the distance function of Definition 2 do not appear: only the support points, their weights and losses enter. Definition 2's neighbourhoods are abstracted to a chain `N : ℕ → Finset ι`; the theorems assume it is monotone with `N 0 = ∅` (the page never defines $N^0$; it is the convention for $N^{j-1}$ at $j=1$) and `N n = univ`. Every supremum and infimum that can be empty or unbounded is taken in `EReal` (sup ∅ = −∞, inf ∅ = +∞). The estimator (18) is meant on $\mathcal D_{n,n}$, where $j^*$ exists and the denominator is positive. The one-draw law is `∑ i, ofReal (Dtr i) • dirac i` on a measurable space with measurable singletons; only the first $n$ coordinates of the infinite bootstrap sequence $D^\infty_{\mathrm{tr}[n]}$ matter.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Definitions 1–3, 5, 6 and (14), (17)–(19), (22)–(27), (29), pp. 6–15; C_j from the proof of Theorem 6, p. 15

import Mathlib

namespace BootRobust.Perf

open MeasureTheory

/-! Setting of Bertsimas and Van Parys, *Bootstrap robust prescriptive analytics*,
arXiv:1711.09974v2, §§1–4 (pp. 6–15).

The empirical support `Ωₙ` of the training data is a finite type `ι`; a distribution on it
is a vector `D : ι → ℝ` in `stdSimplex ℝ ι` (the set `Dₙ`). Covariates, responses, the
context `x₀` and the distance function never appear: only the support points, their
weights `w i = w_n(x̄, x₀)` and their losses `ℓ i = L(z̄, ȳ)` enter. The nested
neighbourhoods `N^j_n(x₀)` of Definition 2 are a chain `N : ℕ → Finset ι`; the theorems
assume `Monotone N`, `N 0 = ∅` and `N n = univ`. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mass `∑_{i ∈ s} D i` that the distribution `D` puts on the set `s`. -/
def mass (D : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, D i

/-- The bootstrap distributions `D_{n,n}` (p. 11): distributions on `Ωₙ` all of whose
weights are multiples of `1/n`, i.e. `n · D i ∈ {0, 1, …, n}`. -/
def Dnn (n : ℕ) : Set (ι → ℝ) :=
  {D | D ∈ stdSimplex ℝ ι ∧ ∀ i, ∃ m : ℕ, m ≤ n ∧ (n : ℝ) * D i = m}

/-- The domain `D^j_n` of the `j`-th partial estimator, (23), p. 11: the distributions with
`∑_{N^{j−1}} D ≤ (k − 1)/n` and `k/n ≤ ∑_{N^j} D`. For `j = 0` the index `j - 1` is the
truncated `0`; the theorems only use `1 ≤ j ≤ n`. -/
def Dj (n k : ℕ) (N : ℕ → Finset ι) (j : ℕ) : Set (ι → ℝ) :=
  {D | D ∈ stdSimplex ℝ ι ∧ mass D (N (j - 1)) ≤ ((k : ℝ) - 1) / n ∧
    (k : ℝ) / n ≤ mass D (N j)}

/-- Feasibility of `(s, P)` in the linear program (22), p. 11, defining the `j`-th partial
estimator at the distribution `D`, constraint by constraint. -/
def lpFeasible (n k : ℕ) (N : ℕ → Finset ι) (w : ι → ℝ) (j : ℕ) (D : ι → ℝ)
    (s : ℝ) (P : ι → ℝ) : Prop :=
  0 < s ∧ (∀ i, 0 ≤ P i) ∧ (∀ i, s * D i = P i) ∧ ∑ i, P i = s ∧
    ∑ i ∈ N j, w i * P i = 1 ∧ (k : ℝ) / n * s ≤ ∑ i ∈ N j, P i ∧
    ∑ i ∈ N (j - 1), P i ≤ ((k : ℝ) - 1) / n * s

/-- The partial estimator `E^{n,j}_D[L(z̄, y) | x = x₀]` of (22), p. 11: the supremum of
`∑_{N^j} w · ℓ · P` over the feasible `(s, P)`, in `EReal`. It is `⊥ = −∞` when (22) is
infeasible ("the supremum over an empty set is unbounded from below"). -/
noncomputable def partialEst (n k : ℕ) (N : ℕ → Finset ι) (w ℓ : ι → ℝ) (j : ℕ)
    (D : ι → ℝ) : EReal :=
  ⨆ p ∈ {p : ℝ × (ι → ℝ) | lpFeasible n k N w j D p.1 p.2},
    ((∑ i ∈ N j, w i * ℓ i * p.2 i : ℝ) : EReal)

/-- The index `j*` of the smallest neighbourhood `N^{j*}` carrying `D`-mass at least `k/n`,
i.e. holding at least `k` of the `n` observations of a bootstrap distribution. On `D_{n,n}`
(with the chain hypotheses and `1 ≤ k ≤ n`) the set is nonempty and `1 ≤ j* ≤ n`. -/
noncomputable def jstar (n k : ℕ) (N : ℕ → Finset ι) (D : ι → ℝ) : ℕ :=
  sInf {j : ℕ | (k : ℝ) / n ≤ mass D (N j)}

/-- The nominal estimator `E^n_D[L(z, y) | x = x₀]` of (18), p. 9: the `w`-weighted average
of the loss over the smallest neighbourhood holding at least `k` of the `n` observations.
Used only on `D_{n,n}`, where the denominator is positive. -/
noncomputable def nominalEst (n k : ℕ) (N : ℕ → Finset ι) (w ℓ : ι → ℝ) (D : ι → ℝ) : ℝ :=
  (∑ i ∈ N (jstar n k N D), ℓ i * w i * D i) / (∑ i ∈ N (jstar n k N D), w i * D i)

/-- The bootstrap distance `B(D, D′) = ∑ D log(D/D′)` of (27), p. 13, in `EReal`, with the
conventions `0 log 0 = 0` (via `Real.log 0 = 0`) and `B(D, D′) = +∞` when some `D′ i = 0 < D i`.
-/
noncomputable def bootDist (D D' : ι → ℝ) : EReal :=
  if ∀ i, D' i = 0 → D i = 0 then ((∑ i, D i * Real.log (D i / D' i) : ℝ) : EReal) else ⊤

/-- The partial robust budget `c^j_n(z, D_tr, x₀) = sup{E^{n,j}_D : D ∈ Dₙ, B(D, D_tr) ≤ r}`
(p. 12), in `EReal`; it is `⊥` when no distribution of the ball lies in the domain of the
partial estimator. -/
noncomputable def partialRobust (n k : ℕ) (N : ℕ → Finset ι) (w ℓ : ι → ℝ) (Dtr : ι → ℝ)
    (r : ℝ) (j : ℕ) : EReal :=
  ⨆ D ∈ {D : ι → ℝ | D ∈ stdSimplex ℝ ι ∧ bootDist D Dtr ≤ (r : EReal)},
    partialEst n k N w ℓ j D

/-- The robust budget `max_{j ∈ [n]} c^j_n(z, D_tr, x₀)` of (26), p. 12, with `R = B`. -/
noncomputable def robustBudget (n k : ℕ) (N : ℕ → Finset ι) (w ℓ : ι → ℝ) (Dtr : ι → ℝ)
    (r : ℝ) : EReal :=
  ⨆ j ∈ Finset.Icc 1 n, partialRobust n k N w ℓ Dtr r j

/-- The minimum bootstrap radius `r^j_n = inf{B(D, D_tr) : D ∈ D^j_n}` of (29), p. 14, in
`EReal`; it is `⊤ = +∞` when `D^j_n` is empty. -/
noncomputable def rj (n k : ℕ) (N : ℕ → Finset ι) (Dtr : ι → ℝ) (j : ℕ) : EReal :=
  ⨅ D ∈ Dj n k N j, bootDist D Dtr

/-- The set `C_j = {D ∈ D^j_n : E^{n,j}_D[L(z̄, y) | x = x₀] > c̄}` of the proof of
Theorem 6, p. 15, for a threshold `c̄ ∈ EReal`. -/
def Cj (n k : ℕ) (N : ℕ → Finset ι) (w ℓ : ι → ℝ) (cbar : EReal) (j : ℕ) : Set (ι → ℝ) :=
  {D | D ∈ Dj n k N j ∧ cbar < partialEst n k N w ℓ j D}

/-- The Nadaraya–Watson estimator (19), p. 10: the `w`-weighted average of the loss over all
of `Ωₙ`; this is (18) with `k = n`. -/
noncomputable def nwEst (w ℓ : ι → ℝ) (D : ι → ℝ) : ℝ :=
  (∑ i, w i * ℓ i * D i) / (∑ i, w i * D i)

/-- The robust Nadaraya–Watson budget `c_n(z, D_tr, x₀) = sup{E^n_D : D ∈ Dₙ, B(D, D_tr) ≤ r}`,
(24) with `k = n` and `R = B`, in `EReal`. -/
noncomputable def nwBudget (w ℓ : ι → ℝ) (Dtr : ι → ℝ) (r : ℝ) : EReal :=
  ⨆ D ∈ {D : ι → ℝ | D ∈ stdSimplex ℝ ι ∧ bootDist D Dtr ≤ (r : EReal)}, (nwEst w ℓ D : EReal)

/-- The law of one bootstrap draw: the distribution `D_tr` on `Ωₙ`, as the measure
`∑ i, D_tr i · δ_i`. -/
noncomputable def drawLaw [MeasurableSpace ι] (Dtr : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (Dtr i) • Measure.dirac i

instance drawLaw_isFinite [MeasurableSpace ι] (Dtr : ι → ℝ) :
    IsFiniteMeasure (drawLaw Dtr) := by
  constructor
  simp [drawLaw, Finset.sum_apply]

/-- The bootstrap law (14), p. 6: `n` independent draws from `D_tr`, the `n`-fold product
measure on `Fin n → ι`. (Only the first `n` coordinates of `D^∞_tr[n]` matter.) -/
noncomputable def bootLaw [MeasurableSpace ι] (Dtr : ι → ℝ) (n : ℕ) : Measure (Fin n → ι) :=
  Measure.pi (fun _ : Fin n => drawLaw Dtr)

/-- The empirical distribution `D_bs[n]` of `n` bootstrap draws `ω`: the frequency of each
support point, divided by `n`. -/
noncomputable def empDist {n : ℕ} (ω : Fin n → ι) : ι → ℝ :=
  fun i => ((Finset.univ.filter fun m => ω m = i).card : ℝ) / n

/-- `exp(−n · x)` for an exponent `x ∈ EReal`, in `ℝ≥0∞`, with `exp(−n · (+∞)) = 0`.
It is only applied to exponents `x ≥ r ∈ ℝ`, never to `⊥`. -/
noncomputable def expNeg (n : ℕ) (x : EReal) : ENNReal :=
  if x = ⊤ then 0 else ENNReal.ofReal (Real.exp (-((n : ℝ) * x.toReal)))

end BootRobust.Perf


