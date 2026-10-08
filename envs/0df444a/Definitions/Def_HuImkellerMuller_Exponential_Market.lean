-- Prove2me | Definitions.Def_HuImkellerMuller_Exponential_Market
-- name    : HuImkellerMuller_Exponential_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:55.490032+00:00
-- url     : https://prove2.me/theorems/59e5467f-d03c-49dc-a512-969f8efeeed1
-- title:
--   §1, pp. 3–4 and (3), p. 6 — predictability, the market (1), θ, the constraint sets C_t = C̃σ_t and Π_C
-- statement:
--   This module fixes the market of Hu, Imkeller and Müller (2005), §1.
--
--   Time runs over $[0,T]$ and $\mathbb F = (\mathcal F_t)$ is a filtration on $(\Omega,\mathcal F,P)$. A process $\varphi$ is **predictable** when $(t,\omega)\mapsto\varphi_t(\omega)$ is measurable for the predictable $\sigma$-algebra of $\mathbb F$.
--
--   There are $d\le m$ stocks with prices $dS^i_t/S^i_t = b^i_t\,dt+\sigma^i_t\,dW_t$, driven by an $m$-dimensional Brownian motion $W$. The **standing market hypotheses** are:
--
--   1. $d\le m$;
--   2. the drift $b=(b^1,\dots,b^d)$ and the volatility matrix $\sigma$ (a $d\times m$ matrix with rows $\sigma^i$) are predictable, entry by entry;
--   3. $b$ and $\sigma$ are uniformly bounded on $[0,T]\times\Omega$;
--   4. $\sigma\sigma^{\mathrm{tr}}$ is uniformly elliptic: there are constants $K>\varepsilon>0$ with
--   $$K I_d \;\ge\; \sigma_t\sigma_t^{\mathrm{tr}} \;\ge\; \varepsilon I_d\qquad\text{for all } t\le T,\ P\text{-a.s.}$$
--
--   The **market price of risk** is the $\mathbb R^m$-valued process
--   $$\theta_t=\sigma_t^{\mathrm{tr}}(\sigma_t\sigma_t^{\mathrm{tr}})^{-1}b_t .$$
--
--   For a constraint set $\tilde C\subseteq\mathbb R^{1\times d}$ of row vectors, the **constraint set in amounts** is (3):
--   $$C_t(\omega)=\tilde C\sigma_t(\omega)=\{c\,\sigma_t(\omega): c\in\tilde C\}\subseteq\mathbb R^{1\times m}.$$
--
--   For $C\subseteq\mathbb R^m$ and $a\in\mathbb R^m$, $\operatorname{dist}_C(a)=\inf_{b\in C}|a-b|$, and the set of **nearest points** is
--   $$\Pi_C(a)=\{b\in C : |a-b|=\operatorname{dist}_C(a)\}.$$
--
--   These objects are the data of every statement of the mission: the strategies take values in $C_t$, and the optimal strategy is a selection of $\Pi_{C_t}$.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$; row vectors of $\mathbb R^{1\times m}$ are `EuclideanSpace ℝ (Fin m)`, so $|\cdot|$ is Euclidean; row vectors of $\mathbb R^{1\times d}$ are `Fin d → ℝ`. Ellipticity is read "for $P$-a.e. $\omega$, for every $t\le T$" and uniform boundedness pointwise on $[0,T]\times\Omega$. The page's full-rank assumption is not a separate field: it follows from $\sigma\sigma^{\mathrm{tr}}\ge\varepsilon I_d$. Matrix inversion is total in Lean; off the null set where ellipticity fails, $(\sigma\sigma^{\mathrm{tr}})^{-1}$ is a junk value, which does not affect any $\lambda\otimes P$-a.e. statement. $\operatorname{dist}_C$ is `Metric.infDist`, which equals the page's minimum for a closed nonempty $C$.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, §1, pp. 3–4 (market (1), θ, dist_C, Π_C); (3), p. 6

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_CvitanicKaratzas92_Optimality_Market

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}

/-- A process `φ : ℝ≥0 → Ω → E` is predictable with respect to the filtration `𝓕` when the map
`(t, ω) ↦ φ t ω` is measurable for the predictable σ-algebra on `ℝ≥0 × Ω` (p. 3). -/
def IsPredictable {E : Type*} [MeasurableSpace E] (𝓕 : Filtration ℝ≥0 mΩ)
    (φ : ℝ≥0 → Ω → E) : Prop :=
  Measurable[𝓕.predictable] (fun q : ℝ≥0 × Ω => φ q.1 q.2)

/-- The standing assumptions on the market (1), pp. 3–4: there are `d ≤ m` stocks; the drift
`b` (an `ℝ^d`-valued process, the column of the `bⁱ`) and the volatility `σ` (a `d × m` matrix
process, rows `σⁱ`) are predictable and uniformly bounded on `[0, T] × Ω`; and `σσᵀ` is uniformly
elliptic, `K I_d ≥ σσᵀ ≥ ε I_d` for constants `K > ε > 0`, for `P`-a.e. `ω` and every `t ≤ T`. -/
structure MarketHyp (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ) : Prop where
  d_le_m : d ≤ m
  b_pred : ∀ i, IsPredictable 𝓕 (fun t ω => b t ω i)
  σ_pred : ∀ i j, IsPredictable 𝓕 (fun t ω => σ t ω i j)
  b_bdd : ∃ B : ℝ, ∀ t ≤ T, ∀ ω i, |b t ω i| ≤ B
  σ_bdd : ∃ B : ℝ, ∀ t ≤ T, ∀ ω i j, |σ t ω i j| ≤ B
  elliptic : ∃ K ε : ℝ, 0 < ε ∧ ε < K ∧ ∀ᵐ ω ∂P, ∀ t ≤ T,
    (σ t ω * (σ t ω).transpose - ε • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
    (K • (1 : Matrix (Fin d) (Fin d) ℝ) - σ t ω * (σ t ω).transpose).PosSemidef

/-- The market price of risk `θ_t = σ_tᵀ (σ_t σ_tᵀ)⁻¹ b_t` (p. 4), an `ℝ^m`-valued process computed
from `b` and `σ`. -/
noncomputable def theta (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 ((σ t ω).transpose.mulVec ((σ t ω * (σ t ω).transpose)⁻¹.mulVec (b t ω)))

/-- (3), p. 6: the constraint set `C_t(ω) = C̃ σ_t(ω) = {c σ_t(ω) : c ∈ C̃} ⊆ ℝ^m`, the image of the
row-vector constraint set `C̃ ⊆ ℝ^{1×d}` under right multiplication by `σ_t(ω)`. -/
def Cset (Ct : Set (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ) (t : ℝ≥0) (ω : Ω) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  (fun c : Fin d → ℝ => WithLp.toLp 2 (Matrix.vecMul c (σ t ω))) '' Ct

/-- p. 3: the set `Π_C(a) = {b ∈ C : |a − b| = dist_C(a)}` of points of `C` nearest to `a`, where
`dist_C(a) = Metric.infDist a C`. -/
def proj (C : Set (EuclideanSpace ℝ (Fin m))) (a : EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {b | b ∈ C ∧ ‖a - b‖ = Metric.infDist a C}

end HuImkellerMuller.Exponential


