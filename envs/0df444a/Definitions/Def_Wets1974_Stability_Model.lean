-- Prove2me | Definitions.Def_Wets1974_Stability_Model
-- name    : Wets1974_Stability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:34:24.191281+00:00
-- url     : https://prove2.me/theorems/e610b32a-2c67-4987-8f9c-3516354c0923
-- title:
--   The stochastic program with fixed recourse (2.1), weak covariance (Def. 2.2), the paper's integral, $Z(x)=\bar c x+\mathcal Q(x)$ (3.1) and $K_2$ (Cor. 4.5)
-- statement:
--   This file sets up the **stochastic program with fixed recourse** of Wets (1974), (2.1):
--   $$\inf_{x\ge 0,\ Ax=b}\ Z(x)=E_\xi\Big\{c(\xi)x+\min_{y\ge 0}\,[\,q(\xi)y \mid T(\xi)x+Wy=p(\xi)\,]\Big\}.$$
--
--   1. **Data.** The random element is $\xi=(c,q,p,T)$ with $c\in\mathbb R^n$, $q\in\mathbb R^{\bar n}$, $p\in\mathbb R^{\bar m}$ and $T$ an $\bar m\times n$ matrix; it has law $\mu$, a measure on the product space with its Borel structure. $c(\xi),q(\xi),p(\xi),T(\xi)$ are the coordinate projections. The recourse matrix $W$ ($\bar m\times\bar n$) is fixed.
--   2. **Weak covariance condition** (Definition 2.2): for all $i,j,k$ the functions $c_j(\xi)$, $q_j(\xi)p_i(\xi)$ and $q_j(\xi)t_{ik}(\xi)$ are $\mu$-integrable. Nothing is assumed about $q$, $p$, $T$ separately.
--   3. **Full row rank** of $W$: $\operatorname{rank}W=\bar m$, the paper's standing assumption (p. 312).
--   4. **Recourse function** (p. 312): $Q(x,\xi)=\min\{q(\xi)y \mid Wy=p(\xi)-T(\xi)x,\ y\ge 0\}$, equal to $+\infty$ when the program is infeasible and $-\infty$ when it is unbounded below.
--   5. **The paper's integral** (p. 312): for $g$ with values in $[-\infty,+\infty]$,
--   $$E\{g\}=\int g^+\,d\mu-\int g^-\,d\mu,$$
--   where the positive (negative) part is $+\infty$ ($-\infty$) if its integral diverges or $g=+\infty$ ($-\infty$) on a set of positive measure, and the ambiguous case is resolved as $(+\infty)+(-\infty)=+\infty$.
--   6. **Expected recourse and objective** ((3.1), p. 313): $\mathcal Q(x)=E_\xi\{Q(x,\xi)\}$ with that integral, $\bar c=E_\xi\{c(\xi)\}$ (finite by item 2), and
--   $$Z(x)=\bar c\,x+\mathcal Q(x)\in[-\infty,+\infty].$$
--   7. **Induced constraints** (Corollary 4.5, p. 316): $\operatorname{pos}W=\{Wy: y\ge 0\}$; for $\zeta=(p,T)$, $K_2(\zeta)=\{x : p-Tx\in\operatorname{pos}W\}$; $\tilde\Xi_{p,T}$ is the support of the distribution of $(p(\xi),T(\xi))$; and
--   $$K_2=\bigcap_{\zeta\in\tilde\Xi_{p,T}}K_2(\zeta).$$
--   8. **Feasible region** (p. 318): $K=K_1\cap K_2$ with $K_1=\{x: Ax=b,\ x\ge 0\}$.
--
--   These are the objects of the deterministic equivalent program (3.2)/(8.2): minimize $Z$ over $K$.
--
--   **Formalization Note** The data space is `(Fin n → ℝ) × (Fin n̄ → ℝ) × (Fin m̄ → ℝ) × (Fin m̄ → Fin n → ℝ)`; the paper's $\Xi\subseteq\mathbb R^N$ only carries $\mu$, so $\mu$ lives on the whole space. $Q$ is the platform definition `KallMayer.Recourse.PointwiseRecourse` (an `EReal`-valued `sInf`). The integral is written out with `lintegral` of the positive and negative parts, as `if P = ⊤ then ⊤ else P − N`, because Mathlib's `EReal` subtraction gives $\top-\top=\bot$, the opposite of the paper's convention. $\bar c$ is a Bochner integral, legitimate because each $c_j$ is integrable under Definition 2.2. Supports are `MeasureTheory.Measure.support`; $\tilde\Xi_{p,T}$ is the support of the push-forward of $\mu$ under the (continuous, hence measurable) projection $\xi\mapsto(p,T)$. Measurability of $Q(x,\cdot)$, which the paper assumes when it forms $\mathcal Q$, is not assumed.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, pp. 311-318, Eq. (2.1), Definition 2.2, p. 312 (full rank of W, definition of Q and of the integral), Eq. (3.1), Eq. (4.4), Corollary 4.5, p. 318 (K = K₁ ∩ K₂)

import Mathlib
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_Wets1974_Stability_ConvexAnalysis

namespace Wets1974.Stability

open MeasureTheory Matrix

/-- The data space of problem (2.1), p. 311: a point `ξ = (c, q, p, T)` with `c ∈ ℝⁿ`,
`q ∈ ℝ^n̄`, `p ∈ ℝ^m̄` and `T` an `m̄ × n` matrix (stored as `Fin m̄ → Fin n → ℝ`).
It carries the product (Borel) measurable structure and the product topology. -/
abbrev DataSpace (n nb mb : ℕ) : Type :=
  (Fin n → ℝ) × (Fin nb → ℝ) × (Fin mb → ℝ) × (Fin mb → Fin n → ℝ)

/-- The space of the pair `(p, T)`. -/
abbrev PTSpace (n mb : ℕ) : Type :=
  (Fin mb → ℝ) × (Fin mb → Fin n → ℝ)

variable {n nb mb : ℕ}

/-- The projection `c(ξ)`. -/
def cOf (ξ : DataSpace n nb mb) : Fin n → ℝ := ξ.1

/-- The projection `q(ξ)`. -/
def qOf (ξ : DataSpace n nb mb) : Fin nb → ℝ := ξ.2.1

/-- The projection `p(ξ)`. -/
def pOf (ξ : DataSpace n nb mb) : Fin mb → ℝ := ξ.2.2.1

/-- The projection `T(ξ)`, as an `m̄ × n` matrix. -/
def TOf (ξ : DataSpace n nb mb) : Matrix (Fin mb) (Fin n) ℝ := Matrix.of ξ.2.2.2

/-- The projection `ξ ↦ (p(ξ), T(ξ))`. -/
def projPT (ξ : DataSpace n nb mb) : PTSpace n mb := (ξ.2.2.1, ξ.2.2.2)

/-- `projPT` is a coordinate projection, hence measurable. -/
theorem measurable_projPT : Measurable (projPT : DataSpace n nb mb → PTSpace n mb) :=
  measurable_snd.snd

/-- Definition 2.2, p. 311 (weak covariance condition): for all `i, j, k` the random functions
`c_j(ξ)`, `q_j(ξ) p_i(ξ)` and `q_j(ξ) t_ik(ξ)` have first moments (are `μ`-integrable). -/
def WeakCovariance (μ : Measure (DataSpace n nb mb)) : Prop :=
  (∀ j : Fin n, Integrable (fun ξ => cOf ξ j) μ) ∧
  (∀ (j : Fin nb) (i : Fin mb), Integrable (fun ξ => qOf ξ j * pOf ξ i) μ) ∧
  (∀ (j : Fin nb) (i : Fin mb) (k : Fin n), Integrable (fun ξ => qOf ξ j * TOf ξ i k) μ)

/-- The standing assumption of p. 312: `W` (an `m̄ × n̄` matrix) has full row rank `m̄`. -/
def FullRowRank (W : Matrix (Fin mb) (Fin nb) ℝ) : Prop :=
  W.rank = mb

/-- The recourse function `Q(x, ξ) = min {q(ξ) y | W y = p(ξ) − T(ξ) x, y ≥ 0}`, p. 312, with
value `+∞` when the program is infeasible and `−∞` when it is unbounded below. -/
noncomputable def Q (W : Matrix (Fin mb) (Fin nb) ℝ) (x : Fin n → ℝ)
    (ξ : DataSpace n nb mb) : EReal :=
  KallMayer.Recourse.PointwiseRecourse W (TOf ξ) (pOf ξ) (qOf ξ) x

/-- The paper's integral of an extended-real function, p. 312: the sum of its positive part
`∫ g⁺ dμ ∈ [0, +∞]` and its negative part `−∫ g⁻ dμ ∈ [−∞, 0]`, with the ambiguous case
resolved as `(+∞) + (−∞) = +∞`. -/
noncomputable def paperIntegral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → EReal) : EReal :=
  if (∫⁻ ξ, (g ξ).toENNReal ∂μ) = ⊤ then ⊤
  else ((∫⁻ ξ, (g ξ).toENNReal ∂μ : ENNReal) : EReal) -
    ((∫⁻ ξ, (-g ξ).toENNReal ∂μ : ENNReal) : EReal)

/-- The expected recourse `𝒬(x) = E_ξ{Q(x, ξ)}`, (3.1), p. 313, with the paper's integral. -/
noncomputable def expectedRecourse (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (x : Fin n → ℝ) : EReal :=
  paperIntegral μ (Q W x)

/-- `c̄ = E_ξ{c(ξ)}`, (3.1), p. 313, componentwise (a Bochner integral; each `c_j` is
integrable under Definition 2.2). -/
noncomputable def cbar (μ : Measure (DataSpace n nb mb)) : Fin n → ℝ :=
  fun j => ∫ ξ, cOf ξ j ∂μ

/-- The objective of the deterministic equivalent program, (3.1), p. 313:
`Z(x) = c̄ x + 𝒬(x)`, an extended real number. -/
noncomputable def Z (μ : Measure (DataSpace n nb mb)) (W : Matrix (Fin mb) (Fin nb) ℝ)
    (x : Fin n → ℝ) : EReal :=
  ((cbar μ ⬝ᵥ x : ℝ) : EReal) + expectedRecourse μ W x

/-- `pos W = {t | t = W y, y ≥ 0}`, p. 315. -/
def posW (W : Matrix (Fin mb) (Fin nb) ℝ) : Set (Fin mb → ℝ) :=
  {t | ∃ y : Fin nb → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = t}

/-- `K₂(ζ) = {x | p − T x ∈ pos W}` for `ζ = (p, T)`, (4.4), p. 316. -/
def K2of (W : Matrix (Fin mb) (Fin nb) ℝ) (ζ : PTSpace n mb) : Set (Fin n → ℝ) :=
  {x | ζ.1 - Matrix.of ζ.2 *ᵥ x ∈ posW W}

/-- `Ξ̃_{p,T}`, the support of the marginal distribution of `(p, T)`, p. 316. -/
noncomputable def suppPT (μ : Measure (DataSpace n nb mb)) : Set (PTSpace n mb) :=
  (μ.map projPT).support

/-- The induced constraint set `K₂ = ⋂_{ζ ∈ Ξ̃_{p,T}} K₂(ζ)`, Corollary 4.5, p. 316. -/
noncomputable def K2 (μ : Measure (DataSpace n nb mb)) (W : Matrix (Fin mb) (Fin nb) ℝ) :
    Set (Fin n → ℝ) :=
  ⋂ ζ ∈ suppPT μ, K2of W ζ

/-- The feasible region `K = K₁ ∩ K₂` of the deterministic equivalent program, p. 318. -/
noncomputable def K {m : ℕ} (μ : Measure (DataSpace n nb mb)) (W : Matrix (Fin mb) (Fin nb) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  K1 A b ∩ K2 μ W

end Wets1974.Stability


