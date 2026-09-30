-- Prove2me | Definitions.Def_Wets1974_Feasibility_Model
-- name    : Wets1974_Feasibility_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:30:50.315126+00:00
-- url     : https://prove2.me/theorems/5dd2e6b6-20e5-47b9-a9c1-2d2634073613
-- title:
--   Stochastic program with fixed recourse (2.1): weak covariance (Def. 2.2), the paper's extended integral, and the feasibility sets of §4
-- statement:
--   This file sets up the model of Wets (1974), §§2–4: the two-stage **stochastic program with fixed recourse**
--
--   $$
--   \inf_{x \ge 0,\ Ax = b}\ Z(x) = E_\xi\Big\{ c(\xi)x + \min_{y \ge 0}\big[\, q(\xi) y \;\big|\; T(\xi)x + Wy = p(\xi) \,\big] \Big\},
--   $$
--
--   and the candidate feasibility sets for the constraints it induces on the first-stage decision $x \in \mathbb{R}^n$.
--
--   **Data.** The recourse matrix $W$ is a fixed real $\bar m \times \bar n$ matrix. The random data $\xi = (c, q, p, T)$ consist of $c \in \mathbb{R}^n$, $q \in \mathbb{R}^{\bar n}$, $p \in \mathbb{R}^{\bar m}$ and an $\bar m \times n$ matrix $T$; $c, q, p, T$ are the coordinate projections of $\xi$. The law of $\xi$ is a probability measure $\mu$ on this finite-dimensional space, equipped with its Borel $\sigma$-algebra. The **support** $\tilde\Xi$ of $\mu$ is the set of points every neighbourhood of which has positive measure; it is the smallest closed set of measure one.
--
--   **Weak covariance condition (Definition 2.2).** $\xi$ satisfies it when, for all indices $i, j, k$, the functions $c_j(\xi)$, $q_j(\xi)p_i(\xi)$ and $q_j(\xi)t_{ik}(\xi)$ are $\mu$-integrable. Integrability of $q$, $p$ or $T$ alone is not required.
--
--   **Recourse function and the paper's integral.** $Q(x,\xi) = \min\{ q(\xi)y \mid Wy = p(\xi) - T(\xi)x,\ y \ge 0\}$, with the conventions $Q = +\infty$ if the program is infeasible and $Q = -\infty$ if it is unbounded below. For an extended-real function $g$ the integral $E\{g\} = \int g\,d\mu$ is the sum of its positive part $\int g^+ d\mu \in [0, +\infty]$ and its negative part $-\int g^- d\mu \in [-\infty, 0]$, where each part is $+\infty$ (resp. $-\infty$) when the integral diverges or the integrand is infinite on a set of positive measure, and the ambiguous case is resolved as $(+\infty) + (-\infty) = +\infty$. The expected recourse is $\mathcal Q(x) = E_\xi\{Q(x,\xi)\}$.
--
--   **Feasibility sets.** With $\operatorname{pos} W = \{ t \mid t = Wy,\ y \ge 0 \}$:
--
--   1. $K_2^\mu = \{ x \mid \text{with probability } 1\ \exists y \ge 0 \text{ such that } Wy = p(\xi) - T(\xi)x \}$;
--   2. $K_2^s = \{ x \mid \mathcal Q(x) < +\infty \}$, the strong feasibility set;
--   3. $K_2^p = \{ x \mid \forall \xi \in \tilde\Xi,\ \exists y \ge 0 \text{ such that } Wy = p(\xi) - T(\xi)x \}$;
--   4. for $\zeta = (p, T)$, $K_2(\zeta) = \{ x \mid p - Tx \in \operatorname{pos} W \}$, and $K_2 = \bigcap_{\zeta \in \tilde\Xi_{p,T}} K_2(\zeta)$, where $\tilde\Xi_{p,T}$ is the support of the marginal law of $(p(\xi), T(\xi))$.
--
--   **Auxiliary notions.** A **convex polyhedron** in $\mathbb{R}^n$ is a set $\{x \mid Gx \ge \alpha\}$ cut out by finitely many weak linear inequalities (this includes $\emptyset$ and $\mathbb{R}^n$). "$T$ is fixed" means $T(\xi) = T_0$ with probability one for some matrix $T_0$. The **closed positive hull** $\operatorname{pos}(S)$ of a set $S$ of $(p,T)$-space is the closure of the set of nonnegative linear combinations of points of $S$ (so $\operatorname{pos}(\emptyset) = \{0\}$), and a **convex polyhedral cone** is the set of nonnegative combinations of finitely many vectors.
--
--   These objects are the common vocabulary of Theorems 4.1–4.10 of the paper: the region of finiteness of $\mathcal Q$ and its polyhedral structure.
--
--   **Formalization Note.** The paper writes $c, q, \pi$ as row vectors and suppresses transposes; here all vectors are functions `Fin k → ℝ` and matrix–vector products are `Matrix.mulVec`. The paper's sample space $\Xi \subseteq \mathbb{R}^N$ only carries $\mu$, so $\mu$ is taken on the whole data space. $\tilde\Xi$ is Mathlib's `Measure.support` and $\tilde\Xi_{p,T}$ is the support of the pushforward of $\mu$ under the continuous (hence measurable) projection $\xi \mapsto (p, T)$. $Q$ is the platform definition `KallMayer.Recourse.PointwiseRecourse`, an `EReal`-valued infimum that equals $+\infty$ on infeasibility and $-\infty$ on unboundedness. The integral is written out with two lower Lebesgue integrals and an explicit `if` that returns $+\infty$ whenever the positive part diverges, because Mathlib's `EReal` subtraction would give $(+\infty) - (+\infty) = -\infty$, the opposite of the paper's convention. The paper's set on p. 314 (iii) is printed $K_2^p$ ("possible" points).
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, pp. 311-316: Eq. (2.1), Definition 2.2 (p. 311), definition of Q and of the integral (p. 312), Eq. (3.1) (p. 313), K₂^μ, K₂^s, K₂^p (p. 314), pos W (p. 315), Eq. (4.4) and K₂ of Corollary 4.5 (p. 316), pos(Ξ̃_{p,T}) (Theorem 4.7, p. 317)

import Mathlib
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse

namespace Wets1974.Feasibility

open MeasureTheory Matrix

/-- The data space of problem (2.1), p. 311: a point `ξ = (c, q, p, T)` with `c ∈ ℝⁿ`,
`q ∈ ℝ^n̄`, `p ∈ ℝ^m̄` and `T` an `m̄ × n` matrix (stored as `Fin m̄ → Fin n → ℝ`).
It carries the product (Borel) measurable structure and the product topology. -/
abbrev DataSpace (n nb mb : ℕ) : Type :=
  (Fin n → ℝ) × (Fin nb → ℝ) × (Fin mb → ℝ) × (Fin mb → Fin n → ℝ)

/-- The space of the pair `(p, T)`, the right-hand side and technology matrix. -/
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
  else ((∫⁻ ξ, (g ξ).toENNReal ∂μ : ENNReal) : EReal) - ((∫⁻ ξ, (-g ξ).toENNReal ∂μ : ENNReal) : EReal)

/-- The expected recourse `𝒬(x) = E_ξ{Q(x, ξ)}`, (3.1), p. 313, with the paper's integral. -/
noncomputable def expectedRecourse (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (x : Fin n → ℝ) : EReal :=
  paperIntegral μ (Q W x)

/-- `pos W = {t | t = W y, y ≥ 0}`, p. 315. -/
def posW (W : Matrix (Fin mb) (Fin nb) ℝ) : Set (Fin mb → ℝ) :=
  {t | ∃ y : Fin nb → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = t}

/-- `K₂^μ = {x | with probability 1 ∃ y ≥ 0 such that W y = p(ξ) − T(ξ) x}`, p. 314 (i). -/
def K2mu (μ : Measure (DataSpace n nb mb)) (W : Matrix (Fin mb) (Fin nb) ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∀ᵐ ξ ∂μ, ∃ y : Fin nb → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = pOf ξ - TOf ξ *ᵥ x}

/-- `K₂^s = {x | 𝒬(x) < +∞}`, p. 314 (ii), the strong feasibility set. -/
def K2s (μ : Measure (DataSpace n nb mb)) (W : Matrix (Fin mb) (Fin nb) ℝ) :
    Set (Fin n → ℝ) :=
  {x | expectedRecourse μ W x < ⊤}

/-- `K₂^p = {x | ∀ ξ ∈ Ξ̃, ∃ y ≥ 0 such that W y = p(ξ) − T(ξ) x}`, p. 314 (iii), where
`Ξ̃ = μ.support` is the support of the distribution of `ξ`. -/
def K2supp (μ : Measure (DataSpace n nb mb)) (W : Matrix (Fin mb) (Fin nb) ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∀ ξ ∈ μ.support, ∃ y : Fin nb → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = pOf ξ - TOf ξ *ᵥ x}

/-- `K₂(ζ) = {x | p − T x ∈ pos W}` for `ζ = (p, T)`, (4.4), p. 316. -/
def K2of (W : Matrix (Fin mb) (Fin nb) ℝ) (ζ : PTSpace n mb) : Set (Fin n → ℝ) :=
  {x | ζ.1 - Matrix.of ζ.2 *ᵥ x ∈ posW W}

/-- `Ξ̃_{p,T}`, the support of the marginal distribution of `(p, T)`, p. 316. -/
noncomputable def suppPT (μ : Measure (DataSpace n nb mb)) : Set (PTSpace n mb) :=
  (μ.map projPT).support

/-- `K₂ = ⋂_{ζ ∈ Ξ̃_{p,T}} K₂(ζ)`, Corollary 4.5, p. 316. -/
noncomputable def K2 (μ : Measure (DataSpace n nb mb)) (W : Matrix (Fin mb) (Fin nb) ℝ) :
    Set (Fin n → ℝ) :=
  ⋂ ζ ∈ suppPT μ, K2of W ζ

/-- A convex polyhedron in `ℝⁿ`: the solution set of finitely many weak linear inequalities
`G x ≥ α`. This includes `∅` and `ℝⁿ`. -/
def IsPolyhedron (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (l : ℕ) (G : Matrix (Fin l) (Fin n) ℝ) (α : Fin l → ℝ), S = {x | ∀ i, α i ≤ (G *ᵥ x) i}

/-- "`T` is fixed": `T(ξ)` equals one matrix `T₀` with probability one. -/
def TFixed (μ : Measure (DataSpace n nb mb)) : Prop :=
  ∃ T₀ : Matrix (Fin mb) (Fin n) ℝ, ∀ᵐ ξ ∂μ, TOf ξ = T₀

/-- The closed positive hull `pos(S)` of a set `S` of `(p, T)`-space: the closure of the
set of nonnegative linear combinations of points of `S` (with `pos ∅ = {0}`). -/
def closedPosHull (S : Set (PTSpace n mb)) : Set (PTSpace n mb) :=
  closure (PointedCone.hull ℝ S : Set (PTSpace n mb))

/-- A convex polyhedral cone in `(p, T)`-space: the set of nonnegative linear combinations of
finitely many vectors. -/
def IsPolyhedralCone (C : Set (PTSpace n mb)) : Prop :=
  ∃ F : Finset (PTSpace n mb), C = (PointedCone.hull ℝ (F : Set (PTSpace n mb)) : Set _)

end Wets1974.Feasibility


