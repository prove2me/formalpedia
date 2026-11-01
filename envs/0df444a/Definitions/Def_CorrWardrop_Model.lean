-- Prove2me | Definitions.Def_CorrWardrop_Model
-- name    : CorrWardrop_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:44.895388+00:00
-- url     : https://prove2.me/theorems/2a2e84dd-1101-44eb-8105-4882cd4ce442
-- title:
--   Nonatomic games, Wardrop equilibria, (coarse) correlated Wardrop equilibria and convex potentials (Definitions 1, 4, 5)
-- statement:
--   This module sets up the complete-information nonatomic games of Koessler, Scarsini and Tomala (§4) and their equilibrium notions.
--
--   **Nonatomic game.** A nonatomic game $\Gamma=(\mathcal K,\gamma,\mathcal A,c)$ consists of
--
--   1. a finite set $\mathcal K$ of populations, population $k$ having size $\gamma^k>0$;
--   2. for each population $k$ a finite set of actions $\mathcal A^k$;
--   3. for each $k\in\mathcal K$ and $a\in\mathcal A^k$ a continuous cost function $c^k_a:\mathcal Y\to\mathbb R$.
--
--   A flow profile is a vector $y=(y^k_a)_{k\in\mathcal K,a\in\mathcal A^k}$, where $y^k_a$ is the mass of population $k$ playing $a$. The set of flow profiles is
--   $$
--   \mathcal Y=\prod_{k\in\mathcal K}\Delta_{\gamma^k}(\mathcal A^k),\qquad \Delta_\gamma(J)=\Big\{y\in\mathbb R^J:\ y_j\ge 0\ \forall j,\ \sum_{j\in J}y_j=\gamma\Big\}.
--   $$
--   $\Delta(\mathcal Y)$ is the set of Borel probability distributions on $\mathcal Y$.
--
--   **Wardrop equilibrium.** $y\in\mathcal Y$ is a WE if $y^k_a\,c^k_a(y)\le y^k_a\,c^k_b(y)$ for all $k$ and all $a,b\in\mathcal A^k$ (4.1). $\mathrm{WE}(\Gamma)$ is the set of WE.
--
--   **Correlated and coarse correlated Wardrop equilibria.** $\mu\in\Delta(\mathcal Y)$ is a CWE if for all $k$ and $a,b\in\mathcal A^k$
--   $$
--   \int y^k_a\,c^k_a(y)\,d\mu(y)\le\int y^k_a\,c^k_b(y)\,d\mu(y),\tag{4.2}
--   $$
--   and a CCWE if for all $k$ and $b\in\mathcal A^k$
--   $$
--   \int\sum_{a\in\mathcal A^k}y^k_a\,c^k_a(y)\,d\mu(y)\le\int\gamma^k\,c^k_b(y)\,d\mu(y).\tag{4.3}
--   $$
--   $\Delta(\mathrm{WE}(\Gamma))$ is the set of distributions over WE.
--
--   **Potential.** $\Phi$ is a potential of $\Gamma$ on an open neighbourhood $U$ of $\mathcal Y$ if $\Phi$ is continuously differentiable on $U$ and $\partial\Phi(y)/\partial y^k_a=c^k_a(y)$ for every $k$, $a\in\mathcal A^k$ and $y\in\mathcal Y$ (4.7). It is a convex potential if moreover $U$ is convex and $\Phi$ is convex on $U$; $\Gamma$ has the convex potential $\Phi$ if this holds for some such $U$.
--
--   These objects are the vocabulary of Proposition 4: with a convex potential, $\mathrm{CCWE}(\Gamma)=\mathrm{CWE}(\Gamma)=\Delta(\mathrm{WE}(\Gamma))$.
--
--   **Formalization Note.** Flow profiles live in the dependent function space $\prod_k\mathbb R^{\mathcal A^k}$ (`Flow A`), $\mathcal Y$ is the subtype `FlowSet γ`, and the costs are continuous functions on that subtype. $\Delta(\mathcal Y)$ is `ProbabilityMeasure` on the subtype with its Borel σ-algebra; every integrand above is continuous on the compact set $\mathcal Y$, hence integrable. $\Delta(\mathrm{WE}(\Gamma))$ is encoded as "almost every flow is a WE", which equals $\mu(\mathrm{WE}(\Gamma))=1$ because $\mathrm{WE}(\Gamma)$ is closed. The partial derivative $\partial\Phi/\partial y^k_a$ is the Fréchet derivative of $\Phi$ applied to the unit vector $e^k_a$. Neither $\mathcal K$ nor the $\mathcal A^k$ is assumed nonempty. "Convex potential" is read as convexity on an open convex neighbourhood of $\mathcal Y$: convexity on $\mathcal Y$ alone does not give Proposition 4 (for $\Phi(y)=(y_a+y_b-1)y_a$ and $c_a=c_b=y_a$, which is convex on $\mathcal Y$ where it vanishes, the WE $(1,0)$ and $(\tfrac12,\tfrac12)$ have different costs).
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, Notation and (1.1), p.5; Definition 1, pp.5–6 (with |Θ| = 1, §4, p.16); (4.1), Definition 4, (4.2), (4.3), p.16; Definition 5, (4.7), p.17; "convex potential", Proposition 4, p.18

import Mathlib

open MeasureTheory

namespace CorrWardrop

/-- The flow space `ℝ^{⊔_k A^k}`: a flow profile `y` assigns the mass `y k a = y^k_a` to every
action `a ∈ A^k` of every population `k ∈ K`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Definition 1(b), p.5, and notation (1.1), p.5.

Formalization Note: the flow space is the dependent function type `(k : K) → A k → ℝ`, a
finite-dimensional normed space (sup norm) when `K` and every `A k` are finite. It is the ambient
space of the potential `Φ` of Definition 5. -/
abbrev Flow {K : Type*} (A : K → Type*) : Type _ := (k : K) → A k → ℝ

/-- The set of flow profiles `Y = ×_{k ∈ K} Δ_{γ^k}(A^k)`, where
`Δ_γ(J) = {y ∈ ℝ^J : ∀ j, y_j ≥ 0, ∑_j y_j = γ}`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, (1.1) and (2.1), p.5. -/
def FlowSet {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)] (γ : K → ℝ) :
    Set (Flow A) :=
  {y | (∀ k a, 0 ≤ y k a) ∧ ∀ k, ∑ a, y k a = γ k}

/-- A nonatomic game `Γ = (K, γ, A, c)` (a Bayesian nonatomic game with a single state).

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Definition 1 (a), (b), (d), pp.5–6, with
`|Θ| = 1` as in §4, p.16: a finite set `K` of populations, each population `k` of size
`γ^k > 0`, a finite set of actions `A^k` for each population, and for each `k` and `a ∈ A^k` a
continuous cost function `c^k_a : Y → ℝ`.

Formalization Note: `K` and the `A k` are the type parameters, with `Fintype` instances; they
are not assumed nonempty (the paper does not assume it; an empty `A^k` makes `Y` empty). The
costs are functions on the subtype `Y` (with the subspace topology), and are required to be
continuous there. -/
structure NonatomicGame (K : Type*) [Fintype K] (A : K → Type*) [∀ k, Fintype (A k)] where
  /-- the size `γ^k` of population `k` -/
  γ : K → ℝ
  /-- every population has positive size -/
  γ_pos : ∀ k, 0 < γ k
  /-- the cost `c^k_a(y)` of action `a` in population `k` at the flow profile `y ∈ Y` -/
  c : (k : K) → A k → FlowSet (A := A) γ → ℝ
  /-- every cost function is continuous on `Y` -/
  continuous_c : ∀ k a, Continuous (c k a)

variable {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]

/-- The set `Y` of flow profiles of the game `Γ`, as a type (a subtype of the flow space). -/
abbrev NonatomicGame.Y (Γ : NonatomicGame K A) : Type _ := FlowSet (A := A) Γ.γ

/-- `y ∈ Y` is a Wardrop equilibrium (WE) of `Γ`: for all `k ∈ K` and all `a, b ∈ A^k`,
`y^k_a c^k_a(y) ≤ y^k_a c^k_b(y)`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, (4.1), p.16. -/
def IsWE (Γ : NonatomicGame K A) (y : Γ.Y) : Prop :=
  ∀ k (a b : A k), (y : Flow A) k a * Γ.c k a y ≤ (y : Flow A) k a * Γ.c k b y

/-- `WE(Γ)`, the set of Wardrop equilibria of `Γ`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, p.16. -/
def WE (Γ : NonatomicGame K A) : Set Γ.Y := {y | IsWE Γ y}

/-- `CWE(Γ)`: the correlated Wardrop equilibria, i.e. the distributions `μ ∈ Δ(Y)` such that
for all `k ∈ K` and all `a, b ∈ A^k`,
`∫ y^k_a c^k_a(y) dμ(y) ≤ ∫ y^k_a c^k_b(y) dμ(y)` (4.2).

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Definition 4, (4.2), p.16.

Formalization Note: `Δ(Y)`, the Borel probability distributions over `Y` (Notation, p.5), is
`ProbabilityMeasure Γ.Y`, with the Borel σ-algebra of the subspace `Y`. Every integrand is a
continuous function on the compact space `Y`, hence bounded and integrable, so the Bochner
integrals are the paper's integrals. -/
def CWE (Γ : NonatomicGame K A) : Set (ProbabilityMeasure Γ.Y) :=
  {μ | ∀ k (a b : A k),
    ∫ y, (y : Flow A) k a * Γ.c k a y ∂(μ : Measure Γ.Y) ≤
      ∫ y, (y : Flow A) k a * Γ.c k b y ∂(μ : Measure Γ.Y)}

/-- `CCWE(Γ)`: the coarse correlated Wardrop equilibria, i.e. the distributions `μ ∈ Δ(Y)` such
that for all `k ∈ K` and all `b ∈ A^k`,
`∫ ∑_{a ∈ A^k} y^k_a c^k_a(y) dμ(y) ≤ ∫ γ^k c^k_b(y) dμ(y)` (4.3).

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Definition 4, (4.3), p.16. -/
def CCWE (Γ : NonatomicGame K A) : Set (ProbabilityMeasure Γ.Y) :=
  {μ | ∀ k (b : A k),
    ∫ y, ∑ a, (y : Flow A) k a * Γ.c k a y ∂(μ : Measure Γ.Y) ≤
      ∫ y, Γ.γ k * Γ.c k b y ∂(μ : Measure Γ.Y)}

/-- `Δ(WE(Γ))`: the probability distributions over `Y` that are concentrated on `WE(Γ)`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, p.16 and p.18 ("distributions over WE"); `Δ(X)`
is defined in the Notation paragraph, p.5.

Formalization Note: a distribution over `WE(Γ)` is encoded as a probability measure on `Y`
under which almost every flow is a WE. `WE(Γ)` is closed in `Y` (the costs are continuous), so
this is the same as `μ(WE(Γ)) = 1`. -/
def DeltaWE (Γ : NonatomicGame K A) : Set (ProbabilityMeasure Γ.Y) :=
  {μ | ∀ᵐ y ∂(μ : Measure Γ.Y), IsWE Γ y}

variable [DecidableEq K] [∀ k, DecidableEq (A k)]

/-- The unit vector `e^k_a` of the flow space in the coordinate `(k, a)`. The directional
derivative of `Φ` along it is the partial derivative `∂Φ/∂y^k_a`. -/
def unitFlow (k : K) (a : A k) : Flow A :=
  Pi.single (M := fun k => A k → ℝ) k (Pi.single (M := fun _ : A k => ℝ) a (1 : ℝ))

/-- `Φ` is a potential of `Γ` on the open set `U`: `U` is an open neighbourhood of `Y`, `Φ` is
continuously differentiable on `U`, and `∂Φ(y)/∂y^k_a = c^k_a(y)` for every `k ∈ K`,
`a ∈ A^k` and `y ∈ Y` (4.7).

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Definition 5, (4.7), p.17.

Formalization Note: `Φ` is a function on the whole flow space; only its values on `U` matter.
The partial derivative `∂Φ(y)/∂y^k_a` is `fderiv ℝ Φ y (unitFlow k a)`; since `U` is open and
`Φ` is `C¹` on `U`, this is the derivative of `Φ` at `y ∈ Y ⊆ U`. The page writes "a ∈ A"
(a printed slip for `a ∈ A^k`). -/
def IsPotentialOn (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (U : Set (Flow A)) : Prop :=
  IsOpen U ∧ FlowSet (A := A) Γ.γ ⊆ U ∧ ContDiffOn ℝ 1 Φ U ∧
    ∀ (y : Γ.Y) k (a : A k), fderiv ℝ Φ (y : Flow A) (unitFlow k a) = Γ.c k a y

/-- `Φ` is a convex potential of `Γ` on `U`: a potential on the open neighbourhood `U` of `Y`
(Definition 5) with `U` convex and `Φ` convex on `U`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Definition 5, p.17, and "convex potential",
p.18 (Proposition 4).

Formalization Note: "convex potential" is read as convexity of `Φ` on its (convex, open)
domain, not merely on `Y`. Any open neighbourhood of the compact convex `Y` contains a convex
open one, so requiring `U` convex loses nothing. Convexity on `Y` alone would not suffice for
Proposition 4. -/
def IsConvexPotentialOn (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (U : Set (Flow A)) : Prop :=
  IsPotentialOn Γ Φ U ∧ Convex ℝ U ∧ ConvexOn ℝ U Φ

/-- `Φ` is a convex potential of `Γ`: it is a convex potential on some open convex neighbourhood
`U` of `Y`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, Definition 5, p.17; Proposition 4, p.18. -/
def HasConvexPotential (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) : Prop :=
  ∃ U, IsConvexPotentialOn Γ Φ U

end CorrWardrop


