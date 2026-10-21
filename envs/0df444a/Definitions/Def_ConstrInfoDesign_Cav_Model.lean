-- Prove2me | Definitions.Def_ConstrInfoDesign_Cav_Model
-- name    : ConstrInfoDesign_Cav_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:39.79878+00:00
-- url     : https://prove2.me/theorems/68515c38-63b5-4ea2-8d4d-8eb06b005340
-- title:
--   §2–3, CID, Definitions 2.1–2.2, (3.1), pp. 5–7 — constrained information design: Bayes-plausible distributions, the value V, F, C, f^ḡ, and the concave hull
-- statement:
--   This file sets up the constrained information design problem (CID) of Doval and Skreta.
--
--   Let $\Omega = \{\omega_1, \dots, \omega_N\}$ be a finite set of states and let $\Delta(\Omega) \subseteq \mathbb R^N$ be the simplex of beliefs. A designer faces an objective $f : \Delta(\Omega) \to \mathbb R$, $I$ inequality constraint functions $\bar g_I = (\bar g_1, \dots, \bar g_I)$ and $E$ equality constraint functions $\bar g_E = (\bar g_{I+1}, \dots, \bar g_{I+E})$, all measurable. A parameter is a point $(\mu, \tilde\gamma) \in \mathbb R^{N+I+E}$, with $\tilde\gamma = (\tilde\gamma_I, \tilde\gamma_E)$ the constraint thresholds.
--
--   1. **Bayes-plausible distributions.** $\Delta_{\mu_0}(\Delta(\Omega))$ is the set of Borel probability measures $\tau$ on $\Delta(\Omega)$ with mean $\mu_0$, i.e. $\int \mu \, \tau(d\mu) = \mu_0$. No finiteness of the support is required.
--   2. **Feasibility.** A distribution $\tau \in \Delta_{\mu_0}(\Delta(\Omega))$ satisfies the constraints at $(\mu_0, \gamma)$ if every $\bar g_k$ is $\tau$-integrable and, component-wise, $\mathbb E_\tau[\bar g_I(\mu)] \ge \gamma_I$ and $\mathbb E_\tau[\bar g_E(\mu)] = \gamma_E$.
--   3. **The value of CID.**
--   $$V(\mu_0, \gamma) = \sup\big\{\mathbb E_\tau[f(\mu)] : \tau \in \Delta_{\mu_0}(\Delta(\Omega)) \text{ satisfies the constraints at } (\mu_0,\gamma),\ f \text{ is } \tau\text{-integrable}\big\},$$
--   a supremum in the extended reals, equal to $-\infty$ when no $\tau$ is feasible.
--   4. **The feasibility set** (Definition 2.2): $\mathcal F = \{(\mu, \tilde\gamma) \in \Delta(\Omega) \times \mathbb R^{I+E} : \text{some } \tau \in \Delta_\mu(\Delta(\Omega)) \text{ satisfies the constraints at } (\mu, \tilde\gamma)\}$.
--   5. **The pointwise set**: $C = \{(\mu, \tilde\gamma) \in \Delta(\Omega) \times \mathbb R^{I+E} : \bar g_I(\mu) \ge \tilde\gamma_I,\ \bar g_E(\mu) = \tilde\gamma_E\}$.
--   6. **The modified objective** (3.1): $f^{\bar g}(\mu, \tilde\gamma) = f(\mu) - \delta(\mu, \tilde\gamma \mid C)$, that is $f(\mu)$ on $C$ and $-\infty$ off $C$.
--   7. **Hypograph and concave hull** (Definition 2.1). For an extended-real-valued $h$ on a real vector space, $\operatorname{hypo} h = \{(x, y) : y \in \mathbb R,\ y \le h(x)\}$ and
--   $$(\operatorname{cav} h)(x) = \sup\{y \in \mathbb R : (x, y) \in \operatorname{conv}(\operatorname{hypo} h)\},$$
--   with $\sup \emptyset = -\infty$.
--
--   These are the objects in terms of which Theorem 3.1 ($V = \operatorname{cav} f^{\bar g}$) and its supporting results are stated.
--
--   **Formalization Note** States are `Fin N` and beliefs are points of `Fin N → ℝ`; $\Delta(\Omega)$ is `stdSimplex ℝ (Fin N)`. The parameter space $\mathbb R^{N+I+E}$ is the product `(Fin N → ℝ) × ((Fin I → ℝ) × (Fin E → ℝ))`. Distributions over posteriors are Borel measures on `Fin N → ℝ` giving the complement of the simplex measure zero; the mean is the Bochner integral of the identity. The functions $f, \bar g_k$ are total on `Fin N → ℝ`, and their values off the simplex never matter. Because Lean's integral of a non-integrable function is $0$, $\tau$-integrability of every $\bar g_k$ (in feasibility, hence in $\mathcal F$) and of $f$ (in $V$) is built in; the paper leaves it implicit. $V$, $f^{\bar g}$ and cav take values in `EReal`, where `sSup ∅ = ⊥` is the paper's $-\infty$.
-- source:
--   Doval and Skreta, Constrained Information Design, arXiv:1811.03588v3, pp. 5–7, (CID), Definitions 2.1–2.2, (3.1)

import Mathlib

namespace ConstrInfoDesign.Cav

open MeasureTheory

/-- The parameter space `ℝ^{N+I+E}` of the program (CID) (Doval–Skreta, p. 5): a prior
`µ ∈ ℝ^N` together with inequality thresholds `γ_I ∈ ℝ^I` and equality thresholds `γ_E ∈ ℝ^E`. -/
abbrev ParamSpace (N nI nE : ℕ) : Type :=
  (Fin N → ℝ) × ((Fin nI → ℝ) × (Fin nE → ℝ))

/-- `τ ∈ Δ_{µ0}(Δ(Ω))` (p. 5): `τ` is a Borel probability measure on `ℝ^N` concentrated on the
belief simplex `Δ(Ω) = stdSimplex ℝ (Fin N)`, whose mean (Bochner integral of the identity) is `µ0`. -/
def IsBayesPlausible {N : ℕ} (mu0 : Fin N → ℝ) (τ : Measure (Fin N → ℝ)) : Prop :=
  IsProbabilityMeasure τ ∧ τ (stdSimplex ℝ (Fin N))ᶜ = 0 ∧ ∫ mu, mu ∂τ = mu0

/-- `τ` is feasible for (CID) at `(µ0, γ_I, γ_E)` (p. 5): `τ ∈ Δ_{µ0}(Δ(Ω))`, every constraint map
`ḡ_k` is `τ`-integrable, `E_τ[ḡ_I] ≥ γ_I` and `E_τ[ḡ_E] = γ_E` component-wise. -/
def IsConstraintFeasible {N nI nE : ℕ} (gI : Fin nI → (Fin N → ℝ) → ℝ)
    (gE : Fin nE → (Fin N → ℝ) → ℝ) (mu0 : Fin N → ℝ) (γI : Fin nI → ℝ) (γE : Fin nE → ℝ)
    (τ : Measure (Fin N → ℝ)) : Prop :=
  IsBayesPlausible mu0 τ ∧ (∀ i, Integrable (gI i) τ) ∧ (∀ e, Integrable (gE e) τ) ∧
    (∀ i, γI i ≤ ∫ mu, gI i mu ∂τ) ∧ (∀ e, ∫ mu, gE e mu ∂τ = γE e)

/-- The value `V(µ0, γ)` of (CID) (p. 5), in the extended reals: the supremum of `E_τ[f]` over all
feasible `τ` for which `f` is `τ`-integrable; `sSup ∅ = ⊥ = −∞` when (CID) is infeasible. -/
noncomputable def value {N nI nE : ℕ} (f : (Fin N → ℝ) → ℝ) (gI : Fin nI → (Fin N → ℝ) → ℝ)
    (gE : Fin nE → (Fin N → ℝ) → ℝ) (mu0 : Fin N → ℝ) (γI : Fin nI → ℝ) (γE : Fin nE → ℝ) :
    EReal :=
  sSup {v : EReal | ∃ τ : Measure (Fin N → ℝ), IsConstraintFeasible gI gE mu0 γI γE τ ∧
    Integrable f τ ∧ v = ((∫ mu, f mu ∂τ : ℝ) : EReal)}

/-- The feasibility set `F` (Definition 2.2, p. 6): the parameters `(µ, γ̃) ∈ Δ(Ω) × ℝ^{I+E}` at which
some `τ ∈ Δ_µ(Δ(Ω))` satisfies the constraints of (CID) in expectation. -/
def feasibleSet {N nI nE : ℕ} (gI : Fin nI → (Fin N → ℝ) → ℝ) (gE : Fin nE → (Fin N → ℝ) → ℝ) :
    Set (ParamSpace N nI nE) :=
  {p | p.1 ∈ stdSimplex ℝ (Fin N) ∧
    ∃ τ : Measure (Fin N → ℝ), IsConstraintFeasible gI gE p.1 p.2.1 p.2.2 τ}

/-- The set `C` (p. 7): the parameters `(µ, γ̃) ∈ Δ(Ω) × ℝ^{I+E}` at which the constraints hold
pointwise, `ḡ_I(µ) ≥ γ̃_I` and `ḡ_E(µ) = γ̃_E`. -/
def pointwiseSet {N nI nE : ℕ} (gI : Fin nI → (Fin N → ℝ) → ℝ) (gE : Fin nE → (Fin N → ℝ) → ℝ) :
    Set (ParamSpace N nI nE) :=
  {p | p.1 ∈ stdSimplex ℝ (Fin N) ∧ (∀ i, p.2.1 i ≤ gI i p.1) ∧ ∀ e, gE e p.1 = p.2.2 e}

open Classical in
/-- The modified objective `f^ḡ(µ, γ̃) = f(µ) − δ(µ, γ̃ | C)` of (3.1) (p. 7): `f(µ)` on `C` and
`−∞` off `C`. -/
noncomputable def modObj {N nI nE : ℕ} (f : (Fin N → ℝ) → ℝ) (gI : Fin nI → (Fin N → ℝ) → ℝ)
    (gE : Fin nE → (Fin N → ℝ) → ℝ) : ParamSpace N nI nE → EReal :=
  fun p => if p ∈ pointwiseSet gI gE then ((f p.1 : ℝ) : EReal) else ⊥

/-- The hypograph `hypo h = {(x, y) : y ≤ h(x)}` of an extended-real-valued function `h` on a real
vector space, with `y` real (Definition 2.1, p. 6). -/
def hypo {E : Type*} (h : E → EReal) : Set (E × ℝ) :=
  {q | ((q.2 : ℝ) : EReal) ≤ h q.1}

/-- The concave hull (Definition 2.1, p. 6): `(cav h)(x) = sup {y ∈ ℝ | (x, y) ∈ conv (hypo h)}`,
the supremum taken in the extended reals (`sSup ∅ = ⊥ = −∞`). -/
noncomputable def cav {E : Type*} [AddCommGroup E] [Module ℝ E] (h : E → EReal) (x : E) : EReal :=
  sSup {v : EReal | ∃ y : ℝ, (x, y) ∈ convexHull ℝ (hypo h) ∧ v = (y : EReal)}

end ConstrInfoDesign.Cav


