-- Prove2me | Definitions.Def_OLPRegret_Assumptions
-- name    : OLPRegret_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:04.759701+00:00
-- url     : https://prove2.me/theorems/24de5c8c-210a-420e-91b0-95ab62d64e82
-- title:
--   The online linear program: customers, the limiting dual, and Assumptions 2–6
-- statement:
--   A **customer** is a pair $(u,a)$ of a utility $u\in\mathbb R$ and a resource bundle $a\in\mathbb R^m$, drawn from a law $\mu$ on $\mathbb R\times\mathbb R^m$. Vectors are ordered componentwise and $\mathbb R^m$ carries the Euclidean norm. Write $\Delta(y)=u-a'y$ for the **surplus** of a customer at shadow price $y$.
--
--   The **limiting dual** is
--   $$
--   \Lambda_\infty^b(y)=b'y+\mathrm E\big(\Delta_1(y)^+\big),
--   $$
--   its gradient is $\dot\Lambda_\infty^b(y)=b-\mathrm E(\mathbb 1\{\Delta_1(y)>0\}a_1)$, and its Hessian is $\ddot\Lambda_\infty(y)=-\partial_y\mathrm E(\mathbb 1\{\Delta_1(y)>0\}a_1)$. Near $\beta$ the limiting shadow price $y_\infty^b$ is the minimizer of $\Lambda_\infty^b$ over $\mathbb R^m_+$.
--
--   For an endowment $\beta\in\mathbb R^m_+$ the standing assumptions are:
--
--   1. (Assumption 2) $u_1,a_1\ge0$ almost surely;
--   2. (Assumption 3) $\mathrm E(u_1)<\infty$;
--   3. (Assumption 4) $a_1\le\alpha$ almost surely, for some $\alpha\in\mathbb R^m_+$;
--   4. (Assumption 5) there is a minimizer $y_\infty^\beta>0$ of $\Lambda_\infty^\beta$ over $\mathbb R^m_+$;
--   5. (Assumption 6) the Jacobian of $y\mapsto\mathrm E(\mathbb 1\{\Delta_1(y)>0\}a_1)$ exists, is full rank, and is continuous in a neighbourhood of that $y_\infty^\beta$.
--
--   These assumptions are every hypothesis of the paper's Theorems 1 and 3; the utility $u_1$ may be unbounded.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin m)`, whose order is the predicate `VLe`. Assumption 1 (i.i.d. customers) is structural: samples have the product law `sampleLaw`. `yInf` is a chosen minimizer when one exists and `0` otherwise; only its values near $\beta$ are used. Under Assumptions 2–4 both integrands are integrable.
-- source:
--   Bray, arXiv:1912.08917v6, §4.1, pp.17–21: Assumptions 1–6, (20), (22), (23), Lemma 1, Lemma 2

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace OLPRegret

/-- The resource space `ℝᵐ` with the Euclidean norm of the balls `B_δ(·)` of Bray,
*Logarithmic Regret in Multisecretary and Online Linear Programs with Continuous Valuations*,
arXiv:1912.08917v6, List of Symbols, p.35. -/
abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- A customer `(u, a)`: utility `u = z.1` and resource bundle `a = z.2`
(Bray, arXiv:1912.08917v6, §4.1, p.17). -/
abbrev Customer (m : ℕ) := ℝ × E m

/-- The componentwise order on `ℝᵐ` used throughout the paper (`a ≤ tb`, `a₁ ≤ α`).

**Formalization Note** `EuclideanSpace` carries no order instance, so the order is this
predicate. -/
def VLe {m : ℕ} (x y : E m) : Prop := ∀ i, x i ≤ y i

/-- `x ∈ ℝᵐ₊`, componentwise. -/
def VNonneg {m : ℕ} (x : E m) : Prop := ∀ i, 0 ≤ x i

/-- The surplus `Δ(y) = u − a′y` of a customer at shadow price `y`
(Bray, arXiv:1912.08917v6, (20), p.19). -/
noncomputable def surplus {m : ℕ} (z : Customer m) (y : E m) : ℝ := z.1 - inner ℝ z.2 y

/-- The limiting dual `Λ∞ᵇ(y) = b′y + E(Δ₁(y)⁺)` (Bray, arXiv:1912.08917v6, (22), p.19).

**Formalization Note** Under Assumptions 2–4 the integrand is integrable: `0 ≤ Δ₁(y)⁺ ≤ u₁ + ‖α‖‖y‖`
almost surely on the orthant, so the Bochner integral is not a junk value. -/
noncomputable def LambdaInf {m : ℕ} (μ : Measure (Customer m)) (b y : E m) : ℝ :=
  inner ℝ b y + ∫ z, max (surplus z y) 0 ∂μ

/-- The mean consumption rate `G(y) = E(𝟙{Δ₁(y) > 0}a₁)` (Bray, arXiv:1912.08917v6,
Assumption 6, p.20).

**Formalization Note** Under Assumptions 2 and 4 the integrand is bounded by `‖α‖` almost surely. -/
noncomputable def consumption {m : ℕ} (μ : Measure (Customer m)) (y : E m) : E m :=
  ∫ z, (if 0 < surplus z y then z.2 else 0) ∂μ

/-- The limiting gradient `Λ̇∞ᵇ(y) = b − E(𝟙{Δ₁(y) > 0}a₁)` (Bray, arXiv:1912.08917v6, (23),
p.21). -/
noncomputable def LambdaDotInf {m : ℕ} (μ : Measure (Customer m)) (b y : E m) : E m :=
  b - consumption μ y

/-- The limiting Hessian `Λ̈∞(y) = −∂/∂y E(𝟙{Δ₁(y) > 0}a₁)` (Bray, arXiv:1912.08917v6, Lemma 1,
p.20). -/
noncomputable def hessInf {m : ℕ} (μ : Measure (Customer m)) (y : E m) : E m →L[ℝ] E m :=
  -fderiv ℝ (consumption μ) y

/-- `y` minimizes `f` over the orthant `ℝᵐ₊`. -/
def IsMinimizer {m : ℕ} (f : E m → ℝ) (y : E m) : Prop :=
  VNonneg y ∧ ∀ z, VNonneg z → f y ≤ f z

open scoped Classical in
/-- The limiting shadow price `y∞ᵇ` (Bray, arXiv:1912.08917v6, Lemma 2, p.20).

**Formalization Note** Lemma 2 gives a unique minimizer only for `b` near `β`. This is a chosen
minimizer of `Λ∞ᵇ` when one exists, and `0` otherwise; only its values near `β` are ever used. -/
noncomputable def yInf {m : ℕ} (μ : Measure (Customer m)) (b : E m) : E m :=
  if h : ∃ y, IsMinimizer (LambdaInf μ b) y then h.choose else 0

/-- Assumptions 2–6 of Bray, arXiv:1912.08917v6, pp.17, 19–20, for the customer law `μ` and the
endowment `β`:

* Assumption 2: `u₁, a₁ ≥ 0` almost surely;
* Assumption 3: `E(u₁) < ∞`;
* Assumption 4: `a₁ ≤ α` almost surely, for some `α ∈ ℝᵐ₊`;
* Assumptions 5 and 6: `Λ∞ᵝ` has a minimizer `y∞ᵝ > 0` over `ℝᵐ₊`, and the Jacobian of
  `y ↦ E(𝟙{Δ₁(y) > 0}a₁)` exists, is full rank and is continuous in a neighbourhood of that `y∞ᵝ`.

**Formalization Note** Assumption 1 (i.i.d. customers) is structural: a sample of horizon `n` has
law `sampleLaw μ n`, the `n`-fold product of `μ`. Nothing bounds `u₁` (p.18). -/
structure Assumptions {m : ℕ} (μ : Measure (Customer m)) (β : E m) : Prop where
  /-- Assumption 2. -/
  nonneg : ∀ᵐ z ∂μ, 0 ≤ z.1 ∧ VNonneg z.2
  /-- Assumption 3. -/
  integrable_utility : Integrable (fun z : Customer m => z.1) μ
  /-- Assumption 4. -/
  bounded_bundle : ∃ α : E m, VNonneg α ∧ ∀ᵐ z ∂μ, VLe z.2 α
  /-- Assumptions 5 and 6, at the same point `y∞ᵝ`. -/
  regular : ∃ yβ : E m, IsMinimizer (LambdaInf μ β) yβ ∧ (∀ i, 0 < yβ i) ∧
    ∃ U ∈ 𝓝 yβ, ∃ J : E m → (E m →L[ℝ] E m),
      (∀ y ∈ U, HasFDerivAt (consumption μ) (J y) y ∧ (J y).IsInvertible) ∧ ContinuousOn J U

end OLPRegret


