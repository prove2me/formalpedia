-- Prove2me | Definitions.Def_Rudin_ch10_forms
-- name    : Rudin_ch10_forms
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T20:06:23.890888+00:00
-- url     : https://prove2.me/theorems/b8e7b436-f559-422b-9eba-28e37ef27f1b
-- title:
--   Surfaces, differential forms, chains and the boundary operator
-- statement:
--   Rudin's concrete apparatus for Chapter 10. A **$k$-surface** in $\mathbb{R}^n$ is a mapping of a $k$-cell, or of the standard simplex $Q^k$, into $\mathbb{R}^n$ (Definition 10.10). A **$k$-form** is given by its coefficients $a_{i_1\cdots i_k}$, indexed by all tuples of indices as in Rudin's equation (34), and it acts on a $k$-surface $\Phi$ by $$\int_\Phi \omega = \int_D \sum a_{i_1\cdots i_k}(\Phi(u))\,\frac{\partial(\varphi_{i_1},\dots,\varphi_{i_k})}{\partial(u_1,\dots,u_k)}\,du$$ (equation (35)). The **exterior derivative** has coefficients $D_j a_I$; the **pullback** along a differentiable $T$ substitutes $T$ into coefficients and differentials (Theorem 10.22). A **$k$-chain** is a formal integer combination of $k$-surfaces over $Q^k$, and the **boundary** of a $(k)$-surface is the alternating sum $\sum_j (-1)^j$ of its restrictions to the faces of $Q^k$ (Definitions 10.26, 10.28, 10.30). Mathlib has no counterpart to these coordinate-based objects. Integrals over parameter domains are Lebesgue integrals for the volume measure, which agree with Rudin's Riemann integrals for continuous integrands.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, pp. 245-273, Definitions 10.10, 10.11, 10.26, 10.28, 10.30, Sections 10.16-10.19 and Theorem 10.22

import Mathlib

/-!
# Rudin, Chapter 10 — differential forms, surfaces and chains

Definitions transcribed from Walter Rudin, *Principles of Mathematical Analysis*, 3rd edition,
Chapter 10 (Definitions 10.10, 10.11, Sections 10.16–10.19, Definitions 10.26, 10.28, 10.30 and
Theorem 10.22).

Mathlib has differential forms only in the guise of alternating multilinear maps on manifolds;
Rudin's concrete objects — a `k`-form presented by its coefficient functions
`ω = ∑ a_{i₁⋯i_k} dx_{i₁} ∧ ⋯ ∧ dx_{i_k}`, evaluated by integrating a Jacobian over the
parameter domain of a `k`-surface — are set up here from scratch.  Points of `ℝⁿ` are functions
`Fin n → ℝ`.

Two conventions are worth stating. First, a `k`-form is recorded by a coefficient function
indexed by *all* tuples `i : Fin k → Fin n`, not only by increasing ones; this is Rudin's
equation (34), where the indices "range independently from 1 to n", and the anticommutation
relations are then consequences of the definition rather than extra data. Second, the integral
over the parameter domain is the Lebesgue integral for the volume measure, which agrees with
Rudin's Riemann integral (Definition 10.1) for the continuous integrands considered here.
-/

namespace Rudin

open MeasureTheory

/-- The partial derivative `D_s f` of a real function on `ℝᵏ`, in the direction of the `s`-th
coordinate vector. -/
noncomputable def partialDeriv {k : ℕ} (f : (Fin k → ℝ) → ℝ) (s : Fin k) (u : Fin k → ℝ) : ℝ :=
  fderiv ℝ f u (Pi.single s 1)

/-- Rudin, Definition 10.11: a **`k`-form** in `ℝⁿ`, presented by its coefficient functions
`a_{i₁⋯i_k}`, one for each tuple of indices. -/
structure KForm (k n : ℕ) where
  /-- The coefficient `a_{i₁⋯i_k}` of `dx_{i₁} ∧ ⋯ ∧ dx_{i_k}`. -/
  coeff : (Fin k → Fin n) → (Fin n → ℝ) → ℝ

/-- Rudin, Definition 10.11, equation (35): the Jacobian
`∂(φ_{i₁}, …, φ_{i_k}) / ∂(u₁, …, u_k)` of a map `Φ : ℝᵏ → ℝⁿ` along the index tuple `i`. -/
noncomputable def jacobian {k n : ℕ} (Φ : (Fin k → ℝ) → (Fin n → ℝ)) (i : Fin k → Fin n)
    (u : Fin k → ℝ) : ℝ :=
  Matrix.det (Matrix.of fun r s : Fin k => partialDeriv (fun v => Φ v (i r)) s u)

/-- Rudin, Definition 10.10: a **`k`-surface** with parameter domain the `k`-cell `[a, b]`, given
by a mapping of that cell into `ℝⁿ`. -/
structure CellSurface (k n : ℕ) where
  /-- Lower corner of the parameter cell. -/
  lo : Fin k → ℝ
  /-- Upper corner of the parameter cell. -/
  hi : Fin k → ℝ
  /-- The mapping into `ℝⁿ`. -/
  map : (Fin k → ℝ) → (Fin n → ℝ)

/-- Rudin, Definition 10.11, equation (35): the integral of a `k`-form over a `k`-surface whose
parameter domain is a cell. -/
noncomputable def integralOverCell {k n : ℕ} (ω : KForm k n) (Φ : CellSurface k n) : ℝ :=
  ∫ u in Set.Icc Φ.lo Φ.hi,
    ∑ i : Fin k → Fin n, ω.coeff i (Φ.map u) * jacobian Φ.map i u

/-- Rudin, Example 10.4: the standard `k`-simplex
`Qᵏ = {u : uᵢ ≥ 0, u₁ + ⋯ + u_k ≤ 1}`, the other admissible parameter domain. -/
def stdSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}

/-- Rudin, Definition 10.10: a `k`-surface whose parameter domain is the standard simplex
`Qᵏ`. -/
structure SimplexSurface (k n : ℕ) where
  /-- The mapping of `Qᵏ` into `ℝⁿ`. -/
  map : (Fin k → ℝ) → (Fin n → ℝ)

/-- The integral of a `k`-form over a `k`-surface with parameter domain `Qᵏ`. -/
noncomputable def integralOverSimplex {k n : ℕ} (ω : KForm k n) (Φ : SimplexSurface k n) : ℝ :=
  ∫ u in stdSimplex k, ∑ i : Fin k → Fin n, ω.coeff i (Φ.map u) * jacobian Φ.map i u

/-- Rudin, Definition 10.26: the oriented affine `k`-simplex `[p₀, …, p_k]`, as the affine map
`u ↦ p₀ + ∑ uᵢ (pᵢ - p₀)` of `Qᵏ` into `ℝⁿ`. -/
def affineSimplexMap {k n : ℕ} (p : Fin (k + 1) → (Fin n → ℝ)) : (Fin k → ℝ) → (Fin n → ℝ) :=
  fun u => p 0 + ∑ i : Fin k, u i • (p i.succ - p 0)

/-- The vertices `0, e₁, …, e_k` of the standard simplex `Qᵏ`, i.e. Rudin's identity simplex
`[0, e₁, …, e_k]`. -/
def stdVertices (k : ℕ) : Fin (k + 1) → (Fin k → ℝ) :=
  Fin.cases (0 : Fin k → ℝ) fun j => Pi.single j (1 : ℝ)

/-- Rudin, Definition 10.28: a **`k`-chain**, a formal integer combination of `k`-surfaces with
parameter domain `Qᵏ`. -/
structure Chain (k n : ℕ) where
  /-- The terms of the chain, each with its integer multiplicity. -/
  terms : List (ℤ × SimplexSurface k n)

/-- Rudin, Definition 10.28, equation (87): the integral of a `k`-form over a `k`-chain. -/
noncomputable def Chain.integral {k n : ℕ} (ω : KForm k n) (Ψ : Chain k n) : ℝ :=
  (Ψ.terms.map fun t => (t.1 : ℝ) * integralOverSimplex ω t.2).sum

/-- The `j`-th face of a `(m+1)`-surface with parameter domain `Q^{m+1}`: the surface is
restricted along the affine map of `Qᵐ` onto the face of `[0, e₁, …, e_{m+1}]` obtained by
deleting the `j`-th vertex (Rudin, Definitions 10.29 and 10.30). -/
noncomputable def boundaryFace {m n : ℕ} (Φ : (Fin (m + 1) → ℝ) → (Fin n → ℝ)) (j : Fin (m + 2)) :
    SimplexSurface m n :=
  ⟨Φ ∘ affineSimplexMap fun i : Fin (m + 1) => stdVertices (m + 1) (j.succAbove i)⟩

/-- Rudin, Definition 10.30: the boundary `∂Φ = ∑_j (-1)^j Φ ∘ (j-th face)` of a
`(m+1)`-surface, as an `m`-chain. -/
noncomputable def surfaceBoundary {m n : ℕ} (Φ : SimplexSurface (m + 1) n) : Chain m n :=
  ⟨List.ofFn fun j : Fin (m + 2) => ((-1 : ℤ) ^ (j : ℕ), boundaryFace Φ.map j)⟩

/-- Rudin, Definition 10.30: the boundary of a `(m+1)`-chain, the `m`-chain obtained by taking
the boundary of each term with its multiplicity. -/
noncomputable def Chain.boundary {m n : ℕ} (Ψ : Chain (m + 1) n) : Chain m n :=
  ⟨Ψ.terms.flatMap fun t => (surfaceBoundary t.2).terms.map fun s => (t.1 * s.1, s.2)⟩

/-- Rudin, Section 10.16–10.19: the **exterior derivative** `dω` of a `k`-form, the `(k+1)`-form
whose coefficient at the tuple `(j, i₁, …, i_k)` is the partial derivative `D_j a_{i₁⋯i_k}`. -/
noncomputable def extDeriv {k n : ℕ} (ω : KForm k n) : KForm (k + 1) n where
  coeff := fun i x =>
    fderiv ℝ (ω.coeff fun r : Fin k => i r.succ) x (Pi.single (i 0) (1 : ℝ))

/-- Rudin, Theorem 10.22 and Section 10.21: the **pullback** `ω_T` of a `k`-form in `ℝⁿ` along a
differentiable map `T : ℝᵐ → ℝⁿ`, whose coefficient at `(j₁, …, j_k)` is
`∑_i a_i(T x) ∏_r D_{j_r} T_{i_r}(x)`. -/
noncomputable def pullback {k m n : ℕ} (T : (Fin m → ℝ) → (Fin n → ℝ)) (ω : KForm k n) :
    KForm k m where
  coeff := fun j x =>
    ∑ i : Fin k → Fin n,
      ω.coeff i (T x) * ∏ r : Fin k, partialDeriv (fun v => T v (i r)) (j r) x

end Rudin


