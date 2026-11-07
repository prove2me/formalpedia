-- Prove2me | Definitions.Def_QuadBogolyubov_QuadVariety
-- name    : QuadBogolyubov_QuadVariety
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:30.195934+00:00
-- url     : https://prove2.me/theorems/6c67771f-a241-43af-aec3-54588d22e019
-- title:
--   Quadratic variety of complexity $(d_1,d_2)$ in $\mathbb F_2^n$
-- statement:
--   A **quadratic variety of complexity $(d_1,d_2)$** in $\mathbb F_2^n$ is given by linearly independent linear functions $\ell_1,\dots,\ell_{d_1}$ with values $a_i$, which cut out the affine subspace
--   $$V=\{x\in\mathbb F_2^n:\ \ell_i(x)=a_i\ \text{for all } i\},$$
--   and quadratic polynomials $q_1,\dots,q_{d_2}$ with values $b_j$ whose quadratic parts are linearly independent on $V$: for every $\lambda\in\mathbb F_2^{d_2}\setminus\{0\}$, the function $\sum_j\lambda_jq_j$ does not agree on $V$ with any polynomial of degree at most one. The variety is
--   $$W=\{x\in V:\ q_j(x)=b_j\ \text{for all } j\}.$$
--   The associated linear subspace is $V_0=V+V=\bigcap_i\ker\ell_i$, and the complexity (the paper's "codimension") is measured by $d_1+d_2$.
--
--   This is the structure that replaces the subspace of Bogolyubov's lemma.
--
--   **Formalization Note** The object is the representation, not the point set, because the rank depends on the representation. The printed independence condition, "$\lambda_0+\lambda_1q_1+\dots+\lambda_{d_2}q_{d_2}$ is not a linear function for any $(\lambda_0,\dots,\lambda_{d_2})\neq 0$", fails for $\lambda=(1,0,\dots,0)$; it is encoded as the property the same sentence names, independence of the quadratic parts. A variety may be empty; statements that need a point say so.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §3, p.9; p.68

import Mathlib
import Definitions.Def_QuadBogolyubov_IsQuadraticPoly

set_option autoImplicit false

namespace QuadBogolyubov

/-- A **quadratic variety of complexity `(d₁, d₂)`** in `𝔽₂ⁿ`, given by its representation:
linearly independent linear functions `ℓ₁, …, ℓ_{d₁}` with values `a₁, …, a_{d₁}` cutting out the
affine subspace `V = {x : ℓᵢ(x) = aᵢ ∀ i}` of codimension `d₁`, and quadratic polynomials
`q₁, …, q_{d₂}` with values `b₁, …, b_{d₂}` whose quadratic parts are linearly independent on `V`,
so that `W = {x ∈ V : qⱼ(x) = bⱼ ∀ j}`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §3, p.9:
"A quadratic variety W ⊆ F₂ⁿ of complexity (d1, d2) is a set of the form
W = {x ∈ V : qj(x) = bj for all j ∈ [d2]}, where V is an affine subspace of codimension d1,
bj ∈ F2 and the qj : V → F2 are quadratic functions whose "quadratic parts" are linearly
independent, that is, λ0 + λ1q1 + · · · + λd2qd2 is not a linear function for any
(λ0, λ1, . . . , λd2) ≠ 0."

**Formalization Note.** The printed independence condition cannot hold as written (take
`λ = (1, 0, …, 0)`: a constant is affine). It is encoded as the property the same sentence names:
for every `λ ∈ 𝔽₂^{d₂} \ {0}`, `∑ⱼ λⱼ qⱼ` does not agree on `V` with any polynomial of degree at
most one. The `qⱼ` are global quadratic polynomials, used only on `V`. Rank and complexity are
properties of this representation, not of the set; "codimension" in the paper means `(d₁, d₂)`. -/
structure QuadVariety (n : ℕ) where
  /-- number of linear equations (codimension of the ambient affine subspace) -/
  d1 : ℕ
  /-- number of quadratic equations -/
  d2 : ℕ
  /-- the linear functions `ℓᵢ` -/
  ℓ : Fin d1 → Module.Dual (ZMod 2) (Fin n → ZMod 2)
  /-- the values `aᵢ` -/
  a : Fin d1 → ZMod 2
  /-- the `ℓᵢ` are linearly independent -/
  ℓ_indep : LinearIndependent (ZMod 2) ℓ
  /-- the quadratic functions `qⱼ` -/
  q : Fin d2 → (Fin n → ZMod 2) → ZMod 2
  /-- each `qⱼ` is a quadratic polynomial -/
  q_quad : ∀ j, IsQuadraticPoly (q j)
  /-- the values `bⱼ` -/
  b : Fin d2 → ZMod 2
  /-- the quadratic parts of the `qⱼ` are linearly independent on `V` -/
  q_indep : ∀ lam : Fin d2 → ZMod 2, lam ≠ 0 →
    ¬ ∃ p : (Fin n → ZMod 2) → ZMod 2, IsAffinePoly p ∧
      ∀ x, (∀ i, ℓ i x = a i) → ∑ j, lam j * q j x = p x

namespace QuadVariety

variable {n : ℕ}

/-- The ambient affine subspace `V = {x : ℓᵢ(x) = aᵢ for all i ∈ [d₁]}`. -/
def affine (W : QuadVariety n) : Set (Fin n → ZMod 2) :=
  {x | ∀ i, W.ℓ i x = W.a i}

/-- The associated linear subspace `V₀ = V + V = ⋂ᵢ ker ℓᵢ` (the two agree because `V` is
non-empty, the `ℓᵢ` being linearly independent). -/
def dir (W : QuadVariety n) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  ⨅ i, LinearMap.ker (W.ℓ i)

open Classical in
/-- The point set `W = {x ∈ V : qⱼ(x) = bⱼ for all j ∈ [d₂]}` as a finite set. -/
noncomputable def carrier (W : QuadVariety n) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter (fun x => (∀ i, W.ℓ i x = W.a i) ∧ ∀ j, W.q j x = W.b j)

/-- The complexity `d₁ + d₂` (p.68: "of complexity at most ℓ+q, as in the statement of the main
theorem"). -/
def complexity (W : QuadVariety n) : ℕ := W.d1 + W.d2

end QuadVariety

end QuadBogolyubov


