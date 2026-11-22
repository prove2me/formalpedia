-- Prove2me | Definitions.Def_VectorValuedHolomorphy_Meromorphic
-- name    : VectorValuedHolomorphy_Meromorphic
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T10:48:47.288458+00:00
-- url     : https://prove2.me/theorems/e549a199-6e1d-4096-8596-ace0388b3936
-- title:
--   Meromorphic functions and residues with values in a topological vector space (vector-valued $\mathscr M(\Omega,E)$, $\operatorname{Res}_{z_0}$)
-- statement:
--   **Meromorphic functions with values in a topological vector space, and their residues.**
--
--   Let $E$ be a topological vector space over $\mathbb C$ (in the source: a quasi-complete Hausdorff locally convex space), let $z_0\in\mathbb C$ and let $f$ be an $E$-valued function defined near $z_0$, except possibly at $z_0$. An $E$-valued function $g$ is *holomorphic* near a point if it is complex differentiable there: the difference quotients $(z-w)^{-1}(g(z)-g(w))$ converge in $E$ as $z\to w$.
--
--   1. **Meromorphic at a point.** $f$ is *meromorphic at $z_0$* if there are an integer $n\ge 0$ and a function $g$, holomorphic on a neighbourhood of $z_0$, such that
--   $$g(z)=(z-z_0)^{n}\,f(z)\qquad\text{for all }z\ne z_0\text{ close to }z_0 ,$$
--   that is, $(z-z_0)^n f(z)$ extends holomorphically across $z_0$.
--
--   2. **Meromorphic on a set.** $f$ is *meromorphic on $U\subset\mathbb C$* if it is meromorphic at every point of $U$. For open $U$ this is the space $\mathscr M(U,E)$ of the source: $f$ is holomorphic off a subset $D\subset U$ without accumulation point in $U$, and has a pole (or a removable singularity) at each point of $D$.
--
--   3. **Residue.** A vector $r\in E$ is *the residue of $f$ at $z_0$*, written $\operatorname{Res}_{z_0}(f)=r$, if there are an integer $n\ge 0$, vectors $a_0,\dots,a_n\in E$ with $a_0=r$, and a function $h$ holomorphic on a neighbourhood of $z_0$ such that
--   $$f(z)=\sum_{j=0}^{n}\frac{a_j}{(z-z_0)^{j+1}}+h(z)\qquad\text{for all }z\ne z_0\text{ close to }z_0 .$$
--   So $r$ is the coefficient $a_{-1}(z_0,f)$ of $(z-z_0)^{-1}$ in the Laurent expansion of $f$ at $z_0$, and $\sum_j a_j (z-z_0)^{-(j+1)}$ is the principal part.
--
--   These are the vector-valued versions of the classical notions; the paper introduces them (Definition C.5.3.1 and formula (C.5.3.5)) for the meromorphic continuation of zeta integrals with values in spaces of distributions, and states for them the Laurent coefficient formula, the residue formula and the Residue Theorem.
--
--   **Formalization Note.** The file defines `VectorValuedHolomorphy.MeromorphicAt f z₀`, `VectorValuedHolomorphy.MeromorphicOn f U` and `VectorValuedHolomorphy.HasResidueAt f z₀ r` for total functions `f : ℂ → E`, with `[AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [ContinuousSMul ℂ E]`. Mathlib's own `MeromorphicAt` requires a normed target, which excludes the spaces of the paper; for $E=\mathbb C$ the new predicate is equivalent to Mathlib's (checked). "Holomorphic on a neighbourhood of $z_0$" is `∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z`, "for $z\ne z_0$ close to $z_0$" is `∀ᶠ z in 𝓝[≠] z₀`; the value $f(z_0)$ is irrelevant, as for Mathlib's `MeromorphicAt`. The pair $(f,D)$ of the paper is encoded by the total function $f$ alone. The residue is a relation, not a function: existence and uniqueness of $r$ (for $E$ quasi-complete Hausdorff locally convex) is a theorem. **Deviation from the source.** Definition C.5.3.1 defines meromorphy by a Laurent series whose lowest index is printed as "$k\ge 0$" (which would exclude poles) and adds "equivalently, some $(\xi-\xi_0)^{N}f(\xi)$ extends holomorphically across $\xi_0$"; the pole-clearing form, which is the one consistent with (C.5.3.4), is taken as the definition, and the equivalence with Laurent expansions is a separate theorem. The order of a pole (Definition C.5.3.1(1)-(2)) is not formalized.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 739-740, Definition C.5.3.1 and formula (C.5.3.5)

import Mathlib

/-!
# Meromorphic functions and residues with values in a topological vector space

Mathlib's `MeromorphicAt` requires a normed target space. Here the target `E` is an arbitrary
topological vector space over `ℂ` (in the applications: a quasi-complete Hausdorff locally convex
space), and holomorphy is Mathlib's complex differentiability `DifferentiableAt ℂ`, which for a
topological vector space target means that the difference quotients converge in `E`.

Source: A. M. Masullo, *The Music of the Primes*, draft of 20 November 2026, Definition C.5.3.1
(p. 739) and (C.5.3.5) (p. 740).
-/

open Filter Topology

namespace VectorValuedHolomorphy

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [ContinuousSMul ℂ E]

/-- `f : ℂ → E` is **meromorphic at `z₀`** if for some `n : ℕ` the function
`z ↦ (z - z₀) ^ n • f z` agrees, on a punctured neighbourhood of `z₀`, with a function `g` that is
complex differentiable at every point of a neighbourhood of `z₀` ("`(z - z₀) ^ n f(z)` extends
holomorphically across `z₀`"). The value `f z₀` is irrelevant. -/
def MeromorphicAt (f : ℂ → E) (z₀ : ℂ) : Prop :=
  ∃ (n : ℕ) (g : ℂ → E), (∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z) ∧
    ∀ᶠ z in 𝓝[≠] z₀, g z = (z - z₀) ^ n • f z

/-- `f : ℂ → E` is **meromorphic on `U`** if it is meromorphic at every point of `U`. -/
def MeromorphicOn (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, MeromorphicAt f z

/-- `r : E` is **the residue of `f` at `z₀`**: on a punctured neighbourhood of `z₀`,
`f z = ∑_{j = 0}^{n} (z - z₀) ^ (-(j + 1)) • a j + h z` with `h` complex differentiable at every
point of a neighbourhood of `z₀`, and `r = a 0` is the coefficient of `(z - z₀)⁻¹`. -/
def HasResidueAt (f : ℂ → E) (z₀ : ℂ) (r : E) : Prop :=
  ∃ (n : ℕ) (a : ℕ → E) (h : ℂ → E), a 0 = r ∧ (∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ h z) ∧
    ∀ᶠ z in 𝓝[≠] z₀,
      f z = (∑ j ∈ Finset.range (n + 1), ((z - z₀) ^ (j + 1))⁻¹ • a j) + h z

end VectorValuedHolomorphy


