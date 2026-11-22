-- Prove2me | Definitions.Def_VectorValuedHolomorphy_Order
-- name    : VectorValuedHolomorphy_Order
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:22:16.30781+00:00
-- url     : https://prove2.me/theorems/93e287e7-2847-489b-96db-7ecb06ba475f
-- title:
--   Order of a vector-valued meromorphic function at a point; poles and their orders ($\operatorname{ord}_{z_0}(f)$)
-- statement:
--   This file defines the **order at a point** of a function with values in a topological vector space, and **poles** and their orders.
--
--   Let $E$ be a topological vector space over $\mathbb C$ (in the source: a quasi-complete Hausdorff locally convex space), let $z_0\in\mathbb C$ and let $f$ be an $E$-valued function defined near $z_0$, except possibly at $z_0$.
--
--   1. **Order.** $f$ *has order $n\in\mathbb Z$ at $z_0$*, written $\operatorname{ord}_{z_0}(f)=n$, if there is a function $g$, holomorphic on a neighbourhood of $z_0$, with
--   $$f(z)=(z-z_0)^{n}\,g(z)\quad\text{for all }z\neq z_0\text{ close to }z_0,\qquad g(z_0)\neq 0 .$$
--   Equivalently (for $E$ quasi-complete Hausdorff locally convex), the Laurent expansion $f(z)=\sum_{k\ge n}a_k(z-z_0)^k$ of $f$ at $z_0$ starts at the exponent $n$ with $a_n\neq 0$.
--   2. **Pole of order $m$.** $f$ *has a pole of order $m$ at $z_0$* if $m\ge 1$ and $\operatorname{ord}_{z_0}(f)=-m$.
--   3. **Pole.** $f$ *has a pole at $z_0$* if it has a pole of some order $m\ge 1$ there, i.e. $\operatorname{ord}_{z_0}(f)\le -1$.
--
--   These are the vector-valued versions of the classical notions (Definition C.5.3.1(1)-(2) of the paper), used there for zeta integrals with values in spaces of distributions: the order of a pole enters the residue formula (C.5.3.8).
--
--   **Formalization Note.** The file defines `VectorValuedHolomorphy.HasOrderAt f z₀ n`, `VectorValuedHolomorphy.HasPoleOfOrderAt f z₀ m` and `VectorValuedHolomorphy.HasPoleAt f z₀` for total functions `f : ℂ → E` with `[AddCommGroup E] [Module ℂ E] [TopologicalSpace E]` (no compatibility between the topology and the linear structure is needed to state them). Mathlib's `meromorphicOrderAt` requires a normed target; for $E=\mathbb C$ and $f$ meromorphic at $z_0$, `HasOrderAt f z₀ n` is equivalent to `meromorphicOrderAt f z₀ = n` (checked). "Holomorphic on a neighbourhood of $z_0$" is `∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z`, "for $z\ne z_0$ close to $z_0$" is `∀ᶠ z in 𝓝[≠] z₀`, and $(z-z_0)^n$ is an integer power; the value $f(z_0)$ is irrelevant. The order is a relation, not a function: a function vanishing identically near $z_0$ has no order in this sense (its order is $+\infty$ in the usual convention). **Deviation from the source.** Definition C.5.3.1(1) defines $\operatorname{ord}_{\xi_0}(f)$ as "the minimal integer $N$ such that" a Laurent expansion $\sum_{k'\ge N}$ exists; as printed this has no meaning (if an expansion starts at $N$ it also starts at every smaller index, with zero coefficients). The classical notion, the exponent of the first non-zero Laurent coefficient, is formalized, in the factorized form used by Mathlib's characterization of `meromorphicOrderAt`; the equivalence with the Laurent form is a separate theorem.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 739, Definition C.5.3.1(1)-(2)

import Mathlib

/-!
# Order of a vector-valued meromorphic function at a point; poles and their orders

Mathlib's `meromorphicOrderAt` requires a normed target space. Here the target `E` is an arbitrary
topological vector space over `ℂ` (in the applications: a quasi-complete Hausdorff locally convex
space), and holomorphy is Mathlib's complex differentiability `DifferentiableAt ℂ`.

Source: A. M. Masullo, *The Music of the Primes*, draft of 20 November 2026,
Definition C.5.3.1(1)-(2) (p. 739).
-/

open Filter Topology

namespace VectorValuedHolomorphy

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- `f : ℂ → E` **has order `n : ℤ` at `z₀`** if, on a punctured neighbourhood of `z₀`,
`f z = (z - z₀) ^ n • g z` for a function `g` that is complex differentiable at every point of a
neighbourhood of `z₀` and satisfies `g z₀ ≠ 0`. Equivalently (for `E` quasi-complete Hausdorff
locally convex), `n` is the index of the first non-zero coefficient of the Laurent expansion of
`f` at `z₀`. The value `f z₀` is irrelevant. A function vanishing identically near `z₀` has no
order in this sense. -/
def HasOrderAt (f : ℂ → E) (z₀ : ℂ) (n : ℤ) : Prop :=
  ∃ g : ℂ → E, (∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z) ∧ g z₀ ≠ 0 ∧
    ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ n • g z

/-- `f : ℂ → E` **has a pole of order `m` at `z₀`**: `m ≥ 1` and `f` has order `-m` at `z₀`. -/
def HasPoleOfOrderAt (f : ℂ → E) (z₀ : ℂ) (m : ℕ) : Prop :=
  0 < m ∧ HasOrderAt f z₀ (-(m : ℤ))

/-- `f : ℂ → E` **has a pole at `z₀`**: its order at `z₀` is at most `-1`. -/
def HasPoleAt (f : ℂ → E) (z₀ : ℂ) : Prop :=
  ∃ m : ℕ, HasPoleOfOrderAt f z₀ m

end VectorValuedHolomorphy


