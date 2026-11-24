-- Prove2me | Definitions.Def_VpVnp_Polynomials
-- name    : VpVnp_Polynomials
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T23:35:52.018365+00:00
-- url     : https://prove2.me/theorems/ec939102-ee96-4a44-8f70-544f356106a9
-- title:
--   The permanent and the Hamiltonian cycle polynomial of a generic $m \times m$ matrix
-- statement:
--   The two canonical VNP-complete families, as polynomials in the $m^2$ independent variables $x_{i,j}$ with $i,j \in \{0,\dots,m-1\}$ and coefficients in a commutative semiring $F$:
--
--   $$\mathrm{PERM}_m = \sum_{\sigma \in S_m} \prod_{i} x_{\sigma(i),\,i}, \qquad \mathrm{HC}_m = \sum_{\substack{\sigma \in S_m \\ \sigma \text{ cyclic}}} \prod_{i} x_{i,\,\sigma(i)} .$$
--
--   The first sum runs over all $m!$ permutations of $\{0,\dots,m-1\}$; the second only over the permutations that consist of a single cycle through all $m$ points, of which there are $(m-1)!$ for $m \geq 1$. Both polynomials are multilinear of degree $m$. The permanent is VNP-complete over every field in which $2 \neq 0$, and the Hamiltonian cycle polynomial over every field; they are the targets of the mission's lower bounds.
--
--   **Formalization Note.** The permanent is written with the index order $x_{\sigma(i),i}$, the transpose of the source's Section 1 display $x_{i,\sigma(i)}$; the two sums agree by replacing $\sigma$ with its inverse, as the source's Appendix Q records. The cycle condition is Mathlib's `Equiv.Perm.IsCycleOn` on the whole index set, and the filtered sum is classical. At $m = 0$ the Hamiltonian cycle polynomial is $1$; the theorems only use $m \geq m_0$.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf §1, p. 1 (displays of PERM_m and HC_m); Appendix Q.3, p. 68 (index order); Lean vp-vnp/Statement.lean, defs Statement.perm and Statement.hc

import Mathlib

open MvPolynomial

universe u

namespace VpVnp

/-- The permanent of the generic `m × m` matrix. -/
noncomputable def perm (F : Type u) [CommSemiring F] (m : ℕ) : MvPolynomial (Fin m × Fin m) F :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i, X (σ i, i)

open Classical in
/-- The Hamiltonian cycle polynomial: the sum over the permutations with a single cycle through all points. -/
noncomputable def hc (F : Type u) [CommSemiring F] (m : ℕ) : MvPolynomial (Fin m × Fin m) F :=
  ∑ σ : Equiv.Perm (Fin m) with σ.IsCycleOn Set.univ, ∏ i, X (i, σ i)

end VpVnp


