-- Prove2me | Definitions.Def_Hatcher_ComplexProjectiveSpace
-- name    : Hatcher_ComplexProjectiveSpace
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-21T08:25:53.626239+00:00
-- url     : https://prove2.me/theorems/c84243ca-5749-437c-a540-92f07e83de08
-- title:
--   Complex projective space $\mathbb CP^n$ with the quotient topology
-- statement:
--   Let $n\ge 0$. Complex projective $n$-space is the space of complex lines through the origin in $\mathbb C^{n+1}$:
--   $$\mathbb CP^n=\bigl(\mathbb C^{n+1}\setminus\{0\}\bigr)\big/\sim,\qquad v\sim\lambda v\quad(\lambda\in\mathbb C^\times),$$
--   with the quotient topology induced by the projection $\mathbb C^{n+1}\setminus\{0\}\to\mathbb CP^n$, where $\mathbb C^{n+1}\setminus\{0\}$ carries the subspace topology of $\mathbb C^{n+1}$.
--
--   This is the space whose homology is computed in Hatcher's §2.2 by cellular homology (p. 140); it is also the space of complex points of the algebraic projective space $\mathbb P^n$.
--
--   **Formalization Note** The underlying set is Mathlib's projectivization `ℙ ℂ (Fin (n + 1) → ℂ)`, so that the same type also describes the complex points of $\mathbb P^n$ in algebraic geometry; the topology is that of the quotient of `{v : Fin (n + 1) → ℂ // v ≠ 0}` by `projectivizationSetoid`.
-- source:
--   A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (online edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0, Example 0.6 (p. 6). Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Definitions/Def_Hatcher_ComplexProjectiveSpace.lean`.

import Mathlib

/-!
Hatcher, *Algebraic Topology*, Chapter 0, Example 0.6: complex projective space `ℂPⁿ`, in the
book-wide namespace `Hatcher`.

`ℂPⁿ` is the space of complex lines through the origin in `ℂⁿ⁺¹`, that is, the quotient of
`ℂⁿ⁺¹ ∖ {0}` by the equivalence relation `v ∼ λv`, `λ ∈ ℂ ∖ {0}`, with the quotient topology.

The underlying set is Mathlib's projectivization `ℙ ℂ (Fin (n + 1) → ℂ)` (the same type as the
complex points of the algebraic projective space); it is given here the quotient topology of the
subspace `{v : Fin (n + 1) → ℂ // v ≠ 0}` of `ℂⁿ⁺¹` (product topology).
-/

open scoped LinearAlgebra.Projectivization

namespace Hatcher

/-- Complex projective space `ℂPⁿ = (ℂⁿ⁺¹ ∖ {0}) / ℂ^×` (Hatcher, Example 0.6). -/
abbrev CP (n : ℕ) : Type := ℙ ℂ (Fin (n + 1) → ℂ)

/-- The quotient topology on `ℂPⁿ`, induced by `ℂⁿ⁺¹ ∖ {0} → ℂPⁿ`. -/
instance (n : ℕ) : TopologicalSpace (CP n) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (Fin (n + 1) → ℂ))))

end Hatcher


