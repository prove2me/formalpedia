-- Prove2me | Definitions.Def_NemirovskiProx_IsLipMonotoneOn
-- name    : NemirovskiProx_IsLipMonotoneOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:30.818615+00:00
-- url     : https://prove2.me/theorems/3739b607-dc66-4660-95ab-7e83845f3c93
-- title:
--   Lipschitz continuous monotone operator on $Z$, (2.1)
-- statement:
--   Let $Z\subset E$, let $\|\cdot\|$ be a norm on $E$ with dual norm $\|\cdot\|_*$, and let $L\in\mathbb R$. A mapping $F:Z\to E$ is **Lipschitz continuous with constant $L$ and monotone on $Z$** if
--
--   1. $\|F(z)-F(z')\|_*\le L\|z-z'\|$ for all $z,z'\in Z$ (2.1.a), and
--   2. $\langle F(z)-F(z'),\,z-z'\rangle\ge 0$ for all $z,z'\in Z$ (2.1.b).
--
--   These are the standing assumptions on the operator of the variational inequality throughout the paper.
--
--   **Formalization Note** $F$ is a function on all of $E$; only its values on $Z$ enter.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, §2.1, eq. (2.1), p. 232

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **Lipschitz continuous monotone mapping on `Z`, (2.1).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), §2.1, (2.1), p. 232: "let F : Z → E be a Lipschitz continuous monotone mapping,
(a) ∀(z, z′ ∈ Z) : ‖F(z) − F(z′)‖∗ ≤ L‖z − z′‖, (b) ∀(z, z′ ∈ Z) : ⟨F(z) − F(z′), z − z′⟩ ≥ 0".

`IsLipMonotoneOn Z N L F` is the conjunction of (2.1.a) and (2.1.b).

**Formalization Note.** `F` is a function on all of `E`; only its values on `Z` enter. The
paper's ‖·‖ is the seminorm `N` and ‖·‖∗ is `dualNorm N`. -/
def IsLipMonotoneOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (N : Seminorm ℝ E) (L : ℝ) (F : E → E) : Prop :=
  (∀ z ∈ Z, ∀ z' ∈ Z, dualNorm N (F z - F z') ≤ L * N (z - z')) ∧
    (∀ z ∈ Z, ∀ z' ∈ Z, 0 ≤ ⟪F z - F z', z - z'⟫_ℝ)

end NemirovskiProx


