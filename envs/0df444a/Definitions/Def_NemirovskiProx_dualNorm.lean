-- Prove2me | Definitions.Def_NemirovskiProx_dualNorm
-- name    : NemirovskiProx_dualNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:00.777548+00:00
-- url     : https://prove2.me/theorems/a03851ea-1502-4423-b127-597ffea35786
-- title:
--   Dual norm $\|\xi\|_*$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with inner product $\langle\cdot,\cdot\rangle$, and let $\|\cdot\|$ be a norm on $E$, not necessarily the one induced by the inner product. The **conjugate (dual) norm** is
--   $$\|\xi\|_*=\max_{z:\ \|z\|\le 1}\langle \xi, z\rangle,\qquad \xi\in E.$$
--
--   It is the norm in which the Lipschitz condition (2.1) on the operator $F$ and the Lipschitz bound (2.4) of the prox-mapping are measured.
--
--   **Formalization Note** The norm $\|\cdot\|$ is a seminorm $N$ on $E$; definiteness ($N(x)=0\Rightarrow x=0$) is a hypothesis of every theorem that uses it, because Lean's own $\|\cdot\|$ on $E$ is the inner-product norm. The maximum is a supremum; the set is nonempty (it contains $0$), and under definiteness the unit ball is compact, so the supremum is attained.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, §2.1, p. 232 (definition of ‖·‖∗ after (2.1))

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The norm conjugate to `N`.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), §2.1, p. 232: "where ‖·‖∗ is the norm conjugate to ‖·‖: ‖ξ‖∗ = max_{z:‖z‖≤1} ⟨ξ, z⟩."

`dualNorm N ξ = sup {⟨ξ, z⟩ : N z ≤ 1}`.

**Formalization Note.** The paper's norm ‖·‖ on `E` is the seminorm `N` (definiteness is a
separate hypothesis `∀ x, N x = 0 → x = 0` wherever it is needed); Lean's `‖·‖` on `E` is the
inner-product norm and is never the paper's ‖·‖. The paper's `max` is `sSup`: the set is
nonempty (it contains `⟨ξ, 0⟩ = 0`), and when `N` is a norm on the finite-dimensional `E` its
unit ball is compact, so the supremum is attained and equals the max. The junk value of `sSup`
(an unbounded set, possible only when `N` vanishes on a nonzero vector) cannot occur under
definiteness. -/
noncomputable def dualNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Seminorm ℝ E) (ξ : E) : ℝ :=
  sSup ((fun z => ⟪ξ, z⟫_ℝ) '' {z | N z ≤ 1})

end NemirovskiProx


