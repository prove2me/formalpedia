-- Prove2me | Definitions.Def_WildeQIT_QMemory_incompatibility
-- name    : WildeQIT_QMemory_incompatibility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:30.536769+00:00
-- url     : https://prove2.me/theorems/506c66cf-ca40-44a1-a399-3f09b3fab5cc
-- title:
--   Measurement incompatibility $c=\max_{x,z}\|\sqrt{\Lambda^x}\sqrt{\Gamma^z}\|_\infty^2$
-- statement:
--   For two POVMs $\{\Lambda^x_A\}$ and $\{\Gamma^z_A\}$ on $\mathcal H_A$, the **measurement incompatibility** is
--
--   $$
--   c\equiv\max_{x,z}\big\|\sqrt{\Lambda^x_A}\sqrt{\Gamma^z_A}\big\|_\infty^2 ,
--   $$
--
--   where $\|M\|_\infty$ is the operator norm, the largest eigenvalue of $|M|$. Two complete projective measurements with a common element have $c=1$; the Pauli $X$ and $Z$ measurements on a qubit have $c=1/2$.
--
--   **Formalization Note** $\sqrt{\Lambda}$ is `CFC.sqrt`, the positive square root. $\|M\|_\infty$ is the operator norm of $M$ on the Euclidean space $\ell^2(a)$ (`Matrix.toEuclideanCLM`), equal to the largest singular value. The maximum over the finite outcome sets is a real supremum, attained since the sets are finite; its value on an empty outcome set is $0$, which does not occur for POVMs on a nonempty system. For two POVMs $c>0$, because $\sum_{x,z}\sqrt{\Gamma^z}\Lambda^x\sqrt{\Gamma^z}=I$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eq. (11.210), p. 354

import Mathlib

open scoped MatrixOrder

namespace WildeQIT.QMemory

/-- **Measurement incompatibility** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, eq. (11.210), p. 354): for POVMs `{Λ^x_A}` and `{Γ^z_A}`,
`c ≡ max_{x,z} ‖√Λ^x_A √Γ^z_A‖²_∞`, where `‖·‖_∞` is the operator (infinity) norm, the largest
eigenvalue of `|A|`.

**Formalization Note** `√Λ` is `CFC.sqrt`, the positive square root of a positive semi-definite
matrix. `‖M‖_∞` is the operator norm of `M` acting on the Euclidean space `ℓ²(a)`
(`Matrix.toEuclideanCLM`), which equals the largest singular value of `M`. The maximum over the
finite outcome sets is a real `⨆`; it is attained because the sets are finite. When an outcome
set is empty the value is `0`, but a POVM on a nonempty `a` has a nonempty outcome set, and for
two POVMs `c > 0` (since `∑_{x,z} √Γ^z Λ^x √Γ^z = I`). -/
noncomputable def incompatibility {a x z : Type} [Fintype a] [DecidableEq a]
    (Λ : x → Matrix a a ℂ) (Γ : z → Matrix a a ℂ) : ℝ :=
  ⨆ i, ⨆ j, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (CFC.sqrt (Λ i) * CFC.sqrt (Γ j))‖ ^ 2

end WildeQIT.QMemory


