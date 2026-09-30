-- Prove2me | Definitions.Def_AccelPPM_FPR_IsMaximalMonotone
-- name    : AccelPPM_FPR_IsMaximalMonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:26:14.267863+00:00
-- url     : https://prove2.me/theorems/520de042-a37d-4461-97bd-779465be1564
-- title:
--   Monotone and maximally monotone set-valued operators $M:\mathcal H\to 2^{\mathcal H}$, and the zero set $X_*(M)$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$. A set-valued operator $M:\mathcal H\to 2^{\mathcal H}$ assigns to every point $x$ a (possibly empty) set $Mx\subseteq\mathcal H$; its graph is $\operatorname{gra}M=\{(x,u)\in\mathcal H\times\mathcal H : u\in Mx\}$.
--
--   1. $M$ is **monotone** if
--   $$
--   \langle x-y,\ u-v\rangle\ \ge\ 0\qquad\text{for all }(x,u),(y,v)\in\operatorname{gra}M .
--   $$
--   2. $M$ is **maximally monotone** if it is monotone and no monotone operator $A:\mathcal H\to 2^{\mathcal H}$ has a graph that properly contains $\operatorname{gra}M$; equivalently, every monotone $A$ with $\operatorname{gra}M\subseteq\operatorname{gra}A$ equals $M$. The class of maximally monotone operators on $\mathcal H$ is denoted $\mathcal M(\mathcal H)$.
--   3. The **zero set** (optimal set of the monotone inclusion problem $0\in Mx$) is
--   $$
--   X_*(M)=\{x\in\mathcal H : 0\in Mx\}.
--   $$
--
--   These are the standing objects of the mission: every method is run on an operator in $\mathcal M(\mathcal H)$, and the reference point $x_*$ of every rate is an element of $X_*(M)$.
--
--   **Formalization Note** The operator is a function `M : H → Set H`; `u ∈ M x` is $(x,u)\in\operatorname{gra}M$, and graph inclusion $\operatorname{gra}M\subseteq\operatorname{gra}A$ is `∀ x, M x ⊆ A x`. The module declares `IsMonotoneOp`, `IsMaximalMonotone` and `zeroSet`. The inner product is Mathlib's `inner ℝ`.
-- source:
--   Kim, Accelerated proximal point method for maximally monotone operators, arXiv:1905.05149v4, p. 2, Section 2.1, Eq. (1) and the definitions of $\mathcal M(\mathcal H)$ and $X_*(M)$ (Eq. (3))

import Mathlib

namespace AccelPPM.FPR

/-- A set-valued operator `M : H → 2^H` (encoded as `M : H → Set H`) is **monotone** if
`⟪x - y, u - v⟫ ≥ 0` for all `(x, u), (y, v) ∈ gra M`, i.e. whenever `u ∈ M x` and `v ∈ M y`
(Kim, arXiv:1905.05149v4, p. 2, Eq. (1)). -/
def IsMonotoneOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) : Prop :=
  ∀ x y u v : H, u ∈ M x → v ∈ M y → 0 ≤ inner ℝ (x - y) (u - v)

/-- A monotone operator `M` is **maximally monotone** if no monotone operator `A : H → 2^H`
has a graph that properly contains `gra M`: every monotone `A` with `M x ⊆ A x` for all `x`
(i.e. `gra M ⊆ gra A`) coincides with `M` (p. 2). `IsMaximalMonotone M` is membership of `M` in
the class `𝓜(H)`. -/
def IsMaximalMonotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) : Prop :=
  IsMonotoneOp M ∧
    ∀ A : H → Set H, IsMonotoneOp A → (∀ x, M x ⊆ A x) → ∀ x, A x = M x

/-- The optimal (zero) set `X_*(M) := {x ∈ H : 0 ∈ M x}` of the monotone inclusion
problem `0 ∈ M x` (p. 2, Eq. (3)). -/
def zeroSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) : Set H :=
  {x | (0 : H) ∈ M x}

end AccelPPM.FPR


