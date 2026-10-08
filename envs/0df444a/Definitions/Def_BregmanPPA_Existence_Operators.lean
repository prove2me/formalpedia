-- Prove2me | Definitions.Def_BregmanPPA_Existence_Operators
-- name    : BregmanPPA_Existence_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:51.473901+00:00
-- url     : https://prove2.me/theorems/b7731a48-b3f1-43a7-9f35-7a7df3885d71
-- title:
--   ∂f, the extension ĥ of h by +∞, the operator ∇h with domain S, and runs of recursion (3)
-- statement:
--   Operators on $H$ are set-valued maps $A:H\to 2^H$; $\operatorname{dom}A=\{x: A x\ne\emptyset\}$ and $\operatorname{im}A=\{y:\exists x,\ y\in Ax\}$ (p. 206). This file introduces four objects built on a Bregman function $h$ with zone $S$.
--
--   1. For $f:H\to(-\infty,+\infty]$, the **subdifferential map** $\partial f(x)=\{g : f(x)<+\infty,\ f(v)\ge f(x)+\langle g,v-x\rangle\ \forall v\}$.
--   2. The **extension** $\hat h$ of $h$ by $+\infty$: $\hat h(x)=h(x)$ for $x\in\bar S$ and $\hat h(x)=+\infty$ otherwise. By the closing note of Definition 1 (p. 205), $\hat h$ is a closed proper convex function on $\mathbb R^n$; its subdifferential is the operator the paper writes $\partial h$.
--   3. The operator **$\nabla h$** with $\operatorname{dom}\nabla h=S$: $x\mapsto\{\nabla h(x)\}$ for $x\in S$ and $x\mapsto\emptyset$ for $x\notin S$. Its image is $\operatorname{im}\nabla h=\nabla h(S)$.
--   4. A **run of recursion (3)**, $x^{k+1}=(\nabla h+c_kT)^{-1}(\nabla h(x^k))$, for an operator $T$ and scalars $c_k$: a sequence $\{x^k\}$ with $x^k\in S$ for every $k$ and, in the equivalent form (4),
--   $$
--   \frac1{c_k}\bigl(\nabla h(x^k)-\nabla h(x^{k+1})\bigr)\in T(x^{k+1})\qquad\text{for all }k\ge0 .
--   $$
--
--   These are the objects in which the existence question of Theorem 4 is posed.
--
--   **Formalization Note** Functions with values in $(-\infty,+\infty]$ are `EReal`-valued and use the published `IsSubgradient` of `InertialFB.IFB.ConvexAnalysis`. Recursion (3) is encoded through (4), which the paper states is equivalent (p. 207), together with $x^k\in S$: the point $\nabla h(x^k)$ must be defined, and $(\nabla h+c_kT)^{-1}$ is the graph inverse, so $x^{k+1}\in\operatorname{dom}(\nabla h + c_kT)\subseteq S$. The operator $\nabla h$ is empty off $S$; using Mathlib's `gradient h` everywhere instead would add junk values (zero) outside the zone.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 205 (note after Definition 1), p. 206 (dom and im; recursion (3)), p. 207 (form (4))

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_BregmanPPA_Convergence_Model

open InertialFB.IFB

namespace BregmanPPA.Existence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The extended function `ĥ` of the closing note of Definition 1 (p. 205): `ĥ = h` on `S̄` and
`ĥ = +∞` off `S̄`. Its subdifferential `subdiffOp (extendedFn S h)` is the paper's `∂h`. -/
noncomputable def extendedFn (S : Set H) (h : H → ℝ) : H → EReal := by
  classical
  exact fun x => if x ∈ closure S then ((h x : ℝ) : EReal) else ⊤

/-- The gradient `∇h` as an operator with domain `dom ∇h = S`: `x ↦ {∇h(x)}` for `x ∈ S` and
`x ↦ ∅` off `S`. Its image `imOp (gradOp S h)` is `im ∇h = ∇h(S)`. -/
noncomputable def gradOp (S : Set H) (h : H → ℝ) : H → Set H :=
  fun x => {g | x ∈ S ∧ g = gradient h x}

/-- A run of recursion (3), `x^{k+1} = (∇h + c_k T)⁻¹(∇h(x^k))`, in its equivalent form (4)
(p. 207): every iterate lies in `S = dom ∇h`, and
`(1/c_k)(∇h(x^k) − ∇h(x^{k+1})) ∈ T(x^{k+1})` for every `k`. -/
def IsBregmanPPARun (S : Set H) (h : H → ℝ) (T : H → Set H) (c : ℕ → ℝ) (x : ℕ → H) : Prop :=
  ∀ k, x k ∈ S ∧ (c k)⁻¹ • (gradient h (x k) - gradient h (x (k + 1))) ∈ T (x (k + 1))

end BregmanPPA.Existence


