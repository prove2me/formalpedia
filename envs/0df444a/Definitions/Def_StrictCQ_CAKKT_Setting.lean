-- Prove2me | Definitions.Def_StrictCQ_CAKKT_Setting
-- name    : StrictCQ_CAKKT_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:31:29.903662+00:00
-- url     : https://prove2.me/theorems/24c2014b-4aca-4a96-b6a0-290c54c609bc
-- title:
--   (1.1), (1.6), (3.3)–(3.5), (3.7), p. 1–5 — constraints, KKT, polar, outer limit, tangent / regular normal / limiting normal cones, linearized cone, Abadie's CQ
-- statement:
--   This file fixes the objects shared by every statement of the mission. Throughout, $\mathbb R^n$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$.
--
--   1. **Constraint system (1.1).** Functions $h_1,\dots,h_m$ and $g_1,\dots,g_p$ from $\mathbb R^n$ to $\mathbb R$ define the feasible set
--   $$\Omega=\{x\in\mathbb R^n:\ h_i(x)=0\ (i=1,\dots,m),\ g_j(x)\le 0\ (j=1,\dots,p)\}.$$
--   The standing hypothesis is that every $h_i$ and $g_j$ is continuously differentiable. The active set at a feasible $x^*$ is $J(x^*)=\{j: g_j(x^*)=0\}$.
--   2. **KKT.** For an objective $f$, the KKT condition holds at $x^*$ if there are $\lambda\in\mathbb R^m$ and $\mu\in\mathbb R^p_+$ with $\mu_j=0$ for $j\notin J(x^*)$ and $\nabla f(x^*)+\sum_i\lambda_i\nabla h_i(x^*)+\sum_j\mu_j\nabla g_j(x^*)=0$.
--   3. **Polar cone** of $\mathcal K\subseteq\mathbb R^n$: $\mathcal K^\circ=\{v:\ \langle v,k\rangle\le 0\ \text{for all } k\in\mathcal K\}$.
--   4. **Outer limit (1.6)** of a set-valued map $F$ at $z^*$ relative to a domain $D$: the set of all limits $w=\lim v^k$ with $v^k\in F(z^k)$, $z^k\in D$, $z^k\to z^*$.
--   5. **Tangent cone (3.3)** of $S$ at $z^*\in S$: $T_S(z^*)=\{d:\ \exists\, t_k\downarrow 0,\ d^k\to d,\ z^*+t_kd^k\in S\}$.
--   6. **Regular normal cone (3.4):** $\widehat N_S(z^*)=\{w:\ \langle w,z-z^*\rangle\le o(\|z-z^*\|)\ \text{for } z\in S\}$, i.e. for every $\varepsilon>0$, $\langle w,z-z^*\rangle\le\varepsilon\|z-z^*\|$ for all $z\in S$ near $z^*$.
--   7. **Limiting normal cone (3.5):** $N_S(z^*)=\limsup_{z\to_S z^*}\widehat N_S(z)$, the outer limit of $\widehat N_S$ along points of $S$.
--   8. **Linearized cone (3.7):** $L_\Omega(x^*)=\{d:\ \langle\nabla h_i(x^*),d\rangle=0\ \forall i,\ \langle\nabla g_j(x^*),d\rangle\le 0\ \forall j\in J(x^*)\}$.
--   9. **Abadie's constraint qualification** (p. 5) holds at $x^*$ if $L_\Omega(x^*)=T_\Omega(x^*)$.
--
--   These are the classical objects of variational analysis (Rockafellar–Wets) in the paper's notation; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and indices are `Fin m`, `Fin p` (0-based). Gradients are Mathlib's `gradient`; the C¹ hypothesis is carried by `IsC1` in each theorem. "$t_k\downarrow 0$" is encoded as $t_k>0$, $t_k\to 0$ (equivalent after passing to a monotone subsequence); Mathlib's `tangentConeAt` is not used because it allows negative scalars. The regular normal cone carries the clause $z^*\in S$, so it is empty off $S$. The outer limit is the sequential Painlevé–Kuratowski outer limit. The sum over $J(x^*)$ in KKT is written over all $j$ with $\mu_j=0$ off $J(x^*)$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 1–5, (1.1), (1.6), (3.3), (3.4), (3.5), (3.7), Abadie's CQ (p. 5)

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

variable {n : ℕ}

/-- (Bouligand–Severi) tangent cone (3.3): `d ∈ T_S(z)` iff there are `t k > 0`, `t k → 0`,
`dk k → d` with `z + t k • dk k ∈ S`. -/
def tangentCone (S : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ∃ t : ℕ → ℝ, ∃ dk : ℕ → EuclideanSpace ℝ (Fin n), (∀ k, 0 < t k) ∧
    Tendsto t atTop (𝓝 0) ∧ Tendsto dk atTop (𝓝 d) ∧ ∀ k, z + t k • dk k ∈ S}

/-- (Fréchet) regular normal cone (3.4): `w ∈ N̂_S(z)` iff `z ∈ S` and
`⟨w, y - z⟩ ≤ o(‖y - z‖)` for `y ∈ S`, i.e. for every `ε > 0`, `⟨w, y - z⟩ ≤ ε ‖y - z‖`
for all `y ∈ S` near `z`. Empty when `z ∉ S`. -/
def regNormal (S : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {w | z ∈ S ∧ ∀ ε > (0 : ℝ), ∀ᶠ y in 𝓝[S] z, ⟪w, y - z⟫_ℝ ≤ ε * ‖y - z‖}

/-- (Mordukhovich) limiting normal cone (3.5): the outer limit of `N̂_S(z)` as `z → z*` within `S`. -/
def limNormal (S : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  StrictCQ.AGP.outerLimitWithin (regNormal S) S z

/-- The constraint data `h : ℝⁿ → ℝᵐ`, `g : ℝⁿ → ℝᵖ` of problem (1.1), as index families. -/
structure Constraints (n m p : ℕ) where
  h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ

namespace Constraints

variable {m p : ℕ} (C : Constraints n m p)

/-- Standing hypothesis of p. 1: every `hᵢ` and every `gⱼ` is continuously differentiable. -/
def IsC1 : Prop :=
  (∀ i, ContDiff ℝ 1 (C.h i)) ∧ ∀ j, ContDiff ℝ 1 (C.g j)

/-- The feasible set `Ω = {x : h(x) = 0, g(x) ≤ 0}` of (1.1). -/
def feasible : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, C.h i x = 0) ∧ ∀ j, C.g j x ≤ 0}

/-- KKT at `xs` for the objective `f`, in multiplier form (feasibility is a separate hypothesis). -/
def IsKKT (f : EuclideanSpace ℝ (Fin n) → ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ j, 0 ≤ mu j) ∧ (∀ j, C.g j xs ≠ 0 → mu j = 0) ∧
    gradient f xs + ∑ i, lam i • gradient (C.h i) xs + ∑ j, mu j • gradient (C.g j) xs = 0

/-- Linearized cone (3.7): `∇hᵢ(x*)ᵀd = 0` for all `i`, `∇gⱼ(x*)ᵀd ≤ 0` for `j ∈ J(x*)`. -/
def linCone (xs : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | (∀ i, ⟪gradient (C.h i) xs, d⟫_ℝ = 0) ∧
    ∀ j, C.g j xs = 0 → ⟪gradient (C.g j) xs, d⟫_ℝ ≤ 0}

/-- Abadie's constraint qualification, p. 5: `L_Ω(x*) = T_Ω(x*)`. -/
def Abadie (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  C.linCone xs = tangentCone C.feasible xs

end Constraints

end StrictCQ.CAKKT


