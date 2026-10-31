-- Prove2me | Definitions.Def_MonoIncExtrap_Setting
-- name    : MonoIncExtrap_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:45.19686+00:00
-- url     : https://prove2.me/theorems/2475b43b-8ceb-4f22-adb9-6158e85d37d8
-- title:
--   Problem (1): $F+B$, local Lipschitz continuity, the residual, Assumption 1 and the resolvent family
-- statement:
--   Let $B:\mathbb R^n\rightrightarrows\mathbb R^n$ be a set-valued operator and $F$ a point-valued operator. This module fixes the objects of the monotone inclusion
--   $$
--   \text{find }x\in\mathbb R^n\text{ such that }0\in(F+B)(x).
--   $$
--
--   1. The sum is $(F+B)(x)=\{F(x)+b:b\in B(x)\}$.
--   2. A map $g$ is $L$-Lipschitz on $\Omega$ if $\|g(x)-g(y)\|\le L\|x-y\|$ for all $x,y\in\Omega$, and locally Lipschitz on a closed set $\widehat\Omega$ if it is $L_\Omega$-Lipschitz, for some $L_\Omega>0$, on every compact $\Omega\subseteq\widehat\Omega$.
--   3. The residual of $T$ at $x$ is $\mathrm{res}_T(x)=\inf\{\|v\|:v\in T(x)\}$, and $x$ is an $\varepsilon$-residual solution if $x\in\mathrm{dom}\,B$ and $\mathrm{res}_{F+B}(x)\le\varepsilon$.
--   4. Assumption 1 with parameter $\mu\ge0$ says that $B$ is maximal monotone with nonempty domain, $F$ is monotone and locally Lipschitz on $\mathrm{cl}(\mathrm{dom}\,B)$, and
--   $$
--   \langle u-v,x-y\rangle\ge\mu\|x-y\|^2\qquad\forall x,y\in\mathrm{dom}\,B,\ u\in(F+B)(x),\ v\in(F+B)(y).
--   $$
--   5. A resolvent family is a family $J$ with $J_\gamma=(I+\gamma B)^{-1}$ for every $\gamma>0$.
--   6. The relation $w=(I+\rho T)^{-1}(z)$ is written $\rho^{-1}(z-w)\in T(w)$.
--   7. $\{x\in\mathrm{dom}\,B:\|x-c\|\le R\}$ is the common shape of the bounded sets of the paper.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Monotonicity, maximal monotonicity, $\mathrm{dom}$ and the resolvent relation are the published `ThreeOpSplitting.Convergence` notions. Assumption 1(a) is the separate predicate `IsSolution`, because the paper names the solution $x^*$. The local Lipschitz notion is the paper's compact-subset form, not Mathlib's neighbourhood form. `res` is a real `sInf`, whose value on an empty set is a junk $0$; it is used only at points of $\mathrm{dom}\,B$.
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, arXiv:2206.00973v3, (1), (2), Assumption 1, p.1; §1.1, p.3

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-! # The monotone inclusion problem (1)

Z. Lu and S. Mei, *Primal-dual extrapolation methods for monotone inclusions under local Lipschitz
continuity*, arXiv:2206.00973v3, §1 and §1.1, pp.1–3.

Set-valued operators are `A : H → Set H`. Monotonicity, maximal monotonicity, `dom` and the
resolvent relation `IsResolvent` are the published `ThreeOpSplitting.Convergence` notions.

**Formalization Note.** The definitions are stated on a real inner product space `H`; every theorem
of this mission takes `H = EuclideanSpace ℝ (Fin n)`, the paper's `ℝⁿ`. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The sum `F + B`** of a point-valued operator `F` and a set-valued operator `B`:
`(F + B)(x) = {F x + b : b ∈ B x}`. arXiv:2206.00973v3, (1), p.1.

**Formalization Note.** `F` is a total map, so `F + B` is empty exactly where `B` is, and
`dom (F + B) = dom B`; values of `F` off `dom B` never enter `sumOp`. -/
def sumOp (F : H → H) (B : H → Set H) : H → Set H :=
  fun x => {w | ∃ b ∈ B x, w = F x + b}

/-- **`L`-Lipschitz continuity on a set.** arXiv:2206.00973v3, §1.1, p.3: "`g` is called
`L`-Lipschitz continuous on a set `Ω` for some constant `L > 0` if
`‖g(x) − g(y)‖ ≤ L‖x − y‖` for all `x, y ∈ Ω`".

**Formalization Note.** Positivity of `L` is a separate hypothesis wherever it is meant. -/
def IsLipschitzOn (g : H → H) (Ω : Set H) (L : ℝ) : Prop :=
  ∀ x ∈ Ω, ∀ y ∈ Ω, ‖g x - g y‖ ≤ L * ‖x - y‖

/-- **Local Lipschitz continuity on a closed set.** arXiv:2206.00973v3, §1.1, p.3: "`g` is called
locally Lipschitz continuous on a closed set `Ω̂` if `g` is `L_Ω`-Lipschitz continuous on any
compact set `Ω ⊆ Ω̂` for some `L_Ω > 0`".

**Formalization Note.** This is the paper's compact-subset form, not Mathlib's neighbourhood form
`LocallyLipschitzOn`. -/
def IsLocallyLipschitzOn (g : H → H) (Ω' : Set H) : Prop :=
  ∀ Ω ⊆ Ω', IsCompact Ω → ∃ L : ℝ, 0 < L ∧ IsLipschitzOn g Ω L

/-- **Monotonicity of a point-valued operator on a set**: `⟨F x − F y, x − y⟩ ≥ 0` for all
`x, y ∈ Ω`. arXiv:2206.00973v3, §1, p.1 ("`F` is a monotone point-valued … operator on
`cl(dom B)`"). -/
def IsMonotoneOn (F : H → H) (Ω : Set H) : Prop :=
  ∀ x ∈ Ω, ∀ y ∈ Ω, 0 ≤ ⟪F x - F y, x - y⟫_ℝ

/-- **The residual** `res_T(x) = inf{‖v‖ : v ∈ T(x)}`. arXiv:2206.00973v3, §1.1, p.3.

**Formalization Note.** The paper defines it at points of `dom T`, where the infimum is over a
nonempty set bounded below by `0`, and every use below is at such a point. Off `dom T`, Lean's
`sInf ∅ = 0` is a junk value. -/
noncomputable def res (T : H → Set H) (x : H) : ℝ :=
  sInf ((fun v => ‖v‖) '' T x)

/-- **`ε`-residual solution of (1).** arXiv:2206.00973v3, §1.1, p.3: "a point `x` is called an
`ε`-residual solution of problem (1) if `x ∈ dom B` and `res_{F+B}(x) ≤ ε`". The membership
`x ∈ dom B` keeps the junk value of `res` out. -/
def IsResidualSolution (F : H → H) (B : H → Set H) (ε : ℝ) (x : H) : Prop :=
  x ∈ dom B ∧ res (sumOp F B) x ≤ ε

/-- **A solution of problem (1)**: `0 ∈ (F + B)(x)`. arXiv:2206.00973v3, (1), p.1. -/
def IsSolution (F : H → H) (B : H → Set H) (x : H) : Prop :=
  (0 : H) ∈ sumOp F B x

/-- **The standing assumptions on (1)**, with monotonicity parameter `μ`.
arXiv:2206.00973v3, §1, p.1: `B` is maximal monotone with nonempty domain, `F` is monotone on
`cl(dom B)`, and Assumption 1(b), 1(c).

**Formalization Note.** Assumption 1(a) (a solution exists) is the separate predicate
`IsSolution`, because the paper names the solution `x∗`. Assumption 1(d) (the resolvent can be
evaluated) has no mathematical content; it appears as a resolvent family, `IsResolventFamily`. -/
structure Assumption1 (F : H → H) (B : H → Set H) (μ : ℝ) : Prop where
  /-- `B` is maximal monotone. -/
  maximal : IsMaximalMonotone B
  /-- `dom B` is nonempty. -/
  dom_nonempty : (dom B).Nonempty
  /-- `F` is monotone on `cl(dom B)`. -/
  monotone : IsMonotoneOn F (closure (dom B))
  /-- The monotonicity parameter is nonnegative, `μ ≥ 0`. -/
  μ_nonneg : 0 ≤ μ
  /-- Assumption 1(b), inequality (2): `⟨u − v, x − y⟩ ≥ μ‖x − y‖²` for `x, y ∈ dom B`,
  `u ∈ (F + B)(x)`, `v ∈ (F + B)(y)`. -/
  strong : ∀ x ∈ dom B, ∀ y ∈ dom B, ∀ u ∈ sumOp F B x, ∀ v ∈ sumOp F B y,
    μ * ‖x - y‖ ^ 2 ≤ ⟪u - v, x - y⟫_ℝ
  /-- Assumption 1(c): `F` is locally Lipschitz continuous on `cl(dom B)`. -/
  locally_lipschitz : IsLocallyLipschitzOn F (closure (dom B))

/-- **A resolvent family of `B`**: `J γ` is the resolvent `(I + γB)⁻¹` for every `γ > 0`.
arXiv:2206.00973v3, Assumption 1(d), p.1, and §1.1, p.3.

**Formalization Note.** Values `J γ` at `γ ≤ 0` are unconstrained and never used. By the published
`DouglasRachfordPPA.GenDR.resolvent_single_valued_full_domain`, such a family exists and is unique
on `γ > 0` when `B` is maximal monotone. -/
def IsResolventFamily (J : ℝ → H → H) (B : H → Set H) : Prop :=
  ∀ γ : ℝ, 0 < γ → IsResolvent γ B (J γ)

/-- **`w = (I + ρT)⁻¹(z)`, as a relation.** arXiv:2206.00973v3, §1.1, p.3: "`z = (I + 𝒯)⁻¹(x)` if
and only if `x ∈ (I + 𝒯)(z)`". Here `z ∈ w + ρ T(w)` is written as `ρ⁻¹(z − w) ∈ T(w)`, the shape
of `IsResolvent`. -/
def IsResolventPoint (ρ : ℝ) (T : H → Set H) (z w : H) : Prop :=
  ρ⁻¹ • (z - w) ∈ T w

/-- `{x ∈ dom B : ‖x − c‖ ≤ R}`, the shape of the sets (8), (10), (16), (17), (73), (74) of
arXiv:2206.00973v3. All of them are subsets of `dom B`. -/
def ballIn (B : H → Set H) (c : H) (R : ℝ) : Set H :=
  {x | x ∈ dom B ∧ ‖x - c‖ ≤ R}

end MonoIncExtrap


