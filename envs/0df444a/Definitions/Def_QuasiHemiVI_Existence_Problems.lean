-- Prove2me | Definitions.Def_QuasiHemiVI_Existence_Problems
-- name    : QuasiHemiVI_Existence_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:11.686735+00:00
-- url     : https://prove2.me/theorems/ce682558-dccc-4b49-afb7-0a88b1eb9fa5
-- title:
--   Solution sets: Problem 1.1 ($\Gamma(f)$), Problem 3.3 ($\mathrm{SOL}(C;T,J,\varphi,f)$), the Minty inequality (3.4), and the variational selection $S$
-- statement:
--   Let $V$, $X$, $Y$ be real normed spaces, $C\subseteq V$, $K:C\to2^C$ and $T:C\to2^{V^*}$ multivalued maps, $\varphi:V\times V\to\mathbb R$, $J:X\to\mathbb R$, $h:V\to\mathbb R$, $\gamma:V\to X$ and $\pi:V\to Y$ bounded linear operators and $f\in Y^*$. Write $J^0$ and $\partial J$ for the Clarke derivative and gradient (Definition 2.4).
--
--   1. **Problem 3.3.** $\mathrm{SOL}(C;T,J,\varphi,f)$ is the set of $u\in C$ for which there is $u^*\in T(u)$ with
--   $$\langle u^*,v-u\rangle+\varphi(v,u)+J^0(\gamma u;\gamma(v-u))\ge\langle f,\pi(v-u)\rangle_{Y^*\times Y}\quad\text{for all }v\in C.\qquad(3.3)$$
--   2. **Minty inequality (3.4).** The set of $u\in C$ such that for all $v\in C$, $v^*\in T(v)$ and $\eta_v\in\partial J(\gamma v)$,
--   $$\langle v^*,v-u\rangle+\varphi(v,u)+\langle\eta_v,\gamma(v-u)\rangle_{X^*\times X}\ge\langle f,\pi(v-u)\rangle_{Y^*\times Y}+h(v-u).$$
--   With $C$ replaced by $K(u)$ this is inequality (3.20) of Theorem 3.8 (i).
--   3. **Problem 1.1.** $\Gamma(f)$ is the set of $u\in C$ with $u\in K(u)$ for which there is $u^*\in T(u)$ with
--   $$\langle u^*,v-u\rangle+\varphi(v,u)+J^0(\gamma u;\gamma(v-u))\ge\langle f,\pi(v-u)\rangle_{Y^*\times Y}\quad\text{for all }v\in K(u).\qquad(1.1)$$
--   4. **Variational selection.** For $w\in C$, $S(w)$ is the set of $u\in K(w)$ for which there is $u^*\in T(u)$ with the inequality (3.21), i.e. (3.3) with $C$ replaced by $K(w)$: $S(w)=\mathrm{SOL}(K(w);T,J,\varphi,f)$.
--
--   Problem 1.1 is the generalized nonlinear quasi-hemivariational inequality whose solvability is the subject of the mission; Problem 3.3 is its version with a fixed constraint set, and $S$ links the two: the fixed points of $S$ are exactly the solutions of Problem 1.1.
--
--   **Formalization Note** Adjoints are written out: $\langle\pi^*f,w\rangle=f(\pi w)$ and $\langle\gamma^*\eta,w\rangle=\eta(\gamma w)$. The maps $K$ and $T$ are total functions on $V$; only their values on $C$ matter.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1247, Problem 1.1, (1.1); p. 1258 (Γ(f)); p. 1251, Problem 3.3, (3.3), Theorem 3.4 (i), (3.4); p. 1259, Theorem 3.8 (i), (3.20), (3.21) and the variational selection S

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv

namespace QuasiHemiVI.Existence

/-- `SOL(C; T, J, φ, f)`, the solution set of the generalized hemivariational inequality
Problem 3.3 (p. 1251): the `u ∈ C` for which there is `u* ∈ T(u)` with
`⟨u*, v - u⟩ + φ(v, u) + J⁰(γu; γ(v - u)) ≥ ⟨f, π(v - u)⟩` for all `v ∈ C` (inequality (3.3)). -/
def SOL {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) : Set V :=
  {u | u ∈ C ∧ ∃ us ∈ T u, ∀ v ∈ C,
    f (π (v - u)) ≤ us (v - u) + φ v u + clarkeDeriv J (γ u) (γ (v - u))}

/-- The solution set of the Minty-type inequality (3.4) (Theorem 3.4 (i), p. 1251): the `u ∈ C`
with `⟨v*, v - u⟩ + φ(v, u) + ⟨η_v, γ(v - u)⟩ ≥ ⟨f, π(v - u)⟩ + h(v - u)` for all `v ∈ C`, all
`v* ∈ T(v)` and all `η_v ∈ ∂J(γv)`. With `C` replaced by `K(u)` it is inequality (3.20). -/
def MintySol {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (h : V → ℝ) : Set V :=
  {u | u ∈ C ∧ ∀ v ∈ C, ∀ vs ∈ T v, ∀ η ∈ clarkeGrad J (γ v),
    f (π (v - u)) + h (v - u) ≤ vs (v - u) + φ v u + η (γ (v - u))}

/-- `Γ(f)`, the solution set of the generalized nonlinear quasi-hemivariational inequality
Problem 1.1 (p. 1247; notation p. 1258): the `u ∈ C` with `u ∈ K(u)` for which there is
`u* ∈ T(u)` with `⟨u*, v - u⟩ + φ(v, u) + J⁰(γu; γ(v - u)) ≥ ⟨f, π(v - u)⟩` for all `v ∈ K(u)`
(inequality (1.1)). -/
def Gamma {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : Set V) (K : V → Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) : Set V :=
  {u | u ∈ C ∧ u ∈ K u ∧ ∃ us ∈ T u, ∀ v ∈ K u,
    f (π (v - u)) ≤ us (v - u) + φ v u + clarkeDeriv J (γ u) (γ (v - u))}

/-- The variational selection `S(w)` (proof of Theorem 3.8 (ii), p. 1259): the set of solutions
`u ∈ K(w)` of inequality (3.21), i.e. of Problem 3.3 with `C` replaced by `K(w)`. -/
def varSel {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (K : V → Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (w : V) : Set V :=
  SOL (K w) T φ J γ π f

end QuasiHemiVI.Existence


