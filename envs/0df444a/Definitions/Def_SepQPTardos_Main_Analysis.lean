-- Prove2me | Definitions.Def_SepQPTardos_Main_Analysis
-- name    : SepQPTardos_Main_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:00.745621+00:00
-- url     : https://prove2.me/theorems/9fc9b02d-8873-4fe2-8c07-9bc39501e5dc
-- title:
--   The relaxed polyhedra $P_F(b)$, the LPs (15), (18), (25), the systems (17), (26), the scale $E_F$, and the analysis context of §4
-- statement:
--   Let $A$ be an integer $r\times m$ matrix and $b\in\mathbb R^r$, $q,c\in\mathbb R^m$. Write $N=\{e:q_e>0\}$, $Z=\{e:q_e=0\}$ and, for an index set $F\subseteq[m]$ with complement $\bar F$,
--
--   $$P_F(b)=\{x\in\mathbb R^m: Ax=b,\ x_{\bar F}\ge0\}.$$
--
--   An **optimum on** $P_F(b)$ is a minimiser of $\Phi$ over $P_F(b)$. Further:
--
--   1. $\rho_F(z)=\max_{e\notin F}z_e$, the empty maximum being $0$.
--   2. $\alpha_F$ is the optimal value of **LP (15)**: minimise $\alpha$ subject to $Au=b$, $0\le u_{\bar F}\le\alpha\mathbf 1$, $\alpha\ge0$, $u_F$ free; it is defined as the infimum of the feasible values of $\alpha$. An optimal solution is a feasible $(u,\alpha_F)$.
--   3. **System (17)** for such $u$, with $v=u_{\bar F}$: $t_{\bar F}=v$, $A_Ft_F=b-A_{\bar F}v$, and $Q_Ft_F+c_F=A_F^\top\lambda$ for some $\lambda\in\mathbb R^r$. A **trial point** is a solution $t$ of (17) built from an optimal solution of (15).
--   4. With $g=Qt+c$, $V_F$ is the optimal value of the **descent LP (18)**: maximise $-g^\top d$ subject to $Ad=0$, $d_{\bar F}\ge0$ and $-1/q_e\le d_e\le1/q_e$ for $e\in N$; it is defined as the supremum of the feasible values. The **scale** is $E_F=\max(\alpha_F,V_F)$, eq. (20).
--   5. **LP (25)**: minimise $c_Z^\top x_Z$ over vectors $x$ with $x_N=t_N$, $x_Z\ge0$ and $Ax=b$.
--   6. **System (26)** in the free variable $\pi$: $A^\top\pi\le Qx+c$, with $(A^\top\pi)_e=(Qx+c)_e$ for every $e$ with $x_e>0$.
--   7. The **box polyhedron** of Lemma 3.2 is $\{u: Au=\beta,\ \ell\le u\le h\}$ for real $\beta,\ell,h$, and a separable quadratic is $\psi(u)=\sum_e(a_eu_e^2+b_eu_e)$.
--   8. The **analysis context of §4**: $q\ge0$, $(x^*,\pi^*)$ is an optimal primal–dual pair of (1), i.e. it satisfies (8), and $F\subseteq T^*=\{e:\sigma^*_e=0\}$ where $\sigma^*=Qx^*+c-A^\top\pi^*$.
--
--   These are the objects of the revelation algorithm of §4 and of the local solver of §3.
--
--   **Formalization Note.** $\alpha_F$ and $V_F$ are an infimum and a supremum of real sets; the milestones assert that under the context of §4 these sets are nonempty and bounded and that the optima are attained, so the values are the LP optima of the paper.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2.2 p. 5 (N, Z); §3 p. 6 (P_F(b), Lemma 3.2); §4 pp. 7–10, eqs. (15), (17), (18), (20), (25), (26)

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem

open Matrix

noncomputable section

namespace SepQPTardos.Main

/-!
# The objects of §§2.2–4: `N`, `Z`, `P_F(b)`, `ρ_F`, the LPs (15), (18), (25), the systems
(17), (26), the scale `E_F`, and the analysis context of §4

Cui–Li–Miao, STOC 2027 submission #829 (October 2026), §2.2 p. 5, §3 p. 6, §4 pp. 7–10.
`A` is an integer `r × m` matrix (cast to ℝ); `b`, `c`, `q` are real vectors.

* `N = {e : qₑ > 0}`, `Z = {e : qₑ = 0}` (p. 5).
* The box polyhedron `{u : Au = β, ℓ ≤ u ≤ h}` and separable convex quadratics of Lemma 3.2.
* `P_F(b) = {x : Ax = b, x_{F̄} ≥ 0}` for an index set `F` (pp. 6–7); an *optimum on `P_F(b)`*
  is a minimiser of `Φ` over `P_F(b)`.
* `ρ_F(z) = max_{e ∉ F} zₑ`, the empty maximum being `0` (p. 8).
* `α_F` is the optimal value of LP (15): `min α` s.t. `Au = b`, `0 ≤ u_{F̄} ≤ α𝟙`, `α ≥ 0`,
  `u_F` free (p. 8). It is defined as the infimum of the feasible values of `α`.
* (17): `t_{F̄} = v`, `A_F t_F = b − A_{F̄} v`, `Q_F t_F + c_F = A_Fᵀ λ` for some `λ` (p. 8), where
  `v = u_{F̄}` for an optimal solution `(u, α_F)` of (15).
* `g = Qt + c` and `V_F` is the optimal value of LP (18): `max −gᵀd` s.t. `Ad = 0`, `d_{F̄} ≥ 0`,
  `−1/qₑ ≤ dₑ ≤ 1/qₑ` for `e ∈ N` (p. 8). It is defined as the supremum of the feasible values.
* `E_F = max(α_F, V_F)`, eq. (20) (p. 9).
* LP (25): `min c_Zᵀ x_Z` s.t. `A_Z x_Z = b − A_N t_N`, `x_Z ≥ 0` (p. 10), written for the
  combined vector `x` with `x_N = t_N`.
* System (26): `Aᵀπ ≤ Qx + c` and `(Aᵀπ)ₑ = (Qx + c)ₑ` whenever `xₑ > 0` (p. 10).
* The §4 context (p. 7): `q ≥ 0`, an optimal primal–dual pair `(x*, π*)` of (1), i.e. a
  solution of (8), and `F ⊆ T* = {e : σ*ₑ = 0}` with `σ* = Qx* + c − Aᵀπ*`.
-/

variable {r m : ℕ}

/-- `N = {e : qₑ > 0}`. -/
def Nset (q : Fin m → ℝ) : Finset (Fin m) := Finset.univ.filter fun e => 0 < q e

/-- `Z = {e : qₑ = 0}`. -/
def Zset (q : Fin m → ℝ) : Finset (Fin m) := Finset.univ.filter fun e => q e = 0

/-- The relaxed polyhedron `P_F(b) = {x : Ax = b, x_{F̄} ≥ 0}`. -/
def PF (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (F : Finset (Fin m)) :
    Set (Fin m → ℝ) :=
  {x | castMat A *ᵥ x = b ∧ ∀ e, e ∉ F → 0 ≤ x e}

/-- `z` minimises `f` over `S`. -/
def IsMinimizer {α : Type*} (S : Set α) (f : α → ℝ) (z : α) : Prop :=
  z ∈ S ∧ ∀ y ∈ S, f z ≤ f y

/-- The box polyhedron `P = {u : Au = β, ℓ ≤ u ≤ h}` of Lemma 3.2 (p. 6); the bounds need not
be integral. -/
def boxPoly (A : Matrix (Fin r) (Fin m) ℤ) (β : Fin r → ℝ) (ℓ hi : Fin m → ℝ) :
    Set (Fin m → ℝ) :=
  {u | castMat A *ᵥ u = β ∧ ∀ e, ℓ e ≤ u e ∧ u e ≤ hi e}

/-- A separable quadratic `ψ(u) = ∑ₑ (aₑuₑ² + bₑuₑ)`; it is convex when `a ≥ 0`. -/
def sepQuad (a bl : Fin m → ℝ) (u : Fin m → ℝ) : ℝ := ∑ e, (a e * u e ^ 2 + bl e * u e)

/-- `ρ_F(z) = max_{e ∉ F} zₑ`, with the empty maximum equal to `0`. -/
def rhoF (F : Finset (Fin m)) (z : Fin m → ℝ) : ℝ :=
  if h : Fᶜ.Nonempty then Fᶜ.sup' h z else 0

/-- Feasibility in LP (15): `Au = b`, `0 ≤ uₑ ≤ α` for `e ∉ F`, `α ≥ 0` (`u_F` free). -/
def LP15Feas (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (F : Finset (Fin m))
    (u : Fin m → ℝ) (α : ℝ) : Prop :=
  castMat A *ᵥ u = b ∧ (∀ e, e ∉ F → 0 ≤ u e ∧ u e ≤ α) ∧ 0 ≤ α

/-- `α_F`, the optimal value of LP (15): the infimum of its feasible values of `α`. -/
noncomputable def alphaF (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (F : Finset (Fin m)) :
    ℝ :=
  sInf {α | ∃ u, LP15Feas A b F u α}

/-- `(u, α_F)` is an optimal solution of LP (15). -/
def IsLP15Opt (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (F : Finset (Fin m))
    (u : Fin m → ℝ) : Prop :=
  LP15Feas A b F u (alphaF A b F)

/-- `t` solves the linear system (17) built from `v = u_{F̄}`: `tₑ = uₑ` for `e ∉ F`,
`A_F t_F = b − A_{F̄} u_{F̄}` (equivalently `At = b`), and `qₑtₑ + cₑ = (Aᵀλ)ₑ` for `e ∈ F` for
some `λ ∈ ℝ^r`. -/
def Sys17 (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (q c : Fin m → ℝ)
    (F : Finset (Fin m)) (u t : Fin m → ℝ) : Prop :=
  (∀ e, e ∉ F → t e = u e) ∧ castMat A *ᵥ t = b ∧
    ∃ lam : Fin r → ℝ, ∀ e, e ∈ F → q e * t e + c e = ((castMat A)ᵀ *ᵥ lam) e

/-- `t` is a trial point of §4.1: a solution of (17) whose `v` comes from an optimal solution
of (15). -/
def IsTrialPoint (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (q c : Fin m → ℝ)
    (F : Finset (Fin m)) (t : Fin m → ℝ) : Prop :=
  ∃ u, IsLP15Opt A b F u ∧ Sys17 A b q c F u t

/-- The gradient `g = Qt + c` of `Φ` at `t`. -/
def grad (q c t : Fin m → ℝ) : Fin m → ℝ := fun e => q e * t e + c e

/-- Feasibility in the descent LP (18): `Ad = 0`, `d_{F̄} ≥ 0`, `−1/qₑ ≤ dₑ ≤ 1/qₑ` for `e ∈ N`. -/
def LP18Feas (A : Matrix (Fin r) (Fin m) ℤ) (q : Fin m → ℝ) (F : Finset (Fin m))
    (d : Fin m → ℝ) : Prop :=
  castMat A *ᵥ d = 0 ∧ (∀ e, e ∉ F → 0 ≤ d e) ∧
    ∀ e, 0 < q e → -(1 / q e) ≤ d e ∧ d e ≤ 1 / q e

/-- `V_F`, the optimal value of the descent LP (18) at the trial point `t`: the supremum of
`−gᵀd` over its feasible `d`, `g = Qt + c`. -/
noncomputable def VF (A : Matrix (Fin r) (Fin m) ℤ) (q c : Fin m → ℝ) (F : Finset (Fin m))
    (t : Fin m → ℝ) : ℝ :=
  sSup {v | ∃ d, LP18Feas A q F d ∧ v = -(grad q c t ⬝ᵥ d)}

/-- The scale `E_F = max(α_F, V_F)`, eq. (20). -/
noncomputable def EF (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (q c : Fin m → ℝ)
    (F : Finset (Fin m)) (t : Fin m → ℝ) : ℝ :=
  max (alphaF A b F) (VF A q c F t)

/-- Feasibility of the combined vector `x` in LP (25): `x_N = t_N`, `x_Z ≥ 0`, `Ax = b`. -/
def LP25Feas (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (q t : Fin m → ℝ)
    (x : Fin m → ℝ) : Prop :=
  (∀ e, 0 < q e → x e = t e) ∧ (∀ e, q e = 0 → 0 ≤ x e) ∧ castMat A *ᵥ x = b

/-- The objective `c_Zᵀ x_Z` of LP (25). -/
def LP25Obj (q c x : Fin m → ℝ) : ℝ := ∑ e ∈ Zset q, c e * x e

/-- System (26) in the free variable `π`: `Aᵀπ ≤ Qx + c`, with equality on every `e` with
`xₑ > 0`. -/
def Sys26 (A : Matrix (Fin r) (Fin m) ℤ) (q c x : Fin m → ℝ) (π : Fin r → ℝ) : Prop :=
  ∀ e, ((castMat A)ᵀ *ᵥ π) e ≤ q e * x e + c e ∧
    (0 < x e → ((castMat A)ᵀ *ᵥ π) e = q e * x e + c e)

/-- The analysis context of §4 (p. 7): `q ≥ 0`, `(x*, π*)` is an optimal primal–dual pair of
(1) (it satisfies (8)), and `F ⊆ T* = {e : σ*ₑ = 0}`. -/
def Sec4Context (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ) (q c : Fin m → ℝ)
    (xs : Fin m → ℝ) (πs : Fin r → ℝ) (F : Finset (Fin m)) : Prop :=
  (∀ e, 0 ≤ q e) ∧ KKT (castMat A) b q c xs πs ∧
    ∀ e, e ∈ F → slack (castMat A) q c xs πs e = 0

end SepQPTardos.Main


