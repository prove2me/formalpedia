-- Prove2me | Definitions.Def_SunNLSDP_Equiv_Setting
-- name    : SunNLSDP_Equiv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:00.553438+00:00
-- url     : https://prove2.me/theorems/3ca14f6e-1ee0-4806-a802-81274fc13da8
-- title:
--   §1–§4, pp. 1–22 — S^p, Π_D, B†, Υ_B, tangent sets, (NLSDP), M(x̄), CQs, C(x̄), app, SSOSC, nondegeneracy, F, strong regularity, Lipschitz homeomorphisms, uniform growth, strong stability
-- statement:
--   This file fixes the objects of D. Sun's paper on nonlinear semidefinite programming.
--
--   **Spaces.** $\mathcal S^p$ is the space of real symmetric matrices indexed by a finite set, with the Frobenius inner product $\langle A,B\rangle=\mathrm{Tr}(A^TB)=\sum_{i,j}A_{ij}B_{ij}$ (p. 7); $\mathcal S^p_+$ and $\mathcal S^p_-=-\mathcal S^p_+$ are the positive and negative semidefinite cones. $Y=\Re^m\times\mathcal S^p$ and $Z=X\times\Re^m\times\mathcal S^p$ carry the sum of the inner products.
--
--   **Matrix objects.** $B^\dagger$ is the Moore–Penrose pseudo-inverse of $B\in\mathcal S^p$ (eigenvalues $\lambda\neq0$ inverted, $0$ kept), and (Definition 6)
--   $$\Upsilon_B(\Gamma,A):=2\langle\Gamma,AB^\dagger A\rangle .$$
--   For a spectral decomposition $A=P\,\mathrm{diag}(\lambda)P^T$, $\alpha,\beta,\gamma$ are the indices of positive, zero and negative eigenvalues, and $U_{ij}=(\max\{\lambda_i,0\}+\max\{\lambda_j,0\})/(|\lambda_i|+|\lambda_j|)$ with $0/0:=1$ (p. 7); the block form of (21) is spelled out entry by entry.
--
--   **Variational objects.** $\Pi_D$ is the metric projector onto a closed convex set $D$ (13); $T_D(y)=\{d:\exists t_k\downarrow0,\ \mathrm{dist}(y+t_kd,D)=o(t_k)\}$ is the contingent cone (p. 3); $T^2_D(y,d)$ is the outer second order tangent set (30); $\sigma(y,D)=\sup_{z\in D}\langle z,y\rangle\in[-\infty,+\infty]$ is the support function (p. 14); $C(A;\mathcal S^p_+)=T_{\mathcal S^p_+}(A_+)\cap(A_+-A)^\perp$ with $A_+=\Pi_{\mathcal S^p_+}(A)$ (p. 8).
--
--   **The problem** (NLSDP): $\min f(x)$ s.t. $h(x)=0$, $g(x)\in\mathcal S^p_+$, with $f,h,g$ twice continuously differentiable (10). The Lagrangian is $L(x,\zeta,\Gamma)=f(x)+\langle\zeta,h(x)\rangle+\langle\Gamma,g(x)\rangle$; $\mathcal M(x)$ is the set of $(\zeta,\Gamma)$ with $J_xL(x,\zeta,\Gamma)=0$, $h(x)=0$, $\Gamma\in N_{\mathcal S^p_+}(g(x))$; a stationary point is a feasible point with $\mathcal M(x)\neq\emptyset$. Robinson's CQ (7)/(41), the strict CQ (42) and constraint nondegeneracy (48)/(49) are the conditions $J_xG(\bar x)X+\mathcal T=Y$ for $\mathcal T=T_K(G(\bar x))$, $T_K(G(\bar x))\cap\bar\Gamma^\perp$, $\mathrm{lin}(T_K(G(\bar x)))$, with $K=\{0\}\times\mathcal S^p_+$. The critical cone $C(\bar x)$ (31), the set $\mathrm{app}(\zeta,\Gamma)$ (38), $\widehat C(\bar x)=\bigcap_{\mathcal M(\bar x)}\mathrm{app}$ and the strong second order sufficient condition (47) follow the paper.
--
--   **KKT map and stability notions.** $F(x,\zeta,\Gamma)=(\nabla_xL,\,-h(x),\,-g(x)+\Pi_{\mathcal S^p_+}(g(x)+\Gamma))$ (51); the generalized equation (52) is $0\in\varphi(z)+N_D(z)$ with $\varphi=(\nabla_xL,-h,-g)$ and $D=X\times\Re^m\times\mathcal S^p_-$; strong regularity is Definition 14; locally and globally Lipschitz homeomorphisms are as in Remark 15 and Theorem 21 (h); $\Phi(\delta)=F'(\bar x,\bar\zeta,\bar\Gamma;\delta)$ (67). $C^2$-smooth parameterizations (61), the canonical parameterization, the uniform second order growth condition (Definition 17) and strong stability (Definition 19) complete the list.
--
--   **Formalization Note.** The brace systems (41), (42), (49) are read as one coupled system in $Y$: every $(a,B)$ equals $(J_xh(\bar x)d,\ J_xg(\bar x)d+T)$ for a single $d$, which is (7)/(48) at $K=\{0\}\times\mathcal S^p_+$ since $T_K(G(\bar x))=\{0\}\times T_{\mathcal S^p_+}(g(\bar x))$. "$\sup>0$" in (47) is stated as "some multiplier gives a positive value". $\Pi_D$ returns its argument when no minimiser exists; it is only applied to nonempty closed convex sets. $B^\dagger$ is computed by the continuous functional calculus. Clarke's Jacobian, the B-subdifferential, directional derivatives, normal cones and lineality spaces are the published platform definitions `NonsmoothNewton.Shared.clarkeJac`, `NonsmoothNewton.Local.dirDeriv` and `RobinsonSR.Reduction.Setting`. Parameter spaces $U$ in Definitions 17 and 19 range over Banach spaces in the universe of $X$.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, pp. 1–4 ((1)–(11)), pp. 5–9 (∂_B, ∂, (13), (15), U, (21), Definition 6), pp. 11–17 ((29)–(31), (38), Definitions 12–14, (51)–(53), Remark 15), pp. 19–22 ((61), Definitions 17, 19, (67))

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting

universe u

namespace SunNLSDP.Equiv

open scoped RealInnerProductSpace Topology
open Filter RobinsonSR.Reduction

noncomputable section

/-! ### The space `S^p` of symmetric matrices with the Frobenius inner product (p. 4, p. 7) -/

/-- The entrywise-symmetric vectors of `EuclideanSpace ℝ (n × n)`. As a subspace of a Euclidean
space it carries the inner product `⟪A, B⟫ = ∑_{i,j} A_ij B_ij = Tr(Aᵀ B)`, the Frobenius inner
product of p. 7. -/
def symSubmodule (n : Type) [Fintype n] [DecidableEq n] :
    Submodule ℝ (EuclideanSpace ℝ (n × n)) where
  carrier := {v | ∀ i j, v (i, j) = v (j, i)}
  add_mem' := by
    intro a b ha hb i j
    simp [ha i j, hb i j]
  zero_mem' := by
    intro i j
    simp
  smul_mem' := by
    intro c a ha i j
    simp [ha i j]

/-- `S^p` (p. 4): the real symmetric matrices indexed by the finite type `n`, as an inner-product
space with the Frobenius inner product. -/
abbrev SymMat (n : Type) [Fintype n] [DecidableEq n] : Type := ↥(symSubmodule n)

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The underlying matrix of an element of `S^p`. -/
def SymMat.toMat (A : SymMat n) : Matrix n n ℝ :=
  fun i j => (A : EuclideanSpace ℝ (n × n)) (i, j)

/-- The element of `S^p` given by the symmetric part `(M + Mᵀ)/2` of a square matrix; it is `M`
itself whenever `M` is symmetric (the only case in which it is used). -/
def SymMat.ofMat (M : Matrix n n ℝ) : SymMat n :=
  ⟨WithLp.toLp 2 (fun p : n × n => (M p.1 p.2 + M p.2 p.1) / 2), by
    intro i j
    simp [add_comm]⟩

/-- The cone `S^p_+` of positive semidefinite matrices (p. 4). -/
def psdCone (n : Type) [Fintype n] [DecidableEq n] : Set (SymMat n) :=
  {A | A.toMat.PosSemidef}

/-- The cone `S^p_- = -S^p_+` of negative semidefinite matrices (p. 16). -/
def nsdCone (n : Type) [Fintype n] [DecidableEq n] : Set (SymMat n) :=
  {A | (-A).toMat.PosSemidef}

/-- The Moore–Penrose pseudo-inverse `B†` of a symmetric matrix (Definition 6, p. 9), through the
continuous functional calculus: eigenvalues `λ ≠ 0` go to `λ⁻¹` and `0` to `0⁻¹ = 0`. -/
def pinv (B : SymMat n) : Matrix n n ℝ :=
  cfc (fun x : ℝ => x⁻¹) B.toMat

/-- Definition 6, p. 9: `Υ_B(Γ, A) := 2⟨Γ, A B† A⟩`, with the Frobenius product
`⟨Γ, M⟩ = Tr(Γᵀ M)` (p. 7). -/
def upsilon (B Γ A : SymMat n) : ℝ :=
  2 * Matrix.trace (Γ.toMat.transpose * (A.toMat * pinv B * A.toMat))

/-! ### Spectral data (15), the matrix `U` and the block form (21) (pp. 7–9) -/

/-- The matrix `U` of p. 7: `U_ij := (max{λ_i, 0} + max{λ_j, 0}) / (|λ_i| + |λ_j|)`, with `0/0 := 1`. -/
def Umat (lam : n → ℝ) (i j : n) : ℝ :=
  if |lam i| + |lam j| = 0 then 1 else (max (lam i) 0 + max (lam j) 0) / (|lam i| + |lam j|)

/-- The index set `β := {i : λ_i = 0}` of zero eigenvalues (p. 7), as a finite type. -/
abbrev betaIdx (lam : n → ℝ) : Type := {i : n // lam i = 0}

/-- The matrix inside `P [ ⋯ ] Pᵀ` in (21), p. 9, given `H̃ = Pᵀ H P` and the `β × β` block
`W(H̃_ββ)`, entry by entry, with `α = {λ_i > 0}`, `β = {λ_i = 0}`, `γ = {λ_i < 0}`:
`H̃_ij` on `α×α` and `α×β`; `H̃_ji` (the block `H̃_αβᵀ`) on `β×α`; `U_ij H̃_ij` on `α×γ`; `H̃_ji U_ji` (the block `H̃_αγᵀ ∘ U_αγᵀ`)
on `γ×α`; `W(H̃_ββ)_ij` on `β×β`; `0` on `β×γ`, `γ×β`, `γ×γ`. -/
def blockForm21 (lam : n → ℝ) (Ht : Matrix n n ℝ)
    (Wbb : Matrix (betaIdx lam) (betaIdx lam) ℝ) : Matrix n n ℝ :=
  fun i j =>
    if hi : lam i = 0 then
      if hj : lam j = 0 then Wbb ⟨i, hi⟩ ⟨j, hj⟩
      else if 0 < lam j then Ht j i
      else 0
    else if 0 < lam i then
      if 0 < lam j then Ht i j
      else if lam j = 0 then Ht i j
      else Umat lam i j * Ht i j
    else
      if 0 < lam j then Ht j i * Umat lam j i
      else 0

/-- Relation (21), p. 9, between `V : S^p → S^p` and `W : S^{|β|} → S^{|β|}`, for the spectral
decomposition `A = P diag(λ) Pᵀ`: for all `H ∈ S^p`, with `H̃ := Pᵀ H P`,
`V(H) = P [blockForm21 λ H̃ W(H̃_ββ)] Pᵀ`. -/
def Eq21 (P : Matrix n n ℝ) (lam : n → ℝ) (V : SymMat n →L[ℝ] SymMat n)
    (W : SymMat (betaIdx lam) →L[ℝ] SymMat (betaIdx lam)) : Prop :=
  ∀ H : SymMat n,
    (V H).toMat = P * blockForm21 lam (P.transpose * H.toMat * P)
      (W (SymMat.ofMat ((P.transpose * H.toMat * P).submatrix
        (fun i : betaIdx lam => (i : n)) (fun i : betaIdx lam => (i : n))))).toMat * P.transpose

/-! ### Metric projector, tangent sets, support function (pp. 2–3, 6, 11, 14) -/

open Classical in
/-- The metric projector `Π_D` (13), p. 6: the minimiser of `‖z - y‖` over `z ∈ D`. For a nonempty
closed convex `D` in a finite-dimensional inner-product space (the only case used) the minimiser
exists and is unique; when no minimiser exists the value is the junk `y`. -/
def metricProj {E : Type*} [NormedAddCommGroup E] (D : Set E) (y : E) : E :=
  if h : ∃ z ∈ D, ∀ w ∈ D, ‖z - y‖ ≤ ‖w - y‖ then Classical.choose h else y

/-- The contingent (Bouligand) cone, p. 3:
`T_D(y) = {d : ∃ t_k ↓ 0, dist(y + t_k d, D) = o(t_k)}`. -/
def tangentCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : Set E) (y : E) :
    Set E :=
  {d | ∃ t : ℕ → ℝ, (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
    Tendsto (fun k => Metric.infDist (y + t k • d) D / t k) atTop (𝓝 0)}

/-- The outer second order tangent set (30), p. 11:
`T²_D(y, d) = {w : ∃ t_k ↓ 0, dist(y + t_k d + ½ t_k² w, D) = o(t_k²)}`. -/
def secondOrderTangentSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : Set E)
    (y d : E) : Set E :=
  {w | ∃ t : ℕ → ℝ, (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
    Tendsto (fun k => Metric.infDist (y + t k • d + ((1 / 2 : ℝ) * t k ^ 2) • w) D / t k ^ 2)
      atTop (𝓝 0)}

/-- The support function `σ(y, D) := sup_{z ∈ D} ⟨z, y⟩` (p. 14), valued in `EReal`
(`-∞` for `D = ∅`, `+∞` when unbounded above). -/
def supportFn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (y : E) (D : Set E) :
    EReal :=
  ⨆ z ∈ D, ((⟪z, y⟫ : ℝ) : EReal)

/-- The critical cone of `S^p_+` at `A` (p. 8): `C(A; S^p_+) := T_{S^p_+}(A₊) ∩ (A₊ - A)^⊥`, where
`A₊ := Π_{S^p_+}(A)`. -/
def psdCriticalCone (A : SymMat n) : Set (SymMat n) :=
  tangentCone (psdCone n) (metricProj (psdCone n) A) ∩
    {B | ⟪metricProj (psdCone n) A - A, B⟫ = 0}

/-! ### The problem (NLSDP), (10)–(11), p. 4 -/

/-- The data `(f, h, g)` of a problem `min f(x) s.t. h(x) = 0, g(x) ∈ S^p_+` (10). -/
structure Data (X : Type*) (m : ℕ) (n : Type) [Fintype n] [DecidableEq n] where
  /-- the objective `f : X → ℜ` -/
  f : X → ℝ
  /-- the equality constraint `h : X → ℜ^m` -/
  h : X → EuclideanSpace ℝ (Fin m)
  /-- the semidefinite constraint `g : X → S^p` -/
  g : X → SymMat n

/-- (NLSDP) (10), p. 4: `f, h, g` twice continuously differentiable. -/
structure NLSDP (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] (m : ℕ)
    (n : Type) [Fintype n] [DecidableEq n] extends Data X m n where
  f_smooth : ContDiff ℝ 2 f
  h_smooth : ContDiff ℝ 2 h
  g_smooth : ContDiff ℝ 2 g

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {m : ℕ}

namespace Data

variable (P : Data X m n)

/-- Feasibility: `G(x) = (h(x), g(x)) ∈ K = {0} × S^p_+` (11). -/
def feasible (x : X) : Prop :=
  P.h x = 0 ∧ P.g x ∈ psdCone n

/-- The Lagrangian `L(x, ζ, Γ) = f(x) + ⟨ζ, h(x)⟩ + ⟨Γ, g(x)⟩` (p. 16). -/
def lagrangian (x : X) (ζ : EuclideanSpace ℝ (Fin m)) (Γ : SymMat n) : ℝ :=
  P.f x + ⟪ζ, P.h x⟫ + ⟪Γ, P.g x⟫

/-- The multiplier set `M(x)` ((6), p. 3; (50), p. 16): the pairs `(ζ, Γ)` with `J_x L(x, ζ, Γ) = 0`
and `(ζ, Γ) ∈ N_K(G(x))`, i.e. `h(x) = 0` and `Γ ∈ N_{S^p_+}(g(x))` (so `Γ ⪯ 0`, `⟨Γ, g(x)⟩ = 0`). -/
def multipliers (x : X) : Set (EuclideanSpace ℝ (Fin m) × SymMat n) :=
  {μ | fderiv ℝ (fun y => P.lagrangian y μ.1 μ.2) x = 0 ∧ P.h x = 0 ∧
    μ.2 ∈ normalCone (psdCone n) (P.g x)}

/-- A stationary point: feasible with `M(x)` nonempty (p. 2). -/
def stationary (x : X) : Prop :=
  P.feasible x ∧ (P.multipliers x).Nonempty

/-- `⟨d, J²_xx L(x, ζ, Γ) d⟩`: the second Fréchet derivative of `x ↦ L(x, ζ, Γ)` applied to `(d, d)`. -/
def hessL (x : X) (ζ : EuclideanSpace ℝ (Fin m)) (Γ : SymMat n) (d : X) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ (fun x' => P.lagrangian x' ζ Γ) y) x d d

/-- Robinson's CQ (7)/(41), p. 3 and p. 13, for `K = {0} × S^p_+`:
`J_x G(x̄) X + T_K(G(x̄)) = Y`, i.e. every `(a, B) ∈ ℜ^m × S^p` is `(J_x h(x̄) d, J_x g(x̄) d + T)`
with one `d ∈ X` and `T ∈ T_{S^p_+}(g(x̄))` (the brace of (41) is one coupled system). -/
def RobinsonCQ (xbar : X) : Prop :=
  ∀ (a : EuclideanSpace ℝ (Fin m)) (B : SymMat n), ∃ d : X,
    fderiv ℝ P.h xbar d = a ∧ B - fderiv ℝ P.g xbar d ∈ tangentCone (psdCone n) (P.g xbar)

/-- The strict constraint qualification (42), p. 13, at `(x̄, Γ̄)` (coupled, as (7)):
every `(a, B)` is `(J_x h(x̄) d, J_x g(x̄) d + T)` with `T ∈ T_{S^p_+}(g(x̄)) ∩ Γ̄^⊥`. -/
def StrictCQ (xbar : X) (Γbar : SymMat n) : Prop :=
  ∀ (a : EuclideanSpace ℝ (Fin m)) (B : SymMat n), ∃ d : X,
    fderiv ℝ P.h xbar d = a ∧
      B - fderiv ℝ P.g xbar d ∈ tangentCone (psdCone n) (P.g xbar) ∩ {T | ⟪Γbar, T⟫ = 0}

/-- Constraint nondegeneracy, Definition 13 (48)/(49), p. 16, for `K = {0} × S^p_+`:
`J_x G(x̄) X + lin(T_K(G(x̄))) = Y` (coupled system). -/
def Nondegenerate (xbar : X) : Prop :=
  ∀ (a : EuclideanSpace ℝ (Fin m)) (B : SymMat n), ∃ d : X,
    fderiv ℝ P.h xbar d = a ∧
      B - fderiv ℝ P.g xbar d ∈ (linealitySpace (tangentCone (psdCone n) (P.g xbar)) : Set (SymMat n))

/-- The critical cone (31), p. 11: `C(x̄) = {d : J_x G(x̄) d ∈ T_K(G(x̄)), J_x f(x̄) d ≤ 0}`, with
`T_K(G(x̄)) = {0} × T_{S^p_+}(g(x̄))`. -/
def criticalCone (xbar : X) : Set X :=
  {d | fderiv ℝ P.h xbar d = 0 ∧ fderiv ℝ P.g xbar d ∈ tangentCone (psdCone n) (P.g xbar) ∧
    fderiv ℝ P.f xbar d ≤ 0}

/-- `app(ζ, Γ)` (38), p. 12: `{d : J_x h(x̄) d = 0, J_x g(x̄) d ∈ aff(C(A; S^p_+))}`, `A = g(x̄) + Γ`. -/
def app (xbar : X) (_ζ : EuclideanSpace ℝ (Fin m)) (Γ : SymMat n) : Set X :=
  {d | fderiv ℝ P.h xbar d = 0 ∧
    fderiv ℝ P.g xbar d ∈ (affineSpan ℝ (psdCriticalCone (P.g xbar + Γ)) : Set (SymMat n))}

/-- `Ĉ(x̄) := ⋂_{(ζ, Γ) ∈ M(x̄)} app(ζ, Γ)` (p. 15). -/
def Chat (xbar : X) : Set X :=
  ⋂ μ ∈ P.multipliers xbar, P.app xbar μ.1 μ.2

/-- The strong second order sufficient condition (47), Definition 12, p. 15:
`sup_{(ζ,Γ) ∈ M(x̄)} {⟨d, J²_xx L(x̄, ζ, Γ) d⟩ - Υ_{g(x̄)}(Γ, J_x g(x̄) d)} > 0` for all
`d ∈ Ĉ(x̄) \ {0}` (a supremum is `> 0` iff some element is). -/
def SSOSC (xbar : X) : Prop :=
  ∀ d ∈ P.Chat xbar, d ≠ 0 → ∃ μ ∈ P.multipliers xbar,
    P.hessL xbar μ.1 μ.2 d - upsilon (P.g xbar) μ.2 (fderiv ℝ P.g xbar d) > 0

end Data

/-! ### The general form (OP) at `K = {0} × S^p_+` (p. 1, (11)), for Theorem 10 -/

/-- `Y = ℜ^m × S^p` with the sum of the inner products (11). -/
abbrev YSpace (m : ℕ) (n : Type) [Fintype n] [DecidableEq n] : Type :=
  WithLp 2 (EuclideanSpace ℝ (Fin m) × SymMat n)

/-- `K = {0} × S^p_+ ⊂ Y` (11). -/
def Kcone (m : ℕ) (n : Type) [Fintype n] [DecidableEq n] : Set (YSpace m n) :=
  {y | (WithLp.ofLp y).1 = 0 ∧ (WithLp.ofLp y).2 ∈ psdCone n}

namespace Data

variable (P : Data X m n)

/-- `G(x) = (h(x), g(x)) ∈ Y` (11). -/
def Gmap (x : X) : YSpace m n := WithLp.toLp 2 (P.h x, P.g x)

/-- `J_x G(x̄) d = (J_x h(x̄) d, J_x g(x̄) d) ∈ Y`. -/
def JG (xbar d : X) : YSpace m n :=
  WithLp.toLp 2 (fderiv ℝ P.h xbar d, fderiv ℝ P.g xbar d)

/-- The sigma term of (44)–(45), p. 14–15: `σ(μ, T²_K(G(x̄), J_x G(x̄) d))` for `μ = (ζ, Γ) ∈ Y`,
in `EReal`. -/
def sigmaTerm (xbar : X) (μ : EuclideanSpace ℝ (Fin m) × SymMat n) (d : X) : EReal :=
  supportFn (WithLp.toLp 2 μ : YSpace m n) (secondOrderTangentSet (Kcone m n) (P.Gmap xbar) (P.JG xbar d))

end Data


/-! ### The KKT map (51) and the generalized equation (52)–(53), pp. 16–17 -/

/-- `Z = X × ℜ^m × S^p` with the sum of the inner products. -/
abbrev KKTSpace (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] (m : ℕ) (n : Type)
    [Fintype n] [DecidableEq n] : Type _ :=
  WithLp 2 (X × WithLp 2 (EuclideanSpace ℝ (Fin m) × SymMat n))

/-- The point `(x, ζ, Γ) ∈ Z`. -/
def kktPt (x : X) (ζ : EuclideanSpace ℝ (Fin m)) (Γ : SymMat n) : KKTSpace X m n :=
  WithLp.toLp 2 (x, WithLp.toLp 2 (ζ, Γ))

/-- The `x`-component of `z ∈ Z`. -/
def zx (z : KKTSpace X m n) : X := (WithLp.ofLp z).1
/-- The `ζ`-component of `z ∈ Z`. -/
def zζ (z : KKTSpace X m n) : EuclideanSpace ℝ (Fin m) := (WithLp.ofLp (WithLp.ofLp z).2).1
/-- The `Γ`-component of `z ∈ Z`. -/
def zΓ (z : KKTSpace X m n) : SymMat n := (WithLp.ofLp (WithLp.ofLp z).2).2

variable [FiniteDimensional ℝ X]

/-- The KKT map `F` (51), p. 16:
`F(x, ζ, Γ) = (∇_x L(x, ζ, Γ), -h(x), -g(x) + Π_{S^p_+}(g(x) + Γ))`. -/
def kktMap (P : NLSDP X m n) (z : KKTSpace X m n) : KKTSpace X m n :=
  kktPt (gradient (fun y => P.lagrangian y (zζ z) (zΓ z)) (zx z)) (-P.h (zx z))
    (-P.g (zx z) + metricProj (psdCone n) (P.g (zx z) + zΓ z))

/-- The single-valued part `φ(x, ζ, Γ) = (∇_x L(x, ζ, Γ), -h(x), -g(x))` of the generalized
equation (52), p. 16. -/
def geMap (P : NLSDP X m n) (z : KKTSpace X m n) : KKTSpace X m n :=
  kktPt (gradient (fun y => P.lagrangian y (zζ z) (zΓ z)) (zx z)) (-P.h (zx z)) (-P.g (zx z))

/-- The closed convex set `D = X × ℜ^m × S^p_-` of (52), whose normal cone is
`N_X(x) × N_{ℜ^m}(ζ) × N_{S^p_-}(Γ)`. -/
def geSet (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] (m : ℕ) (n : Type)
    [Fintype n] [DecidableEq n] : Set (KKTSpace X m n) :=
  {z | zΓ z ∈ nsdCone n}

/-- Definition 14, p. 17: `z̄` is a solution of `0 ∈ φ(z) + N_D(z)` (53), and there are
neighbourhoods `B` of `0` and `V` of `z̄` such that for every `δ ∈ B` the linearized equation
`δ ∈ φ(z̄) + J_z φ(z̄)(z - z̄) + N_D(z)` has a unique solution `z_V(δ)` in `V`, and `z_V` is
Lipschitz continuous on `B`. -/
def StronglyRegular {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] (φ : Z → Z)
    (D : Set Z) (zbar : Z) : Prop :=
  -φ zbar ∈ normalCone D zbar ∧
  ∃ B ∈ 𝓝 (0 : Z), ∃ V ∈ 𝓝 zbar, ∃ s : Z → Z,
    (∀ δ ∈ B, s δ ∈ V ∧ δ - (φ zbar + fderiv ℝ φ zbar (s δ - zbar)) ∈ normalCone D (s δ) ∧
      ∀ z ∈ V, δ - (φ zbar + fderiv ℝ φ zbar (z - zbar)) ∈ normalCone D z → z = s δ) ∧
    ∃ L, LipschitzOnWith L s B

/-- Remark 15, p. 17: `Ξ` is a locally Lipschitz homeomorphism near `z̄` if there is an open
neighbourhood `V` of `z̄` such that `Ξ|_V : V → Ξ(V)` is Lipschitz continuous and bijective and its
inverse is Lipschitz continuous. -/
def LocLipHomeo {Z : Type*} [NormedAddCommGroup Z] (Ξ : Z → Z) (zbar : Z) : Prop :=
  ∃ V : Set Z, IsOpen V ∧ zbar ∈ V ∧ Set.InjOn Ξ V ∧ (∃ K, LipschitzOnWith K Ξ V) ∧
    ∃ ψ : Z → Z, Set.LeftInvOn ψ Ξ V ∧ ∃ K, LipschitzOnWith K ψ (Ξ '' V)

/-- A globally Lipschitz homeomorphism (Theorem 21 (h)): a bijection `Φ : Z → Z` with `Φ` and
`Φ⁻¹` Lipschitz continuous. -/
def GlobLipHomeo {Z : Type*} [NormedAddCommGroup Z] (Φ : Z → Z) : Prop :=
  ∃ ψ : Z → Z, Function.LeftInverse ψ Φ ∧ Function.RightInverse ψ Φ ∧
    (∃ K, LipschitzWith K Φ) ∧ ∃ K, LipschitzWith K ψ

/-- `Φ(δ) := F'(x̄, ζ̄, Γ̄; δ)`, the left-hand side of (67), p. 22 (one-sided directional derivative). -/
def kktDirDeriv (P : NLSDP X m n) (zbar : KKTSpace X m n) : KKTSpace X m n → KKTSpace X m n :=
  NonsmoothNewton.Local.dirDeriv (kktMap P) zbar

/-! ### Parameterizations, uniform growth, strong stability (§4, pp. 19–21) -/

/-- A `C²`-smooth parameterization (61), p. 20, of (NLSDP) by a parameter space `U`:
`f(x, u), h(x, u), g(x, u)` twice continuously differentiable with `f(·, ū) = f`, `G(·, ū) = G`. -/
structure C2Param (P : NLSDP X m n) (U : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U] where
  fu : X × U → ℝ
  hu : X × U → EuclideanSpace ℝ (Fin m)
  gu : X × U → SymMat n
  ubar : U
  fu_smooth : ContDiff ℝ 2 fu
  hu_smooth : ContDiff ℝ 2 hu
  gu_smooth : ContDiff ℝ 2 gu
  fu_base : ∀ x, fu (x, ubar) = P.f x
  hu_base : ∀ x, hu (x, ubar) = P.h x
  gu_base : ∀ x, gu (x, ubar) = P.g x

/-- The perturbed problem (OP_u) (61). -/
def C2Param.prob {P : NLSDP X m n} {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (Q : C2Param P U) (u : U) : Data X m n :=
  ⟨fun x => Q.fu (x, u), fun x => Q.hu (x, u), fun x => Q.gu (x, u)⟩

/-- The canonical parameterization (p. 20): `U = X × Y`, `ū = 0`,
`(f(x) - ⟨u₁, x⟩, G(x) + u₂)`. -/
def canonicalParam (P : NLSDP X m n) :
    C2Param P (X × (EuclideanSpace ℝ (Fin m) × SymMat n)) where
  fu := fun p => P.f p.1 - ⟪p.2.1, p.1⟫
  hu := fun p => P.h p.1 + p.2.2.1
  gu := fun p => P.g p.1 + p.2.2.2
  ubar := 0
  fu_smooth := (P.f_smooth.comp contDiff_fst).sub
    ((contDiff_fst.comp contDiff_snd).inner ℝ contDiff_fst)
  hu_smooth := (P.h_smooth.comp contDiff_fst).add
    (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))
  gu_smooth := (P.g_smooth.comp contDiff_fst).add
    (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
  fu_base := by intro x; simp
  hu_base := by intro x; simp
  gu_base := by intro x; simp

/-- Definition 17 (62), p. 20, with respect to one parameterization `Q`: there are `c > 0` and
neighbourhoods `V_X` of `x̄`, `V_U` of `ū` such that for every `u ∈ V_U` and every stationary point
`x(u) ∈ V_X` of (OP_u), `f(x, u) ≥ f(x(u), u) + c‖x - x(u)‖²` for all `x ∈ V_X` feasible for (OP_u). -/
def UniformGrowthWrt {P : NLSDP X m n} {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (Q : C2Param P U) (xbar : X) : Prop :=
  ∃ c > (0 : ℝ), ∃ VX ∈ 𝓝 xbar, ∃ VU ∈ 𝓝 Q.ubar, ∀ u ∈ VU, ∀ xu ∈ VX,
    (Q.prob u).stationary xu → ∀ x ∈ VX, (Q.prob u).feasible x →
      Q.fu (x, u) ≥ Q.fu (xu, u) + c * ‖x - xu‖ ^ 2

/-- Definition 17, p. 20: (62) holds for every `C²`-smooth parameterization by a Banach space
(in the universe of `X`). -/
def UniformGrowth {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (P : NLSDP X m n) (xbar : X) : Prop :=
  ∀ (U : Type u) [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U] (Q : C2Param P U),
    UniformGrowthWrt Q xbar

/-- Definition 19, p. 21, with respect to one parameterization `Q`: there are neighbourhoods `V_X`
of `x̄` and `V_U` of `ū` such that for every `u ∈ V_U`, (OP_u) has a unique stationary point
`x(u) ∈ V_X`, and `x(·)` is continuous on `V_U`. -/
def StronglyStableWrt {P : NLSDP X m n} {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (Q : C2Param P U) (xbar : X) : Prop :=
  ∃ VX ∈ 𝓝 xbar, ∃ VU ∈ 𝓝 Q.ubar, ∃ xu : U → X,
    (∀ u ∈ VU, xu u ∈ VX ∧ (Q.prob u).stationary (xu u) ∧
      ∀ y ∈ VX, (Q.prob u).stationary y → y = xu u) ∧
    ContinuousOn xu VU

/-- Definition 19, p. 21: `x̄` is strongly stable with respect to every `C²`-smooth
parameterization by a Banach space (in the universe of `X`). -/
def StronglyStable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (P : NLSDP X m n) (xbar : X) : Prop :=
  ∀ (U : Type u) [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U] (Q : C2Param P U),
    StronglyStableWrt Q xbar

end

end SunNLSDP.Equiv


