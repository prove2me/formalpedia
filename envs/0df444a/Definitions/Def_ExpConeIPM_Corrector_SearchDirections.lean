-- Prove2me | Definitions.Def_ExpConeIPM_Corrector_SearchDirections
-- name    : ExpConeIPM_Corrector_SearchDirections
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:36.866278+00:00
-- url     : https://prove2.me/theorems/68f3aa4b-ae12-4257-a378-9073620fa960
-- title:
--   Shadow iterates (7), the double secant scaling (8), and the search directions (11), (16), (17), (18)
-- statement:
--   This file defines the primal-dual scaling and the search directions of Dahl and Andersen's algorithm, on the augmented space $\mathbb R^{N}$ of the homogeneous model ($N=n+1$).
--
--   Let $K$ be a cone with barrier $F$ and conjugate barrier $F_*(s)=\sup_{x\in\operatorname{int}K}\{-\langle s,x\rangle-F(x)\}$. At an iterate $(x,s)$ the **shadow iterates** (7) are
--   $$\tilde x:=-F_*'(s),\qquad \tilde s:=-F'(x).$$
--   A nonsingular linear map $W$ of $\mathbb R^N$ is a **double secant scaling** (8) if
--   $$v:=Wx=W^{-T}s,\qquad \tilde v:=W\tilde x=W^{-T}\tilde s,$$
--   where $W^{-T}$ is the transpose (adjoint) of $W^{-1}$.
--
--   With $G$ the residual of the homogeneous model and $z=(x,s,y)$ the iterate:
--
--   1. $\Delta z^{a}$ is an **affine direction** if it solves (11): $G(\Delta z^{a})=-G(z)$ and $W\Delta x^{a}+W^{-T}\Delta s^{a}=-v$.
--   2. The **corrector term** (16) is $\eta:=-\tfrac12F'''(x)[\Delta x^{a},(F''(x))^{-1}\Delta s^{a}]$.
--   3. $\Delta z^{c}$ is a **pure corrector direction** if it solves (17): $G(\Delta z^{c})=0$ and $W\Delta x^{c}+W^{-T}\Delta s^{c}=-W^{-T}\eta$.
--   4. For a centering parameter $\gamma$, $\Delta z$ is a **combined direction** if it solves (18):
--   $$G(\Delta z)=-(1-\gamma)G(z),\qquad W\Delta x+W^{-T}\Delta s=-v+\gamma\mu\tilde v-W^{-T}\eta,$$
--   with $\mu=\langle x,s\rangle/\vartheta$ and, in the homogeneous model, $K=\hat K\times\mathbb R_+$, $F=\hat F-\log\tau$, $\vartheta=\hat\vartheta+1$.
--
--   The combined direction (18) with the corrector (16) is the paper's main algorithmic contribution; Lemmas 2–4 state its properties.
--
--   **Formalization Note** $W$ is a continuous linear equivalence of `EuclideanSpace ℝ (Fin N)` and $W^{-T}$ is `ContinuousLinearMap.adjoint` of $W^{-1}$ (`invT`). The paper's $W$ is block diagonal, $W=\operatorname{diag}(W_1,\dots,W_{k+1})$ with $W_{k+1}=\sqrt{\kappa/\tau}$; the block form is not assumed here, so the paper's scaling is a special case. $F'$ is `gradient`, $F''(x)$ is the published `hess F x`, and $F'''(x)[u,w]$ is `fderiv ℝ (hess F) x u w`. $(F''(x))^{-1}$ is `ContinuousLinearMap.inverse`, which is the true inverse whenever $F''(x)$ is invertible (it is positive definite at interior points of the cone for the barriers considered). Each direction is a predicate ("$\Delta z$ solves the system"), so the lemmas quantify over every solution. In the combined system, $\tilde v$ is written $W\tilde x$; it equals $W^{-T}\tilde s$ under (8).
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), pp. 349–352, (7), (8), (11), (16), (17), (18)

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel

open scoped InnerProductSpace

namespace ExpConeIPM.Corrector

/-! # Scaling (8) and the search directions (11), (16), (17), (18) of Dahl–Andersen
(Math. Program. 194 (2022), pp. 349–352), on the augmented space `ℝᴺ` (`N = n + 1`). -/

/-- `W^{−T}`: the adjoint of `W⁻¹` for the Euclidean inner product, for a nonsingular linear map
`W` of `ℝᴺ` (p. 350). -/
noncomputable def invT {N : ℕ} (W : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ContinuousLinearMap.adjoint (W.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))

/-- The primal shadow iterate (7), `x̃ := −F'_*(s)`, with `F_*` the conjugate barrier (1) of `F`
for the cone `K`. -/
noncomputable def shadowX {N : ℕ} (K : Set (EuclideanSpace ℝ (Fin N)))
    (F : EuclideanSpace ℝ (Fin N) → ℝ) (s : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  -gradient (SelfScaledIPM.ShortStep.conj K F) s

/-- The dual shadow iterate (7), `s̃ := −F'(x)`. -/
noncomputable def shadowS {N : ℕ} (F : EuclideanSpace ℝ (Fin N) → ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  -gradient F x

/-- The double secant equations (8) (p. 350): the nonsingular scaling `W` satisfies
`v := W x = W^{−T} s` and `ṽ := W x̃ = W^{−T} s̃`, with `x̃, s̃` the shadow iterates (7) of the barrier
`F` of the cone `K`. -/
def IsDoubleSecantScaling {N : ℕ} (K : Set (EuclideanSpace ℝ (Fin N)))
    (F : EuclideanSpace ℝ (Fin N) → ℝ) (x s : EuclideanSpace ℝ (Fin N))
    (W : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) : Prop :=
  W x = invT W s ∧ W (shadowX K F s) = invT W (shadowS F x)

/-- `Δzᵃ = (Δxᵃ, Δsᵃ, Δyᵃ)` solves the affine system (11) (p. 351) at the iterate `z = (x, s, y)`:
`G(Δzᵃ) = −G(z)` and `W Δxᵃ + W^{−T} Δsᵃ = −v`, `v = W x`. -/
def IsAffineDirection {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (W : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (dxa dsa : EuclideanSpace ℝ (Fin (n + 1))) (dya : EuclideanSpace ℝ (Fin m)) : Prop :=
  residual A b c dxa dsa dya = -residual A b c x s y ∧
    W dxa + invT W dsa = -W x

/-- The corrector term (16) (p. 352): `η := −½ F'''(x)[Δxᵃ, (F''(x))⁻¹ Δsᵃ]`. Here
`F''(x) = hess F x`, `F'''(x)[u] = fderiv ℝ (hess F) x u` (a linear map, whose value at `w` is
`F'''(x)[u, w]`), and `(F''(x))⁻¹` is `ContinuousLinearMap.inverse` (the true inverse whenever
`F''(x)` is invertible, e.g. positive definite). -/
noncomputable def corrector {N : ℕ} (F : EuclideanSpace ℝ (Fin N) → ℝ)
    (x dxa dsa : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  -(1 / 2 : ℝ) •
    (fderiv ℝ (SelfScaledIPM.ShortStep.hess F) x dxa)
      ((SelfScaledIPM.ShortStep.hess F x).inverse dsa)

/-- `Δzᶜ = (Δxᶜ, Δsᶜ, Δyᶜ)` solves the pure corrector system (17) (p. 352) for the corrector `η`:
`G(Δzᶜ) = 0` and `W Δxᶜ + W^{−T} Δsᶜ = −W^{−T} η`. -/
def IsPureCorrectorDirection {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (η : EuclideanSpace ℝ (Fin (n + 1)))
    (dxc dsc : EuclideanSpace ℝ (Fin (n + 1))) (dyc : EuclideanSpace ℝ (Fin m)) : Prop :=
  residual A b c dxc dsc dyc = 0 ∧ W dxc + invT W dsc = -invT W η

/-- `Δz = (Δx, Δs, Δy)` solves the combined system (18) (p. 352) for the centering parameter `γ`
and the corrector `η`, at the iterate `z = (x, s, y)` of the homogeneous model with cone
`K = K̂ × ℝ₊`, barrier `F = F̂ − log τ` and `ϑ = ϑ̂ + 1`:
`G(Δz) = −(1 − γ) G(z)` and `W Δx + W^{−T} Δs = −v + γ μ ṽ − W^{−T} η`, where `v = W x`,
`ṽ = W x̃` (`x̃` the primal shadow iterate (7)) and `μ = ⟨x, s⟩ / ϑ`. -/
def IsCombinedDirection {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (Khat : Set (EuclideanSpace ℝ (Fin n))) (Fhat : EuclideanSpace ℝ (Fin n) → ℝ) (ϑhat : ℝ)
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (W : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (η : EuclideanSpace ℝ (Fin (n + 1))) (γ : ℝ)
    (dx ds : EuclideanSpace ℝ (Fin (n + 1))) (dy : EuclideanSpace ℝ (Fin m)) : Prop :=
  residual A b c dx ds dy = (-(1 - γ)) • residual A b c x s y ∧
    W dx + invT W ds =
      -W x + (γ * mu ϑhat x s) • W (shadowX (augCone Khat) (augBarrier Fhat) s) - invT W η

end ExpConeIPM.Corrector


