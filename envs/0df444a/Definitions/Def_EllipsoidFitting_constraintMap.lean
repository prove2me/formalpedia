-- Prove2me | Definitions.Def_EllipsoidFitting_constraintMap
-- name    : EllipsoidFitting_constraintMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:15.080219+00:00
-- url     : https://prove2.me/theorems/bfabec66-b82f-4518-962e-9a9691740b0c
-- title:
--   The constraint map $L$, its adjoint $L^*$, the Gram matrix $M=LL^*$, the span $S$ and $\gamma=2m/d^2$
-- statement:
--   Fix points $v_1,\dots,v_m\in\mathbb R^d$.
--
--   1. $L:\mathbb R^{d\times d}\to\mathbb R^m$, $L(X)=(v_t^\top Xv_t)_{t\in[m]}$, evaluates the constraint values.
--   2. $L^*:\mathbb R^m\to\mathbb R^{d\times d}$, $L^*(w)=\sum_{t\in[m]}w[t]\,v_tv_t^\top$, lifts coefficient vectors to combinations of the rank-one forms.
--   3. $M=LL^*\in\mathbb R^{m\times m}$ is the Gram matrix of the rank-one forms, $M[i,j]=\langle v_i,v_j\rangle^2$.
--   4. $S=\operatorname{Im}(L^*)=\operatorname{span}\{v_iv_i^\top:i\in[m]\}$.
--   5. $\gamma=2m/d^2$.
--
--   These are the paper's standing notation; every construction of the mission is built from them.
--
--   **Formalization Note** $M$ is written by its entries $(v_i\cdot v_j)^2$; that it is the matrix of $w\mapsto L(L^*(w))$ is proved in the mission's sanity file. At $d=0$, $\gamma$ is the junk value $0$.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Notation 2–4, p.5 (PDF p.7); γ = 2m/d², p.18

import Mathlib

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **The constraint map `L`, its adjoint `L*`, the Gram matrix `M = LL*`, the span `S` and the
ratio `γ`.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for Ellipsoid Fitting*,
arXiv:2608.12415 (version of Nov 3, 2026), Notation 2–4, p.5: "L(X) := (v⊤_t X v_t)_{t∈[m]},
L∗(w) := ∑_{t∈[m]} w[t] v_t v⊤_t , M := LL∗"; "S := Im(L∗) = span{v_i v⊤_i : i ∈ [m]}";
"γ = 2m/d²".

`constraintMap v X` is `L(X) = (v_tᵀ X v_t)_t ∈ ℝ^m`. -/
def constraintMap {m d : ℕ} (v : Fin m → Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Fin m → ℝ :=
  fun t => v t ⬝ᵥ (X *ᵥ v t)

/-- `liftMap v w` is `L*(w) = ∑_t w[t] v_t v_tᵀ`. -/
def liftMap {m d : ℕ} (v : Fin m → Fin d → ℝ) (w : Fin m → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ t, w t • vecMulVec (v t) (v t)

/-- `gram v` is the Gram matrix `M = LL*` of the rank-one forms `v_t v_tᵀ` under the trace inner
product: `M[i, j] = ⟨v_i v_iᵀ, v_j v_jᵀ⟩ = ⟨v_i, v_j⟩²`.

**Formalization Note** `M` is written by its entries `(v_i ⬝ v_j)²`; that this is the matrix of
`w ↦ L(L*(w))` is checked (proved) in the mission's sanity file. -/
def gram {m d : ℕ} (v : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => (v i ⬝ᵥ v j) ^ 2

/-- `imageS v` is `S = Im(L*) = span{v_i v_iᵀ : i ∈ [m]}`, a subspace of the `d × d` matrices. -/
def imageS {m d : ℕ} (v : Fin m → Fin d → ℝ) : Submodule ℝ (Matrix (Fin d) (Fin d) ℝ) :=
  Submodule.span ℝ (Set.range fun t => vecMulVec (v t) (v t))

/-- `gammaRatio d m` is the aspect ratio `γ = 2m/d²` (the paper writes "γ = 2m/d²", p.5, p.18).
At `d = 0` it is Lean's junk value `0`. -/
noncomputable def gammaRatio (d m : ℕ) : ℝ :=
  2 * (m : ℝ) / (d : ℝ) ^ 2

end EllipsoidFitting


