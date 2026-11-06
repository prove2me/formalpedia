-- Prove2me | Definitions.Def_ZOGlobalLB_Fnew
-- name    : ZOGlobalLB_Fnew
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:47:17.070816+00:00
-- url     : https://prove2.me/theorems/b9c312d7-0cb4-400a-ad68-a1402297fc0d
-- title:
--   The normalized hard objective $F_{\mathrm{new}}$
-- statement:
--   Fix orthonormal frames $U=(u_1,\dots,u_T)$ in $\mathbb R^r$ and $V=(v_1,\dots,v_T)$ in $\mathbb R^m$. For $z\in\mathbb R^r$ put $R=64\sqrt T$, $\alpha=(1+\|z\|^2/R^2)^{-1/2}$, $y=\alpha z$, $w=U^\top y$, and $P(z)=\frac{R^2}{5}(\alpha^{-1}-1)$. The base objective is $F_{\mathrm{base}}(z)=P(z)+B_T(w)$. With the moving center $a(w)=A\sum_i g_i(w)v_i$ and the past centers $a_{<i}(w)=A\sum_{j<i}g_j(w)v_j$,
--   $$F_{\mathrm{new}}(z,x)=P(z)+B_T(w)+h(x-a(w))-\sum_{i=1}^T\bigl[1-\chi(x-a_{<i}(w))\bigr]c_i(w).$$
--   Also $e_*=1/4805$ and $H_*=66243245/8$.
--
--   This is the normalized hard function whose stationary points certify that every hidden stage has been completed.
--
--   **Formalization Note.** Pairs $(z,x)$ live in the Euclidean product $\mathbb R^r\times\mathbb R^m$ (`WithLp 2`), so gradients and Hessians of $F_{\mathrm{new}}$ are for the Euclidean norm on pairs.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, (17), (18), (22), (24), pp.10–12; Appendix B, p.36; Lemma B.3, p.40

import Mathlib
import Definitions.Def_ZOGlobalLB_Profiles

open scoped RealInnerProductSpace

namespace ZOGlobalLB

/-! # The normalized hard objective `F_new`

Xia, Yuan, arXiv:2610.19652, Section 3.1, (17), (18), (22), (24), pp.10–12, Appendix B, p.36,
and Lemma B.3, p.40.

The chain coordinates are `z ∈ ℝʳ`, the workspace coordinates `x ∈ ℝᵐ`; the hidden frames are
`U = (u₁, …, u_T)` in `ℝʳ` and `V = (v₁, …, v_T)` in `ℝᵐ`, given as parameters.

**Formalization Note.** Frames are maps `Fin T → E r`; theorems assume `Orthonormal ℝ U`. A pair
`(z, x)` lives in `WithLp 2 (E r × E m)`, the product with the Euclidean norm
`‖(z, x)‖² = ‖z‖² + ‖x‖²` (the plain product `E r × E m` carries the sup norm instead).
Stage indices are 0-based (`Fin T`). -/

/-- `R = 64 √T` (17), p.10. -/
noncomputable def Rc (T : ℕ) : ℝ := 64 * Real.sqrt T

/-- `α = (1 + ‖z‖²/R²)^{-1/2}` (17), p.10. -/
noncomputable def alphaC {r : ℕ} (T : ℕ) (z : E r) : ℝ :=
  (Real.sqrt (1 + ‖z‖ ^ 2 / Rc T ^ 2))⁻¹

/-- The bounded chain input `y = α z` (17), p.10. -/
noncomputable def ycoord {r : ℕ} (T : ℕ) (z : E r) : E r := alphaC T z • z

/-- The hidden chain coordinates `w = Uᵀ y`, `w_i = ⟨u_i, y⟩` (17), p.10. -/
noncomputable def wcoord {r T : ℕ} (U : Fin T → E r) (z : E r) : E T :=
  WithLp.toLp 2 (fun i => ⟪U i, ycoord T z⟫)

/-- The radial confinement `P(z) = (R²/5)(α⁻¹ - 1)` (18), p.10. -/
noncomputable def Pconf {r : ℕ} (T : ℕ) (z : E r) : ℝ :=
  Rc T ^ 2 / 5 * ((alphaC T z)⁻¹ - 1)

/-- The base objective `F_base(z) = P(z) + B_T(Uᵀ y(z))` (18), p.10. -/
noncomputable def Fbase {r T : ℕ} (U : Fin T → E r) (z : E r) : ℝ :=
  Pconf T z + chainBT (wcoord U z)

/-- The moving center `a(w) = A Σ_i g_i(w) v_i` (22), p.11. -/
noncomputable def aCenter {m T : ℕ} (V : Fin T → E m) (w : E T) : E m :=
  Acst • ∑ i, gAct w i • V i

/-- The past center `a_{<i}(w) = A Σ_{j<i} g_j(w) v_j` (22), p.11. -/
noncomputable def aBefore {m T : ℕ} (V : Fin T → E m) (w : E T) (i : Fin T) : E m :=
  Acst • ∑ j ∈ Finset.univ.filter (fun j => j < i), gAct w j • V j

/-- **The normalized hard objective** (24), p.12, in separate variables:
`F_new(z, x) = P(z) + B_T(w) + h(x - a(w)) - Σ_i [1 - χ(x - a_{<i}(w))] c_i(w)`, `w = Uᵀ y(z)`. -/
noncomputable def FnewZX {r m T : ℕ} (U : Fin T → E r) (V : Fin T → E m) (z : E r) (x : E m) :
    ℝ :=
  Pconf T z + chainBT (wcoord U z) + wellH (x - aCenter V (wcoord U z)) -
    ∑ i, (1 - chiC (x - aBefore V (wcoord U z) i)) * cCorr (wcoord U z) i

/-- **`F_new` on the Euclidean product** `ℝʳ × ℝᵐ` (24), p.12: `Fnew U V (z, x) = FnewZX U V z x`.
Gradients and Hessians of `Fnew` are taken for the Euclidean norm on pairs. -/
noncomputable def Fnew {r m T : ℕ} (U : Fin T → E r) (V : Fin T → E m)
    (p : WithLp 2 (E r × E m)) : ℝ :=
  FnewZX U V p.ofLp.1 p.ofLp.2

/-- The stationarity threshold `e* = 1/(5J) = 1/4805`, `J = 961` (Lemma B.3, p.40). -/
noncomputable def eStar : ℝ := 1 / 4805

/-- The Hessian bound `H* = 66243245/8` (Lemma B.3, p.40, and (83), p.44). -/
noncomputable def Hstar : ℝ := 66243245 / 8

end ZOGlobalLB


