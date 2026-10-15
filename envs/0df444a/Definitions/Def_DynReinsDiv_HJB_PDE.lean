-- Prove2me | Definitions.Def_DynReinsDiv_HJB_PDE
-- name    : DynReinsDiv_HJB_PDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:30.345619+00:00
-- url     : https://prove2.me/theorems/df4d46fe-4d93-422c-906d-61f695616683
-- title:
--   The variational inequality (3.1), the regularity class C^{2,1}, properties (3.4)–(3.9), the penalty data and the penalized problem (A.17)
-- statement:
--   This file states what it means to solve the two boundary-value problems of the paper.
--
--   **Regularity class.** Write $\mathcal Q_T=(0,\infty)\times(0,T]$ and $\overline{\mathcal Q}_T=[0,\infty)\times[0,T]$. A function $v(x,t)$ with partial derivatives $v_x, v_{xx}, v_t$ belongs to $C^{2,1}(\overline{\mathcal Q}_T\setminus\{(0,0)\})\cap C(\overline{\mathcal Q}_T)$ when $v$ is continuous on $\overline{\mathcal Q}_T$, the functions $v_x, v_{xx}, v_t$ are continuous on $\overline{\mathcal Q}_T\setminus\{(0,0)\}$, and they are the partial derivatives $\partial_x v$, $\partial_x v_x$, $\partial_t v$ at every interior point $x>0$, $0<t<T$. Values of the derivatives on the boundary are their continuous extensions.
--
--   **The variational inequality (3.1).** $v$ solves (3.1) if
--   $$\min\{v_t-\mathcal Lv,\ v_x-1\}=0\ \text{ in }\mathcal Q_T,\qquad v(0,t)=0\ (0<t\le T),\qquad v(x,0)=x\ (x>0).$$
--   Here $t$ is time to maturity: (3.1) is the time-reversed HJB equation of the control problem.
--
--   **Properties (3.4)–(3.9)**, on $\mathcal Q_T$: $v_x\ge1$, $v_t\ge0$, $v_{xx}\le0$; $v_{xxx}\ge0$ in the weak sense, read as: $x\mapsto v_{xx}(x,t)$ is nondecreasing on $(0,\infty)$ for each $t\in(0,T]$; $v_{xt}\ge0$, read as: $t\mapsto v_x(x,t)$ is nondecreasing on $(0,T]$ for each $x>0$; and $\lambda v_x+v_{xx}\ge0$ for every positive root $\lambda$ of $f$.
--
--   **Penalty data** at a fixed $\varepsilon>0$ (pp. 24–25). A penalty function $\beta_\varepsilon\in C^2(\mathbb R)$ with $\beta_\varepsilon(0)=-c$, $\beta_\varepsilon(x)=0$ for $x\ge\varepsilon$, $\beta_\varepsilon\le0$, $\beta_\varepsilon'\ge0$, $\beta_\varepsilon''\le0$. A boundary datum $f_\varepsilon\in C^2([0,\infty))$ with $f_\varepsilon(0)=\lambda$, non-increasing, and $f_\varepsilon(t)=0$ for $t\ge\varepsilon$.
--
--   **The penalized problem (A.17).** On $\mathcal Q_{L,T}=(0,L)\times(0,T]$, $u$ solves
--   $$u_t-\mathcal Tu+\beta_\varepsilon(u-1)=0\ \text{ in }\mathcal Q_{L,T},\quad (\lambda u+u_x)(0,t)=f_\varepsilon(t),\quad u(L,t)=1\ (0<t\le T),\quad u(x,0)=1\ (0<x<L),$$
--   and $u\ne0$ in $\mathcal Q_{L,T}$ so that $\mathcal Tu$ is defined. Two regularity classes on the rectangle are used: $C^{2,1}(\mathcal Q_{L,T})\cap C(\overline{\mathcal Q}_{L,T})$ (Lemma A.2), where $u_x$ is in addition continuous up to $x=0$ so that the Robin condition makes sense, and $C^{2,1}(\overline{\mathcal Q}_{L,T})$ (Lemma A.3), where $u, u_x, u_{xx}, u_t$ are continuous on $[0,L]\times[0,T]$.
--
--   **Formalization Note** Functions of $(x,t)$ are `ℝ → ℝ → ℝ`; the partial derivatives are explicit functions tied to $v$ by `HasDerivAt` on sections at interior points, never `deriv` at a boundary point. The limit $\lim_{\varepsilon\to0+}\beta_\varepsilon$ on p. 24 concerns the family and is used only in the passage to the limit; it is not part of the penalty data at one $\varepsilon$. "Decreasing" for $f_\varepsilon$ is read as non-increasing.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 8 (3.1), p. 9 (Theorem 3.1: class and (3.4)–(3.9)), pp. 24–25 (β_ε, f_ε, (A.17)), p. 26 (classes of Lemmas A.2, A.3)

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model

namespace DynReinsDiv.HJB

/-- The closed domain `𝒬̄_T = [0, ∞) × [0, T]`. -/
def QTbar (T : ℝ) : Set (ℝ × ℝ) := Set.Ici 0 ×ˢ Set.Icc 0 T

/-- `v ∈ C^{2,1}(𝒬̄_T ∖ {(0,0)}) ∩ C(𝒬̄_T)` with partial derivatives `vx, vxx, vt`:
`v` is continuous on `𝒬̄_T`; `vx, vxx, vt` are continuous on `𝒬̄_T ∖ {(0,0)}` and are the
partial derivatives `∂ₓv`, `∂ₓ(vx)`, `∂ₜv` at every interior point `x > 0`, `0 < t < T`.
Boundary values of the derivatives are their continuous extensions. -/
structure IsC21 (T : ℝ) (v vx vxx vt : ℝ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (Function.uncurry v) (QTbar T)
  cont_vx : ContinuousOn (Function.uncurry vx) (QTbar T \ {(0, 0)})
  cont_vxx : ContinuousOn (Function.uncurry vxx) (QTbar T \ {(0, 0)})
  cont_vt : ContinuousOn (Function.uncurry vt) (QTbar T \ {(0, 0)})
  deriv_x : ∀ x t : ℝ, 0 < x → 0 < t → t < T → HasDerivAt (fun y => v y t) (vx x t) x
  deriv_xx : ∀ x t : ℝ, 0 < x → 0 < t → t < T → HasDerivAt (fun y => vx y t) (vxx x t) x
  deriv_t : ∀ x t : ℝ, 0 < x → 0 < t → t < T → HasDerivAt (fun s => v x s) (vt x t) t

/-- `v` (with partial derivatives `vx, vxx, vt`) solves the variational inequality (3.1):
`min{v_t - 𝓛v, v_x - 1} = 0` in `𝒬_T = (0, ∞) × (0, T]`, `v(0, t) = 0` for `0 < t ≤ T`,
`v(x, 0) = x` for `x > 0`. -/
structure SolvesVI (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ) : Prop where
  vi : ∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T →
    min (vt x t - M.Lop (vxx x t) (vx x t) (v x t)) (vx x t - 1) = 0
  left_bc : ∀ t : ℝ, 0 < t → t ≤ M.T → v 0 t = 0
  initial : ∀ x : ℝ, 0 < x → v x 0 = x

/-- The properties (3.4)–(3.9) of Theorem 3.1 on `𝒬_T = (0, ∞) × (0, T]`.
(3.7) `v_xxx ≥ 0` in the weak sense: `x ↦ v_xx(x, t)` is nondecreasing; (3.8) `v_xt ≥ 0`:
`t ↦ v_x(x, t)` is nondecreasing; (3.9) for every positive root `λ` of `f` (A.12). -/
structure HJBProps (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ) : Prop where
  vx_ge_one : ∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T → 1 ≤ vx x t
  vt_nonneg : ∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T → 0 ≤ vt x t
  vxx_nonpos : ∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T → vxx x t ≤ 0
  vxxx_weak : ∀ t : ℝ, 0 < t → t ≤ M.T → MonotoneOn (fun x => vxx x t) (Set.Ioi 0)
  vxt : ∀ x : ℝ, 0 < x → MonotoneOn (fun t => vx x t) (Set.Ioc 0 M.T)
  lam_vx_add_vxx : ∀ lam : ℝ, 0 < lam → M.fA lam = 0 →
    ∀ x t : ℝ, 0 < x → 0 < t → t ≤ M.T → 0 ≤ lam * vx x t + vxx x t

/-- A penalty function `β_ε` (p. 24) at one fixed `ε`: `C²` on `ℝ`, `β_ε(0) = -c`,
`β_ε(x) = 0` for `x ≥ ε`, `β_ε ≤ 0`, `β_ε' ≥ 0`, `β_ε'' ≤ 0`. -/
structure IsPenalty (M : Model) (ε : ℝ) (β : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 2 β
  at_zero : β 0 = -M.c
  vanish : ∀ x : ℝ, ε ≤ x → β x = 0
  nonpos : ∀ x : ℝ, β x ≤ 0
  deriv_nonneg : ∀ x : ℝ, 0 ≤ deriv β x
  deriv2_nonpos : ∀ x : ℝ, deriv (deriv β) x ≤ 0

/-- The boundary datum `f_ε` (p. 25): `C²` on `[0, ∞)`, `f_ε(0) = λ`, non-increasing on
`[0, ∞)`, `f_ε(t) = 0` for `t ≥ ε`. -/
structure IsRamp (ε lam : ℝ) (fε : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 2 fε (Set.Ici 0)
  at_zero : fε 0 = lam
  antitone : AntitoneOn fε (Set.Ici 0)
  vanish : ∀ t : ℝ, ε ≤ t → fε t = 0

/-- `u ∈ C^{2,1}(𝒬_{L,T}) ∩ C(𝒬̄_{L,T})` with `𝒬_{L,T} = (0, L) × (0, T]` (Lemma A.2), with
partial derivatives `ux, uxx, ut`; `ux` is in addition continuous up to `x = 0`
(on `[0, L) × (0, T]`), so that the Robin condition at `x = 0` is meaningful. -/
structure IsC21Rect (L T : ℝ) (u ux uxx ut : ℝ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (Function.uncurry u) (Set.Icc 0 L ×ˢ Set.Icc 0 T)
  cont_ux : ContinuousOn (Function.uncurry ux) (Set.Ico 0 L ×ˢ Set.Ioc 0 T)
  cont_uxx : ContinuousOn (Function.uncurry uxx) (Set.Ioo 0 L ×ˢ Set.Ioc 0 T)
  cont_ut : ContinuousOn (Function.uncurry ut) (Set.Ioo 0 L ×ˢ Set.Ioc 0 T)
  deriv_x : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t < T → HasDerivAt (fun y => u y t) (ux x t) x
  deriv_xx : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t < T → HasDerivAt (fun y => ux y t) (uxx x t) x
  deriv_t : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t < T → HasDerivAt (fun s => u x s) (ut x t) t

/-- `u ∈ C^{2,1}(𝒬̄_{L,T})` (Lemma A.3): `u, ux, uxx, ut` continuous on `[0, L] × [0, T]`,
partial derivatives at the interior points. -/
structure IsC21RectClosed (L T : ℝ) (u ux uxx ut : ℝ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (Function.uncurry u) (Set.Icc 0 L ×ˢ Set.Icc 0 T)
  cont_ux : ContinuousOn (Function.uncurry ux) (Set.Icc 0 L ×ˢ Set.Icc 0 T)
  cont_uxx : ContinuousOn (Function.uncurry uxx) (Set.Icc 0 L ×ˢ Set.Icc 0 T)
  cont_ut : ContinuousOn (Function.uncurry ut) (Set.Icc 0 L ×ˢ Set.Icc 0 T)
  deriv_x : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t < T → HasDerivAt (fun y => u y t) (ux x t) x
  deriv_xx : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t < T → HasDerivAt (fun y => ux y t) (uxx x t) x
  deriv_t : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t < T → HasDerivAt (fun s => u x s) (ut x t) t

/-- `u` (with partial derivatives `ux, uxx, ut`) solves the penalized problem (A.17) on
`𝒬_{L,T} = (0, L) × (0, T]` with penalty `β = β_ε`, boundary datum `fε = f_ε` and root `lam = λ`:
`u_t - 𝒯u + β_ε(u - 1) = 0` in `𝒬_{L,T}`, `(λu + u_x)(0, t) = f_ε(t)`, `u(L, t) = 1`
(`0 < t ≤ T`), `u(x, 0) = 1` (`0 < x < L`). Since `𝒯u` divides by `u`, a solution is
required to be nonzero on `𝒬_{L,T}`. -/
structure SolvesPenalized (M : Model) (L lam : ℝ) (β fε : ℝ → ℝ) (u ux uxx ut : ℝ → ℝ → ℝ) :
    Prop where
  ne_zero : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → u x t ≠ 0
  eqn : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T →
    ut x t - M.Top (uxx x t) (ux x t) (u x t) + β (u x t - 1) = 0
  robin : ∀ t : ℝ, 0 < t → t ≤ M.T → lam * u 0 t + ux 0 t = fε t
  right_bc : ∀ t : ℝ, 0 < t → t ≤ M.T → u L t = 1
  initial : ∀ x : ℝ, 0 < x → x < L → u x 0 = 1

end DynReinsDiv.HJB


