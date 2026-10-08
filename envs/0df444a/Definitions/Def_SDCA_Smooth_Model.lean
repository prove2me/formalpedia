-- Prove2me | Definitions.Def_SDCA_Smooth_Model
-- name    : SDCA_Smooth_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:55.739958+00:00
-- url     : https://prove2.me/theorems/62e41389-8239-4736-831c-dbd620f2bbdb
-- title:
--   Primal (1), dual (2), $w(\alpha)$ (3) and the run of Procedure SDCA
-- statement:
--   Fix $d,n\in\mathbb N$, vectors $x_1,\dots,x_n\in\mathbb R^d$ (Euclidean norm), scalar losses $\varphi_1,\dots,\varphi_n:\mathbb R\to\mathbb R$ and a regularization parameter $\lambda$. This file defines the objects of regularized loss minimization and of Procedure SDCA.
--
--   1. **Primal vector of a dual point** (eq. (3)): for $\alpha\in\mathbb R^n$, $\;w(\alpha)=\frac{1}{\lambda n}\sum_{i=1}^n\alpha_i x_i$.
--   2. **Primal objective** (eq. (1)): $\;P(w)=\frac1n\sum_{i=1}^n\varphi_i(w^\top x_i)+\frac{\lambda}{2}\|w\|^2$.
--   3. **Dual objective** (eq. (2)):
--   $$D(\alpha)=\frac1n\sum_{i=1}^n-\varphi_i^*(-\alpha_i)-\frac{\lambda}{2}\Big\|\frac{1}{\lambda n}\sum_{i=1}^n\alpha_i x_i\Big\|^2\in[-\infty,+\infty),$$
--   which is $-\infty$ exactly when some $\varphi_i^*(-\alpha_i)=+\infty$.
--   4. **Coordinate objective**: for a dual point $\alpha$, a coordinate $i$ and an increment $\delta\in\mathbb R$,
--   $$\delta\ \mapsto\ -\varphi_i^*\big(-(\alpha_i+\delta)\big)-\frac{\lambda n}{2}\big\|w(\alpha)+(\lambda n)^{-1}\delta x_i\big\|^2 .$$
--   5. **SDCA step**: a map $\Delta$ assigning to every dual point $\alpha$ and coordinate $i$ an increment $\Delta(\alpha,i)$ is an *SDCA step* if $\Delta(\alpha,i)$ maximizes the coordinate objective for all $\alpha,i$ ("Find $\Delta\alpha_i$ to maximize …"). The update is $\alpha\leftarrow\alpha+\Delta(\alpha,i)\,e_i$.
--   6. **Run**: given the coordinates $j_1,j_2,\dots,j_T\in\{1,\dots,n\}$ chosen at iterations $1,\dots,T$, the iterates are $\alpha^{(0)}=0$ and $\alpha^{(t)}=\alpha^{(t-1)}+\Delta(\alpha^{(t-1)},j_t)\,e_{j_t}$; the primal iterate is $w^{(t)}=w(\alpha^{(t)})$, which the procedure maintains incrementally.
--   7. **Averaging option output**: for $T_0<T$, $\;\bar\alpha=\frac{1}{T-T_0}\sum_{t=T_0+1}^{T}\alpha^{(t-1)}$ and $\bar w=w(\bar\alpha)$.
--
--   Choosing $j_1,\dots,j_T$ independently and uniformly at random gives the randomness of SDCA; an expectation over the run is the average over all $n^T$ index sequences.
--
--   **Formalization Note** $D$ is `EReal`-valued and built from the `EReal` conjugate `SDCA.Lipschitz.conj`; the one-step update is `SDCA.Lipschitz.sdcaStep` (both shared with the other missions of this paper). The step is a function `Δ : (Fin n → ℝ) → Fin n → ℝ` constrained by the argmax predicate `IsSDCAStep` (no choice function is used); a maximizer exists for convex real-valued losses and $\lambda>0$. Indices are `Fin n` and run from $0$; `alphaIter Δ js t` is $\alpha^{(t)}$ for the index sequence `js : Fin T → Fin n` (it uses only the first $t$ indices), and `alphaAvg Δ js T₀` is $\bar\alpha$, the average of $\alpha^{(T_0)},\dots,\alpha^{(T-1)}$ (the page's summation index "$i=T_0+1$" is read as $t$). The uniform expectation is the published `SAGA.Convex.expectIdx`.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 1, problem (1); p. 2, dual (2) and w(α) (3); p. 5, Procedure SDCA (Averaging option)

import Mathlib
import Definitions.Def_SDCA_Smooth_conj
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SDCA_Lipschitz_Model

namespace SDCA.Smooth

open scoped InnerProductSpace

/-- The primal vector `w(α) = (1/(λn)) ∑ᵢ αᵢ xᵢ` of eq. (3) (p. 2). -/
noncomputable def wOf {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (α : Fin n → ℝ) : EuclideanSpace ℝ (Fin d) :=
  (1 / (lam * n)) • ∑ i, α i • x i

/-- The primal objective `P(w) = (1/n) ∑ᵢ φᵢ(wᵀxᵢ) + (λ/2)‖w‖²` of problem (1) (p. 1). -/
noncomputable def primal {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (n : ℝ)) * (∑ i, φ i ⟪w, x i⟫_ℝ) + lam / 2 * ‖w‖ ^ 2

/-- The dual objective `D(α) = (1/n) ∑ᵢ −φᵢ*(−αᵢ) − (λ/2)‖(1/(λn)) ∑ᵢ αᵢ xᵢ‖²` of problem (2)
(p. 2), in `EReal`: it is `⊥` exactly when some `φᵢ*(−αᵢ) = +∞`, and it is never `⊤`. -/
noncomputable def dual {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) : EReal :=
  ((1 / (n : ℝ) : ℝ) : EReal) * (∑ i, -SDCA.Lipschitz.conj (φ i) (-α i)) -
    ((lam / 2 * ‖wOf lam x α‖ ^ 2 : ℝ) : EReal)

/-- The objective maximized by one SDCA step on coordinate `i` at the dual point `α`
(Procedure SDCA, p. 5): `δ ↦ −φᵢ*(−(αᵢ + δ)) − (λn/2)‖w(α) + (λn)⁻¹ δ xᵢ‖²`. -/
noncomputable def coordObj {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) (i : Fin n) (δ : ℝ) : EReal :=
  -SDCA.Lipschitz.conj (φ i) (-(α i + δ)) -
    ((lam * n / 2 * ‖wOf lam x α + (lam * n)⁻¹ • (δ • x i)‖ ^ 2 : ℝ) : EReal)

/-- `Δ α i` is a maximizer of the coordinate objective `coordObj … α i` for every dual point `α`
and every coordinate `i` ("Find Δαᵢ to maximize …", Procedure SDCA, p. 5). -/
def IsSDCAStep {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (Δ : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (α : Fin n → ℝ) (i : Fin n) (δ : ℝ), coordObj lam x φ α i δ ≤ coordObj lam x φ α i (Δ α i)

/-- The dual iterate `α⁽ᵗ⁾` of Procedure SDCA started at `α⁽⁰⁾ = 0`, when the coordinates chosen
at iterations `1, 2, …` are `js 0, js 1, …`: the first `t` steps are applied (for `t ≤ T`; it
depends only on the first `t` indices). The primal iterate is `w⁽ᵗ⁾ = w(α⁽ᵗ⁾)`. -/
noncomputable def alphaIter {n T : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ) (js : Fin T → Fin n)
    (t : ℕ) : Fin n → ℝ :=
  ((List.ofFn js).take t).foldl (SDCA.Lipschitz.sdcaStep Δ) 0

/-- The output of the Averaging option of Procedure SDCA (p. 5):
`ᾱ = (1/(T − T₀)) ∑_{t=T₀+1}^{T} α⁽ᵗ⁻¹⁾`, the average of `α⁽ᵀ⁰⁾, …, α⁽ᵀ⁻¹⁾`; the primal output is
`w̄ = w(ᾱ)`. -/
noncomputable def alphaAvg {n T : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ) (js : Fin T → Fin n)
    (T₀ : ℕ) : Fin n → ℝ :=
  (1 / ((T : ℝ) - T₀)) • ∑ t ∈ Finset.Ico T₀ T, alphaIter Δ js t

end SDCA.Smooth


