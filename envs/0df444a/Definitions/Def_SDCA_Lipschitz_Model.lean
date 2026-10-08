-- Prove2me | Definitions.Def_SDCA_Lipschitz_Model
-- name    : SDCA_Lipschitz_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:22.696266+00:00
-- url     : https://prove2.me/theorems/29b1c81b-01b9-4b04-b9e6-99170171fbd1
-- title:
--   Primal (1), dual (2), $w(\alpha)$ (3), the SDCA coordinate step and run, and the averaged output (Procedure SDCA)
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$, let $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ and let $\lambda\in\mathbb R$ (in every theorem $\lambda>0$). The norm is the Euclidean norm and $w^\top x$ the Euclidean inner product. This file defines the objects of Shalev-Shwartz and Zhang's analysis of stochastic dual coordinate ascent (SDCA).
--
--   1. **Primal–dual link** (3): for $\alpha\in\mathbb R^n$, $\;w(\alpha)=\frac{1}{\lambda n}\sum_{i=1}^n\alpha_ix_i$.
--   2. **Primal objective** (1): $\;P(w)=\frac1n\sum_{i=1}^n\phi_i(w^\top x_i)+\frac\lambda2\|w\|^2$.
--   3. **Dual objective** (2): $\;D(\alpha)=\frac1n\sum_{i=1}^n-\phi_i^*(-\alpha_i)-\frac\lambda2\|w(\alpha)\|^2\in[-\infty,\infty)$, where $\phi_i^*$ is the convex conjugate. $D(\alpha)=-\infty$ exactly when some $\phi_i^*(-\alpha_i)=+\infty$.
--   4. **Coordinate objective** (Procedure SDCA, p. 5): at the dual state $\alpha$, for a coordinate $i$ and an increment $\delta=\Delta\alpha_i$,
--   $$\mathcal A_{\alpha,i}(\delta)=-\phi_i^*\bigl(-(\alpha_i+\delta)\bigr)-\frac{\lambda n}{2}\Bigl\|w(\alpha)+(\lambda n)^{-1}\delta\,x_i\Bigr\|^2 .$$
--   Since $w(\alpha+\delta e_i)=w(\alpha)+(\lambda n)^{-1}\delta x_i$, one has $n\,[D(\alpha+\delta e_i)-D(\alpha)]=\mathcal A_{\alpha,i}(\delta)-\mathcal A_{\alpha,i}(0)$ whenever $D(\alpha)$ is finite.
--   5. **SDCA step rule**: a map $\Delta$ assigning to each state $\alpha$ and coordinate $i$ an increment $\Delta(\alpha,i)$ is an *SDCA step* if $\Delta(\alpha,i)$ maximizes $\mathcal A_{\alpha,i}$ ("Find $\Delta\alpha_i$ to maximize …"). The update is $\alpha\leftarrow\alpha+\Delta(\alpha,i)\,e_i$.
--   6. **Run**: for an initial point $\alpha^{(0)}$ and a sequence of picked coordinates $j_1,\dots,j_T$, the iterate $\alpha^{(t)}$ ($t\le T$) is obtained by applying the updates with $j_1,\dots,j_t$ in order. The primal iterate is $w^{(t)}=w(\alpha^{(t)})$, which is what the update $w^{(t)}\leftarrow w^{(t-1)}+(\lambda n)^{-1}\Delta\alpha_ix_i$ maintains.
--   7. **Averaging option** (p. 5): for $T_0<T$, $\;\bar\alpha=\frac{1}{T-T_0}\sum_{t=T_0+1}^{T}\alpha^{(t-1)}$, i.e. the average of $\alpha^{(T_0)},\dots,\alpha^{(T-1)}$, and $\bar w=w(\bar\alpha)$.
--
--   These are the objects in which the convergence guarantees of SDCA for Lipschitz losses (Theorem 1) are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and indices are `Fin n`. $D$ is `EReal`-valued (real coefficients coerced). The step is a free map `Δ : (Fin n → ℝ) → Fin n → ℝ` constrained by the predicate `IsSDCAStep` (an arg-max condition), not a choice function; a maximizer exists for convex real $\phi_i$ because $\mathcal A_{\alpha,i}$ is upper semicontinuous, concave and tends to $-\infty$. The coordinate sequence is a function `js : Fin T → Fin n` (0-based, `js k` is the coordinate of iteration $k+1$), the run is a left fold over its first $t$ entries, and expectations over uniformly random coordinates are taken with `SAGA.Convex.expectIdx`. The page's averaging sum is printed with index $i$; it runs over $t$.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 1, (1); p. 2, (2), (3); p. 5, Procedure SDCA (Averaging option)

import Mathlib
import Definitions.Def_SDCA_Lipschitz_conj

namespace SDCA.Lipschitz

/-- `w(α) = (1/(λn)) ∑ᵢ αᵢ xᵢ` (eq. (3), p. 2). -/
noncomputable def wOf {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (α : Fin n → ℝ) : EuclideanSpace ℝ (Fin d) :=
  (1 / (lam * n)) • ∑ i, α i • x i

/-- The primal objective `P(w) = (1/n) ∑ᵢ φᵢ(wᵀxᵢ) + (λ/2)‖w‖²` (eq. (1), p. 1). -/
noncomputable def primal {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (lam : ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, φ i (inner ℝ w (x i)) + lam / 2 * ‖w‖ ^ 2

/-- The dual objective `D(α) = (1/n) ∑ᵢ −φᵢ*(−αᵢ) − (λ/2)‖(1/(λn)) ∑ᵢ αᵢ xᵢ‖²` (eq. (2), p. 2),
in `EReal`. Each `−φᵢ*(−αᵢ)` is never `⊤`, so the sum is well defined; `D(α) = ⊥` exactly when
some `φᵢ*(−αᵢ) = ⊤`. -/
noncomputable def dual {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (lam : ℝ) (α : Fin n → ℝ) : EReal :=
  (((1 / (n : ℝ)) : ℝ) : EReal) * ∑ i, -conj (φ i) (-α i)
    - ((lam / 2 * ‖wOf x lam α‖ ^ 2 : ℝ) : EReal)

/-- The coordinate objective maximized by one step of Procedure SDCA (p. 5): at the dual state `α`,
for coordinate `i` and increment `δ = Δαᵢ`,
`−φᵢ*(−(αᵢ + δ)) − (λn/2) ‖w(α) + (λn)⁻¹ δ xᵢ‖²`. -/
noncomputable def coordObj {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (lam : ℝ) (α : Fin n → ℝ) (i : Fin n) (δ : ℝ) : EReal :=
  -conj (φ i) (-(α i + δ))
    - ((lam * n / 2 * ‖wOf x lam α + (1 / (lam * n)) • (δ • x i)‖ ^ 2 : ℝ) : EReal)

/-- `Δ` is an SDCA step rule: for every dual state `α` and coordinate `i`, the increment `Δ α i`
maximizes the coordinate objective `coordObj φ x lam α i` ("Find Δαᵢ to maximize …", p. 5). -/
def IsSDCAStep {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (α : Fin n → ℝ) (i : Fin n) (δ : ℝ), coordObj φ x lam α i δ ≤ coordObj φ x lam α i (Δ α i)

/-- One SDCA update with the picked coordinate `i`: `α ← α + Δαᵢ eᵢ` (p. 5). -/
noncomputable def sdcaStep {n : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ) (α : Fin n → ℝ) (i : Fin n) :
    Fin n → ℝ :=
  α + Pi.single i (Δ α i)

/-- The SDCA iterate `α⁽ᵗ⁾` started at `α⁽⁰⁾ = α0` along the coordinate sequence `js`: the
updates with the first `t` picked coordinates `js 0, …, js (t−1)`, in order (for `t ≤ T`).
The primal iterate is `w⁽ᵗ⁾ = w(α⁽ᵗ⁾)`, which the update `w⁽ᵗ⁾ ← w⁽ᵗ⁻¹⁾ + (λn)⁻¹Δαᵢxᵢ` maintains. -/
noncomputable def sdcaIter {n T : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ) (α0 : Fin n → ℝ)
    (js : Fin T → Fin n) (t : ℕ) : Fin n → ℝ :=
  ((List.ofFn js).take t).foldl (sdcaStep Δ) α0

/-- The Averaging-option output `ᾱ = (1/(T − T₀)) ∑_{t=T₀+1}^{T} α⁽ᵗ⁻¹⁾` (p. 5), i.e. the average
of `α⁽ᵀ⁰⁾, …, α⁽ᵀ⁻¹⁾`; the corresponding primal output is `w̄ = w(ᾱ)`. -/
noncomputable def avgDual {n T : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ) (α0 : Fin n → ℝ)
    (js : Fin T → Fin n) (T0 : ℕ) : Fin n → ℝ :=
  (1 / ((T : ℝ) - T0)) • ∑ t ∈ Finset.Ico T0 T, sdcaIter Δ α0 js t

end SDCA.Lipschitz


