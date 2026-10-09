-- Prove2me | Definitions.Def_IQCAlg_ConvexIQC_Setting
-- name    : IQCAlg_ConvexIQC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:56.696845+00:00
-- url     : https://prove2.me/theorems/3788139e-76e9-4f7a-9082-7e3690ee770e
-- title:
--   §1.1 p. 3 and §3.3 pp. 13–16 — the class S(m, L), the shifted signals ỹ, ũ, and the terms s, p, g, q of Lemmas 6–10
-- statement:
--   This file fixes the objects of Section 3.3 of Lessard, Recht and Packard.
--
--   1. **The space.** $\mathbb R^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and the Euclidean norm $\|\cdot\|$.
--   2. **The class $S(m,L)$** (p. 3). For $0<m<L$, a function $f:\mathbb R^d\to\mathbb R$ belongs to $S(m,L)$ if it is continuously differentiable, strongly convex with parameter $m$, that is
--   $$f(a x+b y)\le a f(x)+b f(y)-\tfrac m2\,ab\,\|x-y\|^2\qquad(a,b\ge0,\ a+b=1),$$
--   and its gradient is $L$-Lipschitz, $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$.
--   3. **Shifted signals.** For a sequence $y=(y_k)_{k\ge0}$ in $\mathbb R^d$ and a reference point $y_\star$, the gradient is fed back as $u_k=\nabla f(y_k)$, the reference output is $u_\star=\nabla f(y_\star)$, and
--   $$\tilde y_k:=y_k-y_\star,\qquad \tilde u_k:=u_k-u_\star .$$
--   4. **The sector and off-by-one terms** (p. 16):
--   $$s_k:=(\tilde u_k-m\tilde y_k)^{\mathsf T}(L\tilde y_k-\tilde u_k),\qquad p_{k+1}:=(\tilde u_{k+1}-m\tilde y_{k+1})^{\mathsf T}\big(L(\tilde y_{k+1}-\tilde y_k)-(\tilde u_{k+1}-\tilde u_k)\big),$$
--   and, for a parameter $\bar\rho$, the general term of (3.20) without its weight,
--   $$w_{k+1}:=(\tilde u_{k+1}-m\tilde y_{k+1})^{\mathsf T}\big(L(\tilde y_{k+1}-\bar\rho^2\tilde y_k)-(\tilde u_{k+1}-\bar\rho^2\tilde u_k)\big).$$
--   5. **Lemma 8's auxiliary function** (p. 14): $g(x):=f(x)-f(y_\star)-\tfrac m2\|x-y_\star\|^2$, the vector $\nabla f(x)-m(x-y_\star)$ (which is $\nabla g(x)$), and
--   $$q(x):=(L-m)\,g(x)-\tfrac12\|\nabla f(x)-m(x-y_\star)\|^2,$$
--   so that $q_k=q(y_k)$ in (3.16).
--
--   These are the quantities in which the sector, off-by-one, Zames–Falb and weighted off-by-one integral quadratic constraints of the paper are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the 2-norm of the paper. Strong convexity is Mathlib's `StrongConvexOn Set.univ m f`. The terms $p$ and $w$ are indexed by $k$ for the paper's $t=k+1$, which avoids natural-number subtraction. The block quadratic forms of the paper are written out expanded in the theorems.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 3 (S(m, L), §1.1), pp. 13–16 (§3.3: Lemma 6, Lemma 8 and its proof (3.16), Lemma 10 and its proof)

import Mathlib

namespace IQCAlg.ConvexIQC

open scoped InnerProductSpace

/-- ℝᵈ with the Euclidean (2-)norm and inner product, p. 3. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The class `S(m, L)`, p. 3: for `0 < m < L`, the functions `f : ℝᵈ → ℝ` that are continuously
differentiable, strongly convex with parameter `m`, and have `L`-Lipschitz gradients. -/
structure InSmL {d : ℕ} (f : E d → ℝ) (m L : ℝ) : Prop where
  pos_m : 0 < m
  m_lt_L : m < L
  contDiff : ContDiff ℝ 1 f
  strongConvex : StrongConvexOn Set.univ m f
  lipschitz_grad : ∀ x y : E d, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- `ỹ_k := y_k − y⋆`. -/
def yt {d : ℕ} (y : ℕ → E d) (ys : E d) (k : ℕ) : E d := y k - ys

/-- `ũ_k := u_k − u⋆` with `u_k = ∇f(y_k)` and the reference `u⋆ = ∇f(y⋆)`. -/
noncomputable def ut {d : ℕ} (f : E d → ℝ) (y : ℕ → E d) (ys : E d) (k : ℕ) : E d :=
  gradient f (y k) - gradient f ys

/-- The sector term `s_k := (ũ_k − m ỹ_k)ᵀ(L ỹ_k − ũ_k)` (p. 16; the first term of (3.15), (3.20)). -/
noncomputable def sTerm {d : ℕ} (f : E d → ℝ) (m L : ℝ) (y : ℕ → E d) (ys : E d) (k : ℕ) : ℝ :=
  ⟪ut f y ys k - m • yt y ys k, L • yt y ys k - ut f y ys k⟫_ℝ

/-- The off-by-one term `p_{k+1} := (ũ_{k+1} − m ỹ_{k+1})ᵀ(L(ỹ_{k+1} − ỹ_k) − (ũ_{k+1} − ũ_k))`
(p. 16; the general term of (3.15)), indexed by `k` so that no natural subtraction occurs. -/
noncomputable def pTerm {d : ℕ} (f : E d → ℝ) (m L : ℝ) (y : ℕ → E d) (ys : E d) (k : ℕ) : ℝ :=
  ⟪ut f y ys (k + 1) - m • yt y ys (k + 1),
    L • (yt y ys (k + 1) - yt y ys k) - (ut f y ys (k + 1) - ut f y ys k)⟫_ℝ

/-- The general term of (3.20) at `t = k + 1` (without the weight `ρ^{−2t}`):
`(ũ_{k+1} − m ỹ_{k+1})ᵀ(L(ỹ_{k+1} − ρ̄² ỹ_k) − (ũ_{k+1} − ρ̄² ũ_k))`. -/
noncomputable def wTerm {d : ℕ} (f : E d → ℝ) (m L ρbar : ℝ) (y : ℕ → E d) (ys : E d)
    (k : ℕ) : ℝ :=
  ⟪ut f y ys (k + 1) - m • yt y ys (k + 1),
    L • (yt y ys (k + 1) - ρbar ^ 2 • yt y ys k) - (ut f y ys (k + 1) - ρbar ^ 2 • ut f y ys k)⟫_ℝ

/-- Lemma 8's auxiliary function `g(x) := f(x) − f(y⋆) − (m/2)‖x − y⋆‖²` (p. 14). -/
noncomputable def gFun {d : ℕ} (f : E d → ℝ) (ys : E d) (m : ℝ) (x : E d) : ℝ :=
  f x - f ys - m / 2 * ‖x - ys‖ ^ 2

/-- The vector `∇f(x) − m(x − y⋆)`, which is `∇g(x)` (p. 14). -/
noncomputable def gGrad {d : ℕ} (f : E d → ℝ) (ys : E d) (m : ℝ) (x : E d) : E d :=
  gradient f x - m • (x - ys)

/-- `q(x) := (L − m) g(x) − (1/2)‖∇g(x)‖²`; at `x = y_k` this is `q_k` of (3.16) (p. 14). -/
noncomputable def qTerm {d : ℕ} (f : E d → ℝ) (ys : E d) (m L : ℝ) (x : E d) : ℝ :=
  (L - m) * gFun f ys m x - ‖gGrad f ys m x‖ ^ 2 / 2

end IQCAlg.ConvexIQC


