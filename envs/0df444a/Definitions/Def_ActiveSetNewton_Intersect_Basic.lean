-- Prove2me | Definitions.Def_ActiveSetNewton_Intersect_Basic
-- name    : ActiveSetNewton_Intersect_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:24.740915+00:00
-- url     : https://prove2.me/theorems/f16ad750-b8de-46b9-b083-3ce72a144bbf
-- title:
--   §2–§5, pp. 3–9 — C(r)-manifold around a point, transversality, isolated intersection, linear approximation x + T_X(x), constant rank, nearest point, quadratic convergence
-- statement:
--   Throughout, $\mathbf E$ is a Euclidean space (a finite-dimensional real inner-product space) with norm $|\cdot|$. For a set $\mathcal X\subset\mathbf E$ and a point $x$, $T_{\mathcal X}(x)$ is the linear span of the tangent cone of $\mathcal X$ at $x$ and $N_{\mathcal X}(x)=T_{\mathcal X}(x)^{\perp}$ is the normal space; both are imported from the published definition `ProjLikeRetr.Retractor.tangentBundle`.
--
--   1. **Manifold around a point** (§2, p. 3). For a degree $r\in\{1,2,3,\dots\}$, a set $\mathcal X\subset\mathbf E$ is a $C^{(r)}$-*manifold around* $z\in\mathcal X$ if there are a number $m$, a $C^{(r)}$-smooth map $F:\mathbf E\to\mathbf R^m$ whose derivative $DF(z)$ is surjective, and an open set $V\ni z$ with
--   $$\mathcal X\cap V \;=\; F^{-1}(0)\cap V .$$
--   2. **Transversality** (§2, p. 4). $\mathcal X$ and $\mathcal Y$ intersect *transversally* at $z$ if $N_{\mathcal X}(z)\cap N_{\mathcal Y}(z)=\{0\}$.
--   3. **Isolated point of intersection** (§3, p. 4). $z$ is an isolated point of intersection of $\mathcal X$ and $\mathcal Y$ if $\mathcal X\cap\mathcal Y\cap V=\{z\}$ for some open $V\ni z$.
--   4. **Linear approximation** (§3, p. 4). The linear approximation to $\mathcal X$ at $x$ is the affine set $x+T_{\mathcal X}(x)=\{w : w-x\in T_{\mathcal X}(x)\}$.
--   5. **Constant rank nearby** (§5, p. 9). A map $P:\mathbf E\to\mathbf E$ is *$C^{(2)}$-smooth and constant rank nearby $z$ on $\mathcal X$* if there are an open set $V\ni z$ on which $P$ is $C^{(2)}$ and a number $k$ with
--   $$\dim DP(x)\big(T_{\mathcal X}(x)\big)=k\qquad\text{for all } x\in\mathcal X\cap V .$$
--   6. **Nearest point.** $p$ is the nearest point of a set $A$ to $y$, written $p=\mathrm{Proj}_A(y)$, if $p\in A$ and $|y-p|<|y-q|$ for every other $q\in A$.
--   7. **Quadratic convergence.** Starting from any point $x\in A$ near $z$, the iteration $x\leftarrow T(x)$ *converges quadratically to $z$* if there are $\delta>0$ and $C\ge 0$ such that, for every $x_0\in A$ with $|x_0-z|<\delta$, the iterates $x_{n+1}=T(x_n)$ all lie in $A$ with $|x_n-z|<\delta$, satisfy
--   $$|x_{n+1}-z|\le C\,|x_n-z|^2\qquad(n=0,1,2,\dots),$$
--   and converge to $z$.
--
--   These are the objects of Lewis and Wylie's semi-linearization scheme: to find the isolated common point $z$ of two manifolds, linearize one of them at the current point, intersect with the other, and restore the result to the first manifold.
--
--   **Formalization Note** "$F^{-1}(0)$ is a neighborhood of $z$ in $\mathcal X$" is read as local equality on an open set $V$. The tangent space is intrinsic (span of Mathlib's `tangentConeAt`), as the paper itself does on p. 7 ("$T$ denotes the standard tangent cone, which coincides with the classical tangent space for manifolds"), so it does not depend on a choice of $F$. The paper never defines smoothness of a map on a manifold; "$C^{(2)}$-smooth and constant rank nearby" is read as $C^{(2)}$ on an open set of $\mathbf E$ around $z$ (a $C^{(2)}$ map on an embedded $C^{(2)}$ manifold has such a local extension) with the rank of $DP(x)$ restricted to $T_{\mathcal X}(x)$ constant on $\mathcal X$ near $z$. Smoothness degree $C^{(r)}$ is Mathlib's `ContDiff ℝ r` with $r$ a natural number. Quadratic convergence carries one constant $C$ for all starting points, keeps the iterates in $A$ near $z$ (where the iteration is defined), and includes convergence to $z$.
-- source:
--   Lewis & Wylie, Active-set Newton methods and partial smoothness, arXiv:1902.00724v1, pp. 3–4, §2 (manifolds, tangent and normal spaces, transversality); p. 4, Theorem 3.1 (isolated intersection, linear approximation); p. 6, Corollary 3.5 (quadratic convergence); p. 9, Theorem 5.1 (constant rank); p. 7 (tangent cone convention)

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ActiveSetNewton.Intersect

open Metric Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- §2, p. 3: `X` is a `C^(r)`-manifold around `z ∈ X`: there is a `C^(r)`-smooth map
`F : E → ℝ^m` with surjective derivative `DF(z)` such that `F⁻¹(0)` is a neighborhood of `z`
in `X`, read as: `X` and `F⁻¹(0)` agree on some open set `V ∋ z`. -/
def IsCManifoldAround (r : ℕ) (X : Set E) (z : E) : Prop :=
  z ∈ X ∧ ∃ (m : ℕ) (F : E → EuclideanSpace ℝ (Fin m)), ContDiff ℝ r F ∧
    Function.Surjective (fderiv ℝ F z) ∧
    ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ X ∩ V = F ⁻¹' {0} ∩ V

/-- §2, p. 4: two manifolds around `z` intersect transversally at `z` when their normal spaces
`N_X(z) = T_X(z)ᗮ` and `N_Y(z) = T_Y(z)ᗮ` intersect trivially. -/
def TransversalAt (X Y : Set E) (z : E) : Prop :=
  ProjLikeRetr.Retractor.normalSpace X z ⊓ ProjLikeRetr.Retractor.normalSpace Y z = ⊥

/-- §3, p. 4: `z` is an isolated point of intersection of `X` and `Y`: some open `V ∋ z` has
`X ∩ Y ∩ V = {z}`. -/
def IsolatedIntersection (X Y : Set E) (z : E) : Prop :=
  ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ X ∩ Y ∩ V = {z}

/-- §3, p. 4: the linear approximation `x + T_X(x)` to `X` at `x`. -/
def linApprox (X : Set E) (x : E) : Set E :=
  {w | w - x ∈ ProjLikeRetr.Retractor.tangentSpace X x}

/-- §5, p. 9: the map `P` is `C^(2)`-smooth and constant rank nearby `z` on `X`: `P` is `C^(2)` on
an open set `V ∋ z` of `E`, and the rank of `DP(x)` restricted to `T_X(x)`, i.e. the dimension of
`DP(x)(T_X(x))`, is the same for every `x ∈ X ∩ V`. -/
def HasConstantRankNear (P : E → E) (X : Set E) (z : E) : Prop :=
  ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ 2 P V ∧ ∃ k : ℕ, ∀ x ∈ X ∩ V,
    Module.finrank ℝ ((ProjLikeRetr.Retractor.tangentSpace X x).map
      (fderiv ℝ P x : E →ₗ[ℝ] E)) = k

/-- `p` is the unique nearest point of `A` to `y`: `p ∈ A`, `|y − p| ≤ |y − q|` for every `q ∈ A`,
and equality holds only for `q = p` (so `p = Proj_A(y)`). -/
def IsNearestPoint (A : Set E) (y p : E) : Prop :=
  p ∈ A ∧ ∀ q ∈ A, ‖y - p‖ ≤ ‖y - q‖ ∧ (‖y - q‖ = ‖y - p‖ → q = p)

/-- "Starting from any point `x ∈ A` near `z`, the iteration `x ← T x` converges quadratically to
`z`": there are `δ > 0` and `C ≥ 0` such that from every `x₀ ∈ A` with `|x₀ − z| < δ` all iterates
stay in `A ∩ B(z, δ)`, satisfy `|x_{n+1} − z| ≤ C |x_n − z|²`, and converge to `z`. -/
def ConvergesQuadratically (T : E → E) (A : Set E) (z : E) : Prop :=
  ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ x₀ ∈ A ∩ ball z δ,
    (∀ n : ℕ, T^[n] x₀ ∈ A ∩ ball z δ ∧ ‖T^[n + 1] x₀ - z‖ ≤ C * ‖T^[n] x₀ - z‖ ^ 2) ∧
    Tendsto (fun n => T^[n] x₀) atTop (𝓝 z)

end ActiveSetNewton.Intersect


