-- Prove2me | Definitions.Def_PolySwap_KMS_Cohomology
-- name    : PolySwap_KMS_Cohomology
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:39:32.211175+00:00
-- url     : https://prove2.me/theorems/b1484aaa-e957-443a-a1cb-172ccf17362f
-- title:
--   Non-abelian cochains, $h^0$, $h^1$, $H^1$, $(\Lambda,\beta)$ 1-coboundary expanders and $(\beta,r,\Lambda)$-swap coboundary expanders
-- statement:
--   Let $X$ be a finite pure weighted complex and $\Lambda$ any group. $C^0(X,\Lambda)$ consists of the maps $X(0)\to\Lambda$ and $C^1(X,\Lambda)$ of the maps $\phi$ on ordered edges with $\phi(uv)=\phi(vu)^{-1}$. The coboundaries are
--   $$d_0\phi(v_0v_1)=\phi(v_1)\phi(v_0)^{-1},\qquad d_1\phi(v_0v_1v_2)=\phi(v_0v_1)\phi(v_2v_0)\phi(v_1v_2),$$
--   $Z^k=\{\phi: d_k\phi\equiv1\}$ and $B^1=\operatorname{Im}d_0$; $H^1(X,\Lambda)$ is **trivial** iff $B^1=Z^1$. With the Garland weights $w$, $\|d_0\phi\|$ and $\|d_1\phi\|$ are the total weights of the edges, resp. triangles, on which the coboundary is $\ne1$, and $\mathrm{dist}(\phi,\psi)$ is the total weight of the vertices (for $k=0$), resp. edges (for $k=1$), on which $\phi\psi^{-1}\ne1$. The **cocycle expansion constants** are
--   $$h^k(X,\Lambda)=\min_{\phi\in C^k\setminus Z^k}\frac{\|d_k\phi\|}{\min_{\psi\in Z^k}\mathrm{dist}(\phi,\psi)}\quad(k=0,1).$$
--   $X$ is a **$(\Lambda,\beta)$ 1-coboundary expander** if $h^0(X,\Lambda)\ge\beta$, $h^1(X,\Lambda)\ge\beta$ and $H^1(X,\Lambda)$ is trivial. $X$ is a **$(\beta,r,\Lambda)$-swap coboundary expander** if its $r$-faces complex $F^rX$ is a $(\Lambda,\beta)$ 1-coboundary expander.
--
--   **Formalization Note.** Cochains are total functions `V → Λ`, `V → V → Λ`; only their values on vertices, ordered edges and ordered triangles matter, and `IsC1` imposes antisymmetry on ordered edges. Supports of unordered edges and triangles are taken with some ordering (all orderings agree for antisymmetric cochains). `HZeroGe Λ β` and `HOneGe Λ β` state $h^k\ge\beta$ in ratio-free form: every $k$-cochain $\phi$ has a $k$-cocycle $\psi$ with $\beta\cdot\mathrm{dist}(\phi,\psi)\le\|d_k\phi\|$. This is equivalent because the minimum distance to $Z^k$ is attained (finitely many values) and positive for $\phi\notin Z^k$ (positive Garland weights), while $\phi\in Z^k$ takes $\psi=\phi$.
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.2.2 (pp. 11–13, Definitions 2.8, 2.9) and §2.2.3 (p. 14, Definition 2.12)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex

open Classical

noncomputable section

namespace PolySwap.KMS

/-!
# Non-abelian cochains, cocycle expansion constants and (swap) coboundary expansion

Dikstein, Oppenheim, Valentiner-Branth, *Polynomial Swap Coboundary Expansion with Applications
to LTCs and PCPs*, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.2.2 (pp. 11–13,
Definitions 2.8, 2.9) and §2.2.3 (p. 14, Definition 2.12).

Cochains are total functions; only their values on vertices, ordered edges and ordered triangles
of the complex matter. A 1-cochain is antisymmetric on ordered edges.
-/

namespace WComplex

variable {V : Type*} (X : WComplex V) {Λ : Type*} [Group Λ]

/-- `uv` is an ordered edge of `X`. -/
def IsEdge (u v : V) : Prop := u ≠ v ∧ X.IsFace {u, v}

/-- `uvw` is an ordered triangle of `X`. -/
def IsTri (u v w : V) : Prop := u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ X.IsFace {u, v, w}

/-- `ϕ ∈ C¹(X, Λ)`: `ϕ(uv) = ϕ(vu)⁻¹` on every ordered edge. -/
def IsC1 (ϕ : V → V → Λ) : Prop := ∀ u v, X.IsEdge u v → ϕ u v = (ϕ v u)⁻¹

/-- `d₀ϕ(v₀v₁) = ϕ(v₁)ϕ(v₀)⁻¹`. -/
def d0 (g : V → Λ) (u v : V) : Λ := g v * (g u)⁻¹

/-- `d₁ϕ(v₀v₁v₂) = ϕ(v₀v₁)ϕ(v₂v₀)ϕ(v₁v₂)`. -/
def d1 (ϕ : V → V → Λ) (u v w : V) : Λ := ϕ u v * ϕ w u * ϕ v w

/-- `Z⁰(X, Λ)`: `d₀g ≡ 1` on ordered edges. -/
def IsZ0 (g : V → Λ) : Prop := ∀ u v, X.IsEdge u v → d0 g u v = 1

/-- `Z¹(X, Λ)`: antisymmetric `ϕ` with `d₁ϕ ≡ 1` on ordered triangles. -/
def IsZ1 (ϕ : V → V → Λ) : Prop := X.IsC1 ϕ ∧ ∀ u v w, X.IsTri u v w → d1 ϕ u v w = 1

/-- `H¹(X, Λ)` is trivial, i.e. `B¹(X, Λ) = Z¹(X, Λ)`: every 1-cocycle equals `d₀g` on every
ordered edge for some 0-cochain `g`. -/
def H1Trivial (Λ : Type*) [Group Λ] : Prop :=
  ∀ ϕ : V → V → Λ, X.IsZ1 ϕ → ∃ g : V → Λ, ∀ u v, X.IsEdge u v → ϕ u v = d0 g u v

/-- `‖d₀g‖ = Σ_{e ∈ supp(d₀g)} w(e)`. -/
def normD0 (g : V → Λ) : ℝ :=
  ∑ e ∈ (X.facesCard 2).filter (fun e => ∃ u v, e = {u, v} ∧ d0 g u v ≠ 1), X.gw e

/-- `‖d₁ϕ‖ = Σ_{t ∈ supp(d₁ϕ)} w(t)`. -/
def normD1 (ϕ : V → V → Λ) : ℝ :=
  ∑ t ∈ (X.facesCard 3).filter (fun t => ∃ u v w, t = {u, v, w} ∧ d1 ϕ u v w ≠ 1), X.gw t

/-- `dist(ϕ, ψ) = w({v ∈ X(0) | ϕ(v)ψ(v)⁻¹ ≠ 1})` for 0-cochains. -/
def dist0 (ϕ ψ : V → Λ) : ℝ :=
  ∑ v ∈ X.vertices.filter (fun v => ϕ v * (ψ v)⁻¹ ≠ 1), X.gw {v}

/-- `dist(ϕ, ψ) = w({{u,v} ∈ X(1) | ϕ(uv)ψ(uv)⁻¹ ≠ 1})` for 1-cochains. -/
def dist1 (ϕ ψ : V → V → Λ) : ℝ :=
  ∑ e ∈ (X.facesCard 2).filter (fun e => ∃ u v, e = {u, v} ∧ ϕ u v * (ψ u v)⁻¹ ≠ 1), X.gw e

/-- `h⁰(X, Λ) ≥ β` (Definition 2.8), in ratio-free form: every 0-cochain `ϕ` has a 0-cocycle
`ψ` with `β · dist(ϕ, ψ) ≤ ‖d₀ϕ‖`. (For `ϕ ∉ Z⁰` the minimum distance to `Z⁰` is attained and
positive, so this is `‖d₀ϕ‖ / min_ψ dist(ϕ, ψ) ≥ β`; for `ϕ ∈ Z⁰` it holds with `ψ = ϕ`.) -/
def HZeroGe (Λ : Type*) [Group Λ] (β : ℝ) : Prop :=
  ∀ ϕ : V → Λ, ∃ ψ : V → Λ, X.IsZ0 ψ ∧ β * X.dist0 ϕ ψ ≤ X.normD0 ϕ

/-- `h¹(X, Λ) ≥ β` (Definition 2.8), in ratio-free form: every 1-cochain `ϕ` has a 1-cocycle
`ψ` with `β · dist(ϕ, ψ) ≤ ‖d₁ϕ‖`. -/
def HOneGe (Λ : Type*) [Group Λ] (β : ℝ) : Prop :=
  ∀ ϕ : V → V → Λ, X.IsC1 ϕ → ∃ ψ : V → V → Λ, X.IsZ1 ψ ∧ β * X.dist1 ϕ ψ ≤ X.normD1 ϕ

/-- `X` is a `(Λ, β)` 1-coboundary expander (Definition 2.9): `h⁰(X, Λ) ≥ β`, `h¹(X, Λ) ≥ β`
and `H¹(X, Λ)` is trivial. -/
def IsCoboundaryExpander (Λ : Type*) [Group Λ] (β : ℝ) : Prop :=
  X.HZeroGe Λ β ∧ X.HOneGe Λ β ∧ X.H1Trivial Λ

/-- `X` is a `(β, r, Λ)`-swap coboundary expander (Definition 2.12): its `r`-faces complex
`F^r X` is a `(Λ, β)` 1-coboundary expander. -/
def IsSwapCoboundaryExpander (β : ℝ) (r : ℕ) (Λ : Type*) [Group Λ] : Prop :=
  (X.facesComplex r).IsCoboundaryExpander Λ β

end WComplex

end PolySwap.KMS


