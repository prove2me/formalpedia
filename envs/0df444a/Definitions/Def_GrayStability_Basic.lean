-- Prove2me | Definitions.Def_GrayStability_Basic
-- name    : GrayStability_Basic
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-05T18:36:34.296654+00:00
-- url     : https://prove2.me/theorems/1ed89815-b491-4e2b-b5ae-afcf9370f16c
-- title:
--   Contact forms on compact submanifolds of $\mathbb{R}^n$, isotopies, pull-backs
-- statement:
--   Objects for Gray's stability theorem on a closed manifold realized in $\mathbb{R}^n$.
--
--   1. **Closed submanifold.** For a smooth $F:\mathbb{R}^n\to\mathbb{R}^c$, the set $M=F^{-1}(0)$ is a compact regular level if it is compact and $DF(y)$ is surjective for every $y\in M$. Its tangent space is $T_yM=\ker DF(y)$.
--   2. **One-forms.** A one-form is a map $\alpha:\mathbb{R}^n\to(\mathbb{R}^n)^*$. Its exterior derivative is
--   $$d\alpha_y(u,v)=D\alpha_y(u)(v)-D\alpha_y(v)(u).$$
--   On $T_yM$ this is the exterior derivative of the restriction $\alpha|_M$.
--   3. **Contact form.** $\alpha$ is a contact form at $y\in M$ if $\alpha_y\neq0$ on $T_yM$ and $d\alpha_y$ is non-degenerate on the hyperplane $\xi_y=T_yM\cap\ker\alpha_y$: every nonzero $u\in\xi_y$ has some $v\in\xi_y$ with $d\alpha_y(u,v)\neq0$. This is the condition $\alpha\wedge(d\alpha)^k\neq0$ in the form of Geiges' Remark 2.3; the contact structure is $\xi=\ker\alpha$, cooriented by $\alpha$.
--   4. **Families.** A family $\alpha_t$ is smooth if $(t,y)\mapsto\alpha_t(y)$ is smooth on $\mathbb{R}\times\mathbb{R}^n$. It is a family of contact forms on $M$ if each $\alpha_t$, $t\in[0,1]$, is a contact form at every point of $M$.
--   5. **Isotopy.** $\psi:\mathbb{R}\times\mathbb{R}^n\to\mathbb{R}^n$ is an isotopy of $M$ if it is jointly smooth, $\psi_0=\mathrm{id}$ on $M$, and for every $t\in[0,1]$ the map $\psi_t$ sends $M$ bijectively onto $M$ with $D\psi_t(y)$ injective on $T_yM$.
--   6. **Pull-back, time derivative, Lie derivative.** $(\psi^*\alpha)_y(v)=\alpha_{\psi(y)}(D\psi(y)v)$; $\dot\alpha_t(y)(v)=\partial_t\big(\alpha_t(y)(v)\big)$; and for a vector field $X$,
--   $$(\mathcal{L}_X\eta)_y(v)=D\eta_y(X(y))(v)+\eta_y(DX(y)v).$$
--
--   These are the notions in which Theorem 2.20 (Gray stability), its proof, and Lemma 2.19 are stated.
--
--   **Formalization Note** $\mathbb{R}^n$ is `Fin n → ℝ`. Forms are ambient (defined on all of $\mathbb{R}^n$); only their restrictions to $TM$ enter the statements.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, Section 2 (p. 4, cooriented contact structures; Definition 2.1; Remark 2.3), Definition 2.5, Lemma 2.19, Theorem 2.20

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Contact forms on compact submanifolds of `ℝⁿ`, isotopies, pull-backs

Objects for Gray's stability theorem in the form of Geiges, *Contact geometry*,
Handbook of Differential Geometry II (2006), arXiv:math/0307242, §2 and §2.2
(Definition 2.1, Remark 2.3, Definition 2.5, Lemma 2.19, Theorem 2.20, Remark 2.21).

The closed manifold `M` is a compact regular level set `F⁻¹(0)` of a smooth map
`F : ℝⁿ → ℝᶜ`, with tangent spaces `T_y M = ker DF(y)`. One-forms on `M` are
restrictions of ambient one-forms `α : ℝⁿ → (ℝⁿ →L ℝ)`; contact structures are
cooriented, `ξ = ker α` (Geiges' standing assumption, §2, p. 4).
-/

namespace GrayStability

noncomputable section

open scoped ContDiff

/-- `ℝⁿ` as `Fin n → ℝ`. -/
abbrev E (n : ℕ) := Fin n → ℝ

/-- A one-form on `ℝⁿ`: a covector at every point. -/
abbrev OneForm (n : ℕ) := E n → (E n →L[ℝ] ℝ)

variable {n c : ℕ}

/-- The level set `M = F⁻¹(0)`. -/
def levelSet (F : E n → (Fin c → ℝ)) : Set (E n) := {y | F y = 0}

/-- `M = F⁻¹(0)` is a closed (compact, boundaryless) smooth submanifold of `ℝⁿ`:
`F` is smooth, `M` is compact, and `DF(y)` is surjective at every `y ∈ M`. -/
def IsCompactRegularLevel (F : E n → (Fin c → ℝ)) : Prop :=
  ContDiff ℝ ∞ F ∧ IsCompact (levelSet F) ∧
    ∀ y ∈ levelSet F, Function.Surjective (fderiv ℝ F y)

/-- The tangent space `T_y M = ker DF(y)`. -/
def tangentSpace (F : E n → (Fin c → ℝ)) (y : E n) : Set (E n) :=
  {v | fderiv ℝ F y v = 0}

/-- The exterior derivative of an ambient one-form:
`dα_y(u, v) = Dα_y(u)(v) - Dα_y(v)(u)`. Its restriction to `T_y M` is the exterior
derivative of `α|_M`. -/
def extDerivOneForm (α : OneForm n) (y u v : E n) : ℝ :=
  fderiv ℝ α y u v - fderiv ℝ α y v u

/-- The contact hyperplane `ξ_y = T_y M ∩ ker α_y`. -/
def contactPlane (F : E n → (Fin c → ℝ)) (α : OneForm n) (y : E n) : Set (E n) :=
  {v | v ∈ tangentSpace F y ∧ α y v = 0}

/-- `α|_M` is a contact form at `y` (Definition 2.1, in the equivalent form of
Remark 2.3): `α_y` does not vanish on `T_y M`, and `dα_y` is non-degenerate on
`ξ_y = T_y M ∩ ker α_y`. -/
def IsContactFormAt (F : E n → (Fin c → ℝ)) (α : OneForm n) (y : E n) : Prop :=
  (∃ v ∈ tangentSpace F y, α y v ≠ 0) ∧
    ∀ u ∈ contactPlane F α y, u ≠ 0 →
      ∃ v ∈ contactPlane F α y, extDerivOneForm α y u v ≠ 0

/-- A smooth family of one-forms: `(t, y) ↦ α_t(y)` is smooth on `ℝ × ℝⁿ`. -/
def IsSmoothFamily (α : ℝ → OneForm n) : Prop :=
  ContDiff ℝ ∞ (fun p : ℝ × E n => α p.1 p.2)

/-- A smooth family of contact forms on `M`, `t ∈ [0, 1]`. -/
def IsContactFamilyOn (F : E n → (Fin c → ℝ)) (α : ℝ → OneForm n) : Prop :=
  IsSmoothFamily α ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, IsContactFormAt F (α t) y

/-- An isotopy `(ψ_t)_{t ∈ [0,1]}` of `M`: `(t, y) ↦ ψ_t(y)` is smooth, `ψ_0 = id`
on `M`, and each `ψ_t` maps `M` bijectively onto `M` with injective differential on
`T_y M` (so `ψ_t|_M` is a diffeomorphism of `M`). -/
def IsIsotopyOf (F : E n → (Fin c → ℝ)) (ψ : ℝ → E n → E n) : Prop :=
  ContDiff ℝ ∞ (fun p : ℝ × E n => ψ p.1 p.2) ∧
    (∀ y ∈ levelSet F, ψ 0 y = y) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Set.BijOn (ψ t) (levelSet F) (levelSet F) ∧
      ∀ y ∈ levelSet F, Set.InjOn (fderiv ℝ (ψ t) y) (tangentSpace F y)

/-- The pull-back `(ψ^* α)_y(v) = α_{ψ(y)}(Dψ_y v)`. -/
def pullback (ψ : E n → E n) (α : OneForm n) (y v : E n) : ℝ :=
  α (ψ y) (fderiv ℝ ψ y v)

/-- The time derivative `α̇_t(y)(v) = ∂/∂t (α_t(y)(v))`. -/
def formTimeDeriv (α : ℝ → OneForm n) (t : ℝ) (y v : E n) : ℝ :=
  deriv (fun s => α s y v) t

/-- The Lie derivative of a one-form along a vector field on `ℝⁿ`:
`(L_X η)_y(v) = Dη_y(X(y))(v) + η_y(DX_y v)`. -/
def lieDerivOneForm (X : E n → E n) (η : OneForm n) (y v : E n) : ℝ :=
  fderiv ℝ η y (X y) v + η y (fderiv ℝ X y v)

end

end GrayStability


