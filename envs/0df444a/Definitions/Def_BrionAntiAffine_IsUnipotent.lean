-- Prove2me | Definitions.Def_BrionAntiAffine_IsUnipotent
-- name    : BrionAntiAffine_IsUnipotent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:35.576208+00:00
-- url     : https://prove2.me/theorems/bc363ee9-c463-4fe7-a8ed-7d898aafebdc
-- title:
--   Unipotent groups, torsors, and filtrations with trivial subquotients
-- statement:
--   A group scheme $U$ is **unipotent** if it is affine and every non-zero finite-dimensional representation has a non-zero fixed vector: for $\rho$ of size $n>0$ there is $0\ne v\in k^n$ with $\rho v=v$ over $\Gamma(U,\mathcal O_U)$.
--
--   A morphism $\pi:X\to Y$ is a **torsor** under $U$, for an action $a:U\times X\to X$, if all three are of finite type, $\pi$ is faithfully flat and quasi-compact, and
--
--   $$(a,\mathrm{pr}_2):U\times X\xrightarrow{\ \sim\ }X\times_Y X.$$
--
--   An **infinite increasing filtration with subquotients isomorphic to $\mathcal O_Y$** of a sheaf of modules $M$ on $Y$ is a family of subsheaves
--
--   $$0=F_0\subset F_1\subset F_2\subset\cdots\subset M,\qquad F_{n+1}/F_n\cong\mathcal O_Y,$$
--
--   exhausting $M$: every section of $M$ lies locally in some $F_n$.
--
--   These enter Lemma 2.6, which is used in Proposition 2.5 to compute global sections.
--
--   **Formalization Note** Over a field the fixed-vector condition is the standard characterization of unipotence, equivalent to a closed embedding into upper unitriangular matrices (Milne, *Algebraic Groups*, Ch. 14). The action is written on the left; a right action becomes a left one through the inverse. A subsheaf is a monomorphism `F n ⟶ M`, and $F_{n+1}/F_n\cong\mathcal O_Y$ is a cokernel map onto $\mathcal O_Y$.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, §2.3, p.9; Lemma 2.6, p.10

import Mathlib
import Definitions.Def_BrionAntiAffine_IsExactSeq
import Definitions.Def_BrionAntiAffine_Pic

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- `U` is unipotent: an affine group scheme such that every non-zero finite-dimensional
representation has a non-zero fixed vector `v ∈ kⁿ`, i.e. `ρ v = v` over `Γ(U, ⊤)`. Used in Brion,
arXiv:0710.5211v3, §2.3, p.9, and Lemma 2.6, p.10.

**Formalization Note.** Over a field this is the standard characterization of unipotent group schemes,
equivalent to a closed embedding into upper unitriangular matrices (Milne, *Algebraic Groups*,
Theorem 14.5). -/
structure IsUnipotent (U : Sch k) [GrpObj U] : Prop where
  isAffine : IsAffine U.left
  exists_fixed : ∀ (n : ℕ) (ρ : Matrix (Fin n) (Fin n) Γ(U.left, ⊤)), 0 < n → IsMatrixRep U n ρ →
    ∃ v : Fin n → k, v ≠ 0 ∧ ρ.mulVec (fun j => constants U (v j)) = fun j => constants U (v j)

/-- `π : X ⟶ Y` is a torsor under the group scheme `U`, for the action `a`: `π` is faithfully flat
and quasi-compact, and `(a, pr₂) : U × X → X ×_Y X` is an isomorphism. Brion, arXiv:0710.5211v3,
Lemma 2.6, p.10. All schemes are of finite type over `k` (p.3).

**Formalization Note.** The action is written on the left; a right action becomes a left one through
the inverse of `U`. -/
structure IsTorsorUnder {U X Y : Sch k} [GrpObj U] (π : X ⟶ Y) (a : U ⊗ X ⟶ X) : Prop where
  finiteType_U : IsFiniteTypeOver U
  finiteType_X : IsFiniteTypeOver X
  finiteType_Y : IsFiniteTypeOver Y
  isLeftAction : IsLeftAction a
  flat : Flat π.left
  surjective : Surjective π.left
  quasiCompact : QuasiCompact π.left
  isPullback : IsPullback a (snd U X) π π

/-- An infinite increasing filtration `0 = F₀ ⊂ F₁ ⊂ ⋯` of the sheaf of modules `M` on `Y`, exhausting
`M`, with all subquotients `F_{n+1}/F_n` isomorphic to `𝒪_Y`. Brion, arXiv:0710.5211v3, Lemma 2.6,
p.10.

**Formalization Note.** `F n ⟶ M` is a family of monomorphisms compatible with the transition maps.
Exhaustion is the sheaf-theoretic `⨆ F_n = M`: every section of `M` lies locally in some `F_n`. -/
structure IsUnitFiltration {Y : Scheme.{u}} (M : Y.Modules) (F : ℕ → Y.Modules)
    (incl : ∀ n, F n ⟶ M) (t : ∀ n, F n ⟶ F (n + 1)) : Prop where
  mono : ∀ n, Mono (incl n)
  comm : ∀ n, t n ≫ incl (n + 1) = incl n
  isZero_zero : Limits.IsZero (F 0)
  subquotient : ∀ n, ∃ (q : F (n + 1) ⟶ Pic.unitMod Y) (w : t n ≫ q = 0),
    Nonempty (IsColimit (CokernelCofork.ofπ q w))
  exhaustive : ∀ (W : Y.Opens) (f : Γ(M, W)) (y : Y), y ∈ W →
    ∃ (W' : Y.Opens) (h : W' ≤ W) (n : ℕ) (m : Γ(F n, W')), y ∈ W' ∧
      ((incl n).app W').hom m = (M.presheaf.map (homOfLE h).op).hom f

end BrionAntiAffine


