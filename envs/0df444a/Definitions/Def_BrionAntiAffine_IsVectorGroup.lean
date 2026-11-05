-- Prove2me | Definitions.Def_BrionAntiAffine_IsVectorGroup
-- name    : BrionAntiAffine_IsVectorGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:28.148012+00:00
-- url     : https://prove2.me/theorems/d756f27f-308c-4eeb-a78f-fb54c83a4a03
-- title:
--   Vector groups, push-out classes and universal vector extensions
-- statement:
--   A **vector group** is a group scheme $U$ of finite type isomorphic to $\mathbb G_a^n$, i.e. with a natural isomorphism of group-valued functors $U(S)\cong\Gamma(S,\mathcal O_S)^n$. A **homomorphism** $\ell:U\to\mathbb G_a$ is an additive natural family $\ell_S:U(S)\to\Gamma(S,\mathcal O_S)$.
--
--   For an extension $0\to U\xrightarrow{i}G\xrightarrow{\alpha}A\to 0$ and $\ell:U\to\mathbb G_a$, a class $u\in H^1(A,\mathcal O_A)$ is the **class of the push-out along $\ell$** if there are local sections $s_W$ of $\alpha$ over the affine opens $W$ of $A$, and $d_{WW'}\in U(W\cap W')$ with
--
--   $$i(d_{WW'})=s_W^{-1}\,s_{W'}\quad\text{on }W\cap W',$$
--
--   such that $(\ell(d_{WW'}))$ is a cocycle representing $u$.
--
--   A pair $(\gamma,\varphi)$ **fills the diagram (2.4)** if $\gamma:V\to U$ and $\varphi:E\to G$ are homomorphisms making both squares commute. An extension $0\to V\to E\to A\to 0$ of $A$ by a vector group is a **universal vector extension** if every extension of $A$ by a vector group receives exactly one such pair.
--
--   **Formalization Note** The push-out class is the classical map $U^*\to H^1(A,\mathcal O_A)$ (Serre, *Groupes algébriques et corps de classes*, VII.17); it is what identifies the kernel of $E(A)$ with $H^1(A,\mathcal O_A)^*$. Local sections exist since a torsor under a vector group is trivial over an affine base.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, §2.2, p.8, (2.4); Proposition 2.3, proof, p.9

import Mathlib
import Definitions.Def_BrionAntiAffine_IsExactSeq
import Definitions.Def_BrionAntiAffine_CechH1

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- A trivialization of `U` as a vector group: a natural isomorphism of group-valued functors between
`S ↦ U(S)` and `S ↦ Γ(S, ⊤)ⁿ`, i.e. `U ≅ 𝔾ₐⁿ`. -/
structure VectorTrivialization (U : Sch k) [GrpObj U] (n : ℕ) where
  /-- The bijection on `S`-points. -/
  e : ∀ S : Sch k, (S ⟶ U) ≃ (Fin n → Γ(S.left, ⊤))
  map_mul : ∀ (S : Sch k) (x y : S ⟶ U), e S (x * y) = e S x + e S y
  natural : ∀ (S S' : Sch k) (f : S' ⟶ S) (x : S ⟶ U) (j : Fin n),
    e S' (f ≫ x) j = f.left.appTop.hom (e S x j)

/-- `U` is a vector group: isomorphic to `𝔾ₐⁿ` for some `n`, and of finite type. Brion,
arXiv:0710.5211v3, §2.2, p.8. `n = 0` is allowed. -/
def IsVectorGroup (U : Sch k) [GrpObj U] : Prop :=
  IsFiniteTypeOver U ∧ ∃ n : ℕ, Nonempty (VectorTrivialization U n)

/-- A family `ℓ_S : U(S) → Γ(S, ⊤)` is a homomorphism of group schemes `ℓ : U → 𝔾ₐ`, by Yoneda: it is
additive and natural in `S`. In characteristic `0` these form the dual `U^*` of a vector group `U`. -/
structure IsGaHom {U : Sch k} [GrpObj U] (l : ∀ S : Sch k, (S ⟶ U) → Γ(S.left, ⊤)) : Prop where
  map_mul : ∀ (S : Sch k) (x y : S ⟶ U), l S (x * y) = l S x + l S y
  natural : ∀ (S S' : Sch k) (f : S' ⟶ S) (x : S ⟶ U), l S' (f ≫ x) = f.left.appTop.hom (l S x)

/-- An open subscheme of a `k`-scheme, as a `k`-scheme. -/
def overOf (A : Sch k) (W : A.left.Opens) : Sch k := Over.mk (W.ι ≫ A.hom)

/-- The inclusion of an open subscheme, as a `k`-morphism. -/
def overIncl (A : Sch k) (W : A.left.Opens) : overOf A W ⟶ A := Over.homMk W.ι

/-- The inclusion of a smaller open subscheme, as a `k`-morphism. -/
def overLE (A : Sch k) {W W' : A.left.Opens} (h : W' ≤ W) : overOf A W' ⟶ overOf A W :=
  Over.homMk (A.left.homOfLE h) (by
    change A.left.homOfLE h ≫ W.ι ≫ A.hom = W'.ι ≫ A.hom
    rw [Scheme.homOfLE_ι_assoc])

/-- `u ∈ H¹(A, 𝒪_A)` is the class of the push-out along `ℓ : U → 𝔾ₐ` of the extension
`0 → U → G → A → 0`: there are local sections `s_W` of `α` over the affine opens `W` of `A` such that
`s_{W'} - s_W` on `W ∩ W'` is `i(d_{W W'})` with `d_{W W'} ∈ U(W ∩ W')`, and `(ℓ(d_{W W'}))` is a
cocycle representing `u`. This is the map `U^* → H¹(A, 𝒪_A)` of Serre, *Groupes algébriques et corps
de classes*, VII.17, by which Brion, arXiv:0710.5211v3, §2.2, p.8, identifies the kernel of `E(A)`
with `H¹(A, 𝒪_A)^*`. -/
def IsExtensionClass {U G A : Sch k} [GrpObj U] [GrpObj G] (i : U ⟶ G) (α : G ⟶ A)
    (l : ∀ S : Sch k, (S ⟶ U) → Γ(S.left, ⊤)) (u : CechH1 A) : Prop :=
  ∃ g : Z1 A, CechH1.mk g = u ∧
    ∃ s : ∀ W : A.left.affineOpens, overOf A W.1 ⟶ G,
      (∀ W, s W ≫ α = overIncl A W.1) ∧
      ∃ d : ∀ W W' : A.left.affineOpens, overOf A (W.1 ⊓ W'.1) ⟶ U,
        (∀ W W', d W W' ≫ i =
          (overLE A (inf_le_left : W.1 ⊓ W'.1 ≤ W.1) ≫ s W)⁻¹ *
            (overLE A (inf_le_right : W.1 ⊓ W'.1 ≤ W'.1) ≫ s W')) ∧
        ∀ W W', g.1 W W' = (W.1 ⊓ W'.1).topIso.hom.hom (l _ (d W W'))

/-- The pair `(γ, φ)` fills the diagram (2.4) of Brion, arXiv:0710.5211v3, p.8: both are
homomorphisms, the left square commutes, and `φ` is compatible with the maps to `A`. -/
structure FillsDiagram {V E U G A : Sch k} [GrpObj V] [GrpObj E] [GrpObj U] [GrpObj G]
    (iE : V ⟶ E) (βE : E ⟶ A) (iG : U ⟶ G) (αG : G ⟶ A) (c : V ⟶ U) (φ : E ⟶ G) : Prop where
  isMonHom_c : IsMonHom c
  isMonHom_φ : IsMonHom φ
  left_comm : c ≫ iG = iE ≫ φ
  right_comm : φ ≫ αG = βE

/-- `0 → V → E → A → 0` is a universal vector extension of `A`, Brion, arXiv:0710.5211v3, §2.2, p.8:
it is a vector extension and any extension of `A` by a vector group fits into a unique commutative
diagram (2.4). -/
def IsUniversalVectorExtension {V E A : Sch k} [GrpObj V] [GrpObj E] [GrpObj A]
    (iE : V ⟶ E) (βE : E ⟶ A) : Prop :=
  IsVectorGroup V ∧ IsExactSeq iE βE ∧
    ∀ (U G : Sch k) [GrpObj U] [GrpObj G] (iG : U ⟶ G) (αG : G ⟶ A),
      IsVectorGroup U → IsExactSeq iG αG →
        ∃! p : (V ⟶ U) × (E ⟶ G), FillsDiagram iE βE iG αG p.1 p.2

/-- `G` over `A` has vector kernel: `G` is a vector extension of `A`. Brion, arXiv:0710.5211v3,
Proposition 2.3(iii), p.8. -/
def HasVectorKernel {A : Sch k} [GrpObj A] (G : AntiAffineOver A) : Prop :=
  ∃ (U : Sch k) (_ : GrpObj U) (i : U ⟶ G.G), IsVectorGroup U ∧ IsExactSeq i G.α

end BrionAntiAffine


