-- Prove2me | Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
-- name    : AlgebraicGeometry_TangentCoordsOfPair
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/6cec1389-f912-5b80-94cf-a8a3ff07d0e5
-- title:
--   Translating relative tangent points; tangent coordinates of a pair
-- statement:
--   The first half works over a field $k$ with a scheme $X$, a structure morphism $x\colon X\to\operatorname{Spec}k$ and a relative group law $L$ on $x$ (a functorial group structure on the sets $\{\varphi\colon T\to X\mid \varphi\circ t=x\}$ of $X$-points over each $t\colon T\to\operatorname{Spec}k$, with naturality in $T$). Given a $k$-vector space $V$ with compatible left and right actions, an affine-type base $f_0\colon Z_0\to\operatorname{Spec}k$ and a cartesian square exhibiting $Z$ as $Z_0\times_{\operatorname{Spec}k}\operatorname{Spec}(k\oplus V)$ (the square-zero scheme $\operatorname{Spec}$ of `TrivSqZeroExt k V`), `base` is the composite $Z\to\operatorname{Spec}(k\oplus V)\to\operatorname{Spec}k$; two identities record that the zero section $Z_0\to Z$ and its composite with $q_1$ are compatible with this base. For an arbitrary $w_0\colon Z\to X$ over $\operatorname{Spec}k$, `translate` is the product, in the group of $X$-points over `base`, of the inverse of $q_1$ followed by the zero section followed by $w_0$ with $w_0$ itself; it is shown to lie in `RelTangentPoints`, i.e. to restrict along the zero section to the constant map given by the unit section $(L.one\,(\mathbb 1))$ of $L$.
--
--   The second half fixes a local ring $T'$ with residue field $k$, an ideal $I$, a $k$-space $V$ that is also a $T'$-module with $\iota\colon V\to T'$ $T'$-linear, and a $T'$-algebra $C$. With `thickening T' V C` $=(k\otimes_{T'}C)\otimes_k(k\oplus V)$, the maps `reductionBase`, `thickeningFst` and `thickeningSnd` are the $\operatorname{Spec}$ of the evident inclusions, and `thickening_isPullback` asserts that they form a cartesian square over $\operatorname{Spec}(k\oplus V)\to\operatorname{Spec}k$, deduced from the pushout property of tensor products of commutative rings. Finally, for $u,v\colon\operatorname{Spec}C\to Y$, a $k$-scheme $x_k\colon A_k\to\operatorname{Spec}k$ with relative group law $L_k$ and unit point $e$ (the image of the closed point under the unit section), a morphism $a_k\colon A_k\to Y$, a given coordinatisation $\gamma$ assigning to each finite-dimensional $W$ and each such cartesian square over an affine $Z_0$ a bijection between relative tangent points and $k$-linear maps from the cotangent space of the local ring $\mathcal O_{A_k,e}$ to $\operatorname{Hom}_k(V^{\vee}\!,\Gamma(Z_0,\top))$ — with the $k$-algebra structure on the stalk via the germ of $x_k$ at $e$ and the $k$-module structure on $\Gamma(Z_0,\top)$ via $f_0$ — and a candidate element $c$ of the target for $W=V$ and $Z_0=\operatorname{Spec}(k\otimes_{T'}C)$, the predicate `IsTangentCoordsOfPair` asserts the existence of $w_0\colon\operatorname{Spec}(\mathrm{thickening})\to A_k$ over $\operatorname{Spec}k$ such that $w_0$ followed by $a_k$ is a tangent morphism of the pair $(u,v)$ in the sense of `IsTangentOfPair` (factorisation through $\operatorname{Spec}$ of the ring of pairs congruent modulo $I\cdot C$, along a ring map satisfying the two normalisation identities of `IsSchlessingerMap`), and such that $c$ is the value of $\gamma$ on the translate of $w_0$. Thus it is a predicate relating a chosen coordinate datum $c$ to the pair $(u,v)$ through a chosen lift $w_0$, not a construction of $c$.
--
--   **Relation to Mathlib.** The square-zero thickenings are built from Mathlib's `TrivSqZeroExt`, the cotangent space is Mathlib's `IsLocalRing.CotangentSpace`, and the cartesian square comes from Mathlib's identification of tensor products with pushouts in `CommRingCat`. Relative group laws given by functorial group structures on points, relative tangent points over a square-zero base change, and the tangent-of-a-pair predicate have no Mathlib counterpart and are the project's own.
--
--   **Where it is used.** This vocabulary serves the deformation-theoretic analysis of group schemes and their Néron models over small extensions of a local ring: two morphisms $u,v$ out of an affine chart that agree modulo a small ideal $I$ differ by a tangent morphism, and translating it to the unit section of the group law converts it into linear-algebra data on the cotangent space at the identity with values in functions on the reduction. It is the dictionary by which re-gluing data for an abelian scheme acquire Čech cohomology classes in the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TangentCoordsOfPair.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace RelTangentPoints

variable {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
  (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))

abbrev base : Z ⟶ Spec (CommRingCat.of k) := q₂ ≫ SquareZero.toBase k V

theorem zeroSection_base : SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ base V q₂ = f₀ := by
  rw [base, SquareZero.zeroSection_snd_assoc, SquareZero.basePoint_toBase, Category.comp_id]

theorem fst_zeroSection_base : (q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ) ≫ base V q₂ = base V q₂ := by
  rw [Category.assoc, zeroSection_base]; exact hZ.w

def translate (w₀ : Z ⟶ X) (hw₀ : w₀ ≫ x = base V q₂) :
    RelTangentPoints x (L.one (𝟙 (Spec (CommRingCat.of k)))).1 V f₀ q₁ q₂ hZ :=
  ⟨(L.mul (base V q₂)
      (L.inv (base V q₂) ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, by
        rw [Category.assoc, Category.assoc, hw₀, ← Category.assoc]; exact fst_zeroSection_base V f₀ q₁ q₂ hZ⟩)
      ⟨w₀, hw₀⟩).1, by
    constructor
    · exact (L.mul (base V q₂) _ _).2
    ·
      have hψ : SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ base V q₂ = f₀ := zeroSection_base V f₀ q₁ q₂ hZ
      set A : SchemeHomOver (base V q₂) x := ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, by
          rw [Category.assoc, Category.assoc, hw₀, ← Category.assoc]; exact fst_zeroSection_base V f₀ q₁ q₂ hZ⟩ with hA
      set W : SchemeHomOver (base V q₂) x := ⟨w₀, hw₀⟩ with hW
      have hsame : schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A
          = schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ W := by
        apply Subtype.ext
        simp only [schemeHomOverComp_coe, hA, hW]
        rw [← Category.assoc, ← Category.assoc, SquareZero.zeroSection_fst, Category.id_comp]

      have hprod : L.mul f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A))
          (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A) = L.one f₀ := by
        rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
      have hinvnat : schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A)
          = L.inv f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A) := by
        calc schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A)
            = L.mul f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A)) (L.one f₀) :=
              (L.mul_one f₀ _).symm
          _ = L.mul f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A))
                (L.mul f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A)
                  (L.inv f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A))) := by
              rw [L.mul_inv_cancel]
          _ = L.mul f₀ (L.one f₀) (L.inv f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A)) := by
              rw [← L.mul_assoc, hprod]
          _ = L.inv f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A) := L.one_mul f₀ _
      have h1 : (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ
          (L.mul (base V q₂) (L.inv (base V q₂) A) W)).1 = (L.one f₀).1 := by
        rw [L.mul_natural, hinvnat, hsame, L.inv_mul_cancel]
      have h2 : (L.one f₀).1 = f₀ ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 := by
        have := L.one_natural (𝟙 (Spec (CommRingCat.of k))) f₀ f₀ (Category.comp_id f₀)
        rw [← this, schemeHomOverComp_coe]
      rw [← h2, ← h1, schemeHomOverComp_coe]⟩

@[simp] theorem translate_coe (w₀ : Z ⟶ X) (hw₀ : w₀ ≫ x = base V q₂) :
    (translate x L V f₀ q₁ q₂ hZ w₀ hw₀).1 =
      (L.mul (base V q₂)
        (L.inv (base V q₂) ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, by
          rw [Category.assoc, Category.assoc, hw₀, ← Category.assoc]; exact fst_zeroSection_base V f₀ q₁ q₂ hZ⟩)
        ⟨w₀, hw₀⟩).1 := rfl

end RelTangentPoints

namespace SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

abbrev reductionBase : Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)) ⟶ Spec (CommRingCat.of (ResidueField T')) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C)))

variable (T') in

abbrev thickeningFst :
    Spec (CommRingCat.of (thickening T' V C)) ⟶ Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom))

variable (T') in

abbrev thickeningSnd : Spec (CommRingCat.of (thickening T' V C)) ⟶ SquareZero.spec (ResidueField T') V :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
      (B := TrivSqZeroExt (ResidueField T') V)).toRingHom)

theorem thickening_isPullback :
    IsPullback (thickeningFst T' V C) (thickeningSnd T' V C) (reductionBase T' C) (SquareZero.toBase (ResidueField T') V) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (ResidueField T') (ResidueField T' ⊗[T'] C) (TrivSqZeroExt (ResidueField T') V))

def IsTangentCoordsOfPair {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y)
    (γ : letI : Algebra (ResidueField T')
          (Ak.presheaf.stalk ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T')))) :=
        ((Ak.presheaf.germ ⊤ ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T'))) trivial).hom.comp
          (xk.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom)).toAlgebra
      ∀ (W : Type u) [AddCommGroup W] [Module (ResidueField T') W] [Module (ResidueField T')ᵐᵒᵖ W]
        [IsCentralScalar (ResidueField T') W] [Module.Finite (ResidueField T') W]
        {Z₀ Z : Scheme.{u}} [IsAffine Z₀] (f₀ : Z₀ ⟶ Spec (CommRingCat.of (ResidueField T')))
        (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') W)
        (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') W)),
        letI : Module (ResidueField T') Γ(Z₀, ⊤) :=
          ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv ≫ f₀.appTop).hom.toAlgebra.toModule
        RelTangentPoints xk (Lk.one (𝟙 _)).1 W f₀ q₁ q₂ hZ ≃
          (IsLocalRing.CotangentSpace (Ak.presheaf.stalk ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T')))) →ₗ[ResidueField T']
            (Module.Dual (ResidueField T') W →ₗ[ResidueField T'] Γ(Z₀, ⊤))))
    [Module.Finite (ResidueField T') V]
    (c : letI : Algebra (ResidueField T')
          (Ak.presheaf.stalk ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T')))) :=
        ((Ak.presheaf.germ ⊤ ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T'))) trivial).hom.comp
          (xk.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom)).toAlgebra
      letI : Module (ResidueField T') Γ(Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)), ⊤) :=
        ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv ≫ (reductionBase T' C).appTop).hom.toAlgebra.toModule
      IsLocalRing.CotangentSpace (Ak.presheaf.stalk ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T')))) →ₗ[ResidueField T']
        (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] Γ(Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)), ⊤))) : Prop :=
  ∃ (w₀ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak)
    (hw₀ : w₀ ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C)),
    IsTangentOfPair I V ι C u v (w₀ ≫ ak) ∧
    c = γ V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
          (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
            (thickening_isPullback V C) w₀ hw₀)

end SmallExtension

end AlgebraicGeometry

end


