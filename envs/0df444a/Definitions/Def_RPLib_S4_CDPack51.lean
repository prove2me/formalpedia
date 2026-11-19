-- Prove2me | Definitions.Def_RPLib_S4_CDPack51
-- name    : RPLib_S4_CDPack51
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:59:03.641082+00:00
-- url     : https://prove2.me/theorems/94b454b7-508c-44dc-8bdc-c349a10e17b1
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 51 of 71
-- statement:
--   Part 51 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_IntersectC_Len`: S4-IntersectC, file Len: length under a finite flat endomorphism (L35, O2)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack45
import Definitions.Def_RPLib_S4_CDPack50

/-!
# Curve-duality library package, part 51 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_IntersectC_Len`: S4-IntersectC, file Len: length under a finite flat endomorphism (L35, O2)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_IntersectC_Len =====
section

/-!
# S4-IntersectC, file Len: length under a finite flat endomorphism (L35, O2)

* `len_comap_flat`: if `φ : A ⟶ A` over `Spec k` is finite flat of constant rank `d`, then
  pulling back a closed subscheme with finite support multiplies its length by `d`.
* `finrank_eq_of_preconnected`: the rank of a finite flat finitely presented morphism to a
  preconnected scheme is constant.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

/-- The rank of a finite flat finitely presented morphism to a preconnected scheme is constant. -/
theorem finrank_eq_of_preconnected {X Y : Scheme.{u}} (φ : X ⟶ Y) [Flat φ] [IsFinite φ]
    [LocallyOfFinitePresentation φ] [PreconnectedSpace Y] (x y : Y) :
    φ.finrank x = φ.finrank y :=
  (Scheme.Hom.isLocallyConstant_finrank φ).apply_eq_of_preconnectedSpace x y

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- (O2) Pulling back along a finite flat endomorphism of constant rank `d` over `Spec k`
multiplies the length of a closed subscheme with finite support by `d`. -/
theorem len_comap_flat [LocallyOfFiniteType A.hom] (J : A.left.IdealSheafData)
    (V : A.left.affineOpens) (hV : (J.support : Set A.left) ⊆ V)
    (hfin : (J.support : Set A.left).Finite) (φ : A.left ⟶ A.left) [Flat φ] [IsFinite φ]
    (he : φ ≫ A.hom = A.hom) (d : ℕ) (hd : ∀ x, φ.finrank x = d) :
    len A (J.comap φ) = d * len A J := by
  letI := (algV A V).hom.toAlgebra
  obtain ⟨hmf, hlen⟩ := len_eq_finrank A J V hV hfin
  let f : Spec (.of (Γ(A.left, V) ⧸ J.ideal V)) ⟶ J.subscheme := J.subschemeCover.f V
  have hfo : IsOpenImmersion f := J.subschemeCover.map_prop V
  have hf : IsIso f := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨hfo, ⟨fun z => ?_⟩⟩
    have h2 := J.opensRange_subschemeCover_map V
    have hz : z ∈ J.subschemeι ⁻¹ᵁ (V : A.left.Opens) :=
      hV (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)
    rw [← h2] at hz
    exact hz
  have hcomp : f ≫ J.subschemeι ≫ A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    have h1 : f ≫ J.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal V))) ≫
        V.2.fromSpec :=
      (J.subschemeCover_map_subschemeι V).trans (J.glueDataObjι_ι V)
    rw [← Category.assoc, h1, Category.assoc, ← algV_spec, ← Spec.map_comp]
    rfl
  have hg : J.subschemeι ≫ A.hom = inv f ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
  have hpb : IsPullback (pullback.fst φ J.subschemeι) (pullback.snd φ J.subschemeι ≫ inv f) φ
      (f ≫ J.subschemeι) :=
    (IsPullback.of_hasPullback φ J.subschemeι).of_iso (Iso.refl _) (Iso.refl _) (asIso f).symm
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have hr : ∀ x, ((J.comapIso φ).hom ≫ pullback.snd φ J.subschemeι ≫ inv f).finrank x = d := by
    intro x
    rw [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb, hd]
  have hc1 : (J.comap φ).subschemeι ≫ A.hom =
      ((J.comapIso φ).hom ≫ pullback.snd φ J.subschemeι) ≫ J.subschemeι ≫ A.hom := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst J φ]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, he]
  have hc : (J.comap φ).subschemeι ≫ A.hom =
      ((J.comapIso φ).hom ≫ pullback.snd φ J.subschemeι ≫ inv f) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    rw [hc1, hg]
    simp only [Category.assoc]
  show Scheme.Hom.finrank _ (pt0 k) = d * len A J
  rw [hlen, hc]
  exact finrank_comp_SpecMap _ d hr (pt0 k)

/-- (O2b) The rank of a finite flat endomorphism of `A` over `Spec k` (with `A` irreducible and
locally of finite type) is constant. -/
theorem finrank_const [LocallyOfFiniteType A.hom] [IrreducibleSpace A.left]
    (φ : A.left ⟶ A.left) [Flat φ] [IsFinite φ] (x y : A.left) : φ.finrank x = φ.finrank y := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  exact finrank_eq_of_preconnected φ x y

end RamanujanPetersson.IntersectC

end


