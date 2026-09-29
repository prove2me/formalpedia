-- Prove2me | Definitions.Def_AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum
-- name    : AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/8f6db9b2-4af8-5ff1-82c5-bfadad92c06b
-- title:
--   Affine fibre of a Spec map: tensor model and stalks
-- statement:
--   Fix commutative rings $R$, $S$ with an $R$-algebra structure on $S$, and write $f = \mathrm{Spec}(R \to S)$ for the induced morphism of schemes. For a prime $\mathfrak p$ of $R$, [`kmf2_fiberSpecTensorIso`](../def/AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum.html#L13) is an isomorphism of schemes
--   $$f^{-1}(\mathfrak p) \;\cong\; \mathrm{Spec}\bigl(\kappa(\mathfrak p) \otimes_R S\bigr),$$
--   where the left side is Mathlib's scheme-theoretic fibre of $f$ over the point $\mathfrak p$ (the pullback of $f$ along the canonical morphism from the spectrum of the residue field at $\mathfrak p$) and the right side is the spectrum of `p.asIdeal.Fiber S`, the base change of $S$ to the residue field $\kappa(\mathfrak p)$. It is assembled from the symmetry of the pullback, the comparison between the residue field of the local ring at $\mathfrak p$ and the residue field attached to $\mathfrak p$, and Mathlib's identification of a pullback of affine spectra with the spectrum of a tensor product.
--
--   Three compatibility statements accompany it. [`kmf2_fiberSpecTensorIso_hom_includeRight`](../def/AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum.html#L26) asserts that the isomorphism followed by $\mathrm{Spec}$ of the right inclusion $S \to \kappa(\mathfrak p) \otimes_R S$ is the canonical morphism from the fibre to $\mathrm{Spec}(S)$; [`kmf2_fiberSpecTensorIso_point_comap`](../def/AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum.html#L38) is its pointwise consequence, that for a point $w$ of the fibre the prime of $\kappa(\mathfrak p) \otimes_R S$ corresponding to $w$ contracts along the right inclusion to the prime of $S$ underlying $w$. [`kmf2_fiberStalk_localizationAtPrime`](../def/AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum.html#L55) records the existence (as a `Nonempty` claim, not a chosen isomorphism) of a ring isomorphism between the stalk of the fibre at $w$ and the localisation of $\kappa(\mathfrak p) \otimes_R S$ at that prime.
--
--   Finally, [`kmf2_fiberStalkLeg1_affineDatum`](../def/AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum.html#L65) packages this for a point $x$ of $\mathrm{Spec}(S)$ with image $y = f(x)$: there is a prime ideal $Q$ of $\kappa(y) \otimes_R S$ whose contraction along $S \to \kappa(y) \otimes_R S$ is the prime of $x$, together with a ring isomorphism between the stalk of $f^{-1}(y)$ at the canonical fibre point above $x$ and the localisation of $\kappa(y) \otimes_R S$ at $Q$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`, `Scheme.Hom.asFiber`, `Ideal.ResidueField`, `Ideal.Fiber` and `pullbackSpecIso`; Mathlib has no description of the stalks of `Scheme.Hom.fiber`, which is what these declarations provide in the affine case.
--
--   **Where it is used.** This supplies the affine local model for fibres of a morphism of schemes: the fibre over a point is the spectrum of the base change to the residue field, and its stalks are localisations of that base change. It is used as the affine input to the geometric fibre-and-stalk arguments about moduli of elliptic curves that enter the modularity side of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable def kmf2_fiberSpecTensorIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p ≅
      Spec (CommRingCat.of (p.asIdeal.Fiber S)) :=
  pullbackSymmetry _ _ ≪≫
    (pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
        (CommRingCat.of R) p).symm rfl ≪≫
      asIso (pullback.map _ _ _ _
        (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv) (𝟙 _) (𝟙 _)
        (by simp) (by simp))) ≪≫
    pullbackSpecIso R p.asIdeal.ResidueField S

theorem kmf2_fiberSpecTensorIso_hom_includeRight
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (kmf2_fiberSpecTensorIso R S p).hom ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight
            (R := R) (A := p.asIdeal.ResidueField) (B := S)))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p := by
  simp only [kmf2_fiberSpecTensorIso, Scheme.Hom.fiberι, Iso.trans_hom, asIso_hom,
    pullback.congrHom_hom, Category.assoc, pullbackSpecIso_hom_snd,
    pullback.lift_snd, Category.comp_id]
  exact pullbackSymmetry_hom_comp_snd _ _

theorem kmf2_fiberSpecTensorIso_point_comap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R)
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) :
    (((kmf2_fiberSpecTensorIso R S p).hom w).asIdeal).comap
        (Algebra.TensorProduct.includeRight
          (R := R) (A := p.asIdeal.ResidueField) (B := S)).toRingHom =
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p w).asIdeal := by
  have h1 : Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := R) (A := p.asIdeal.ResidueField) (B := S))))
        ((kmf2_fiberSpecTensorIso R S p).hom w) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p w := by
    rw [← Scheme.Hom.comp_apply, kmf2_fiberSpecTensorIso_hom_includeRight]
  have h2 := congrArg PrimeSpectrum.asIdeal h1
  rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom] at h2
  exact h2

theorem kmf2_fiberStalk_localizationAtPrime
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R)
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) :
    Nonempty
      (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p).presheaf.stalk w ≃+*
        Localization.AtPrime ((kmf2_fiberSpecTensorIso R S p).hom w).asIdeal) :=
  ⟨(asIso ((kmf2_fiberSpecTensorIso R S p).hom.stalkMap w)).commRingCatIsoToRingEquiv.symm.trans
    ((StructureSheaf.stalkIso (p.asIdeal.Fiber S)
      ((kmf2_fiberSpecTensorIso R S p).hom w)).symm.toRingEquiv)⟩

theorem kmf2_fiberStalkLeg1_affineDatum
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (x : Spec (CommRingCat.of S)) :
    ∃ (Q : Ideal ((Spec.map (CommRingCat.ofHom (algebraMap R S))
        x).asIdeal.Fiber S)) (_ : Q.IsPrime),
      Q.comap (Algebra.TensorProduct.includeRight
        (R := R)
        (A := (Spec.map (CommRingCat.ofHom (algebraMap R S)) x).asIdeal.ResidueField)
        (B := S)).toRingHom = x.asIdeal ∧
      Nonempty
        (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber
            (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x) ≃+*
          Localization.AtPrime Q) := by
  refine ⟨((kmf2_fiberSpecTensorIso R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).asIdeal,
    ((kmf2_fiberSpecTensorIso R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).2, ?_, ?_⟩
  · rw [kmf2_fiberSpecTensorIso_point_comap]
    rw [Scheme.Hom.fiberι_asFiber]
  · exact kmf2_fiberStalk_localizationAtPrime R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)

/--
info: 'kmf2_fiberSpecTensorIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberSpecTensorIso

/--
info: 'kmf2_fiberSpecTensorIso_hom_includeRight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberSpecTensorIso_hom_includeRight

/--
info: 'kmf2_fiberSpecTensorIso_point_comap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberSpecTensorIso_point_comap

/--
info: 'kmf2_fiberStalk_localizationAtPrime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberStalk_localizationAtPrime

/--
info: 'kmf2_fiberStalkLeg1_affineDatum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberStalkLeg1_affineDatum

end


