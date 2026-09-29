-- Prove2me | solution 1 for AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/80abba98-d329-52e9-9571-71d5bf61e32d

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_isPullback_adicThickening_pullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GraphKer

variable {R : Type u} [CommRing R] (I : Ideal R)

noncomputable abbrev baseStep (n : ℕ) : Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))))

scoped instance (n : ℕ) : IsClosedImmersion (adicThickeningBase I n) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem isPullback_transition {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    IsPullback (adicThickeningToBase f I n) (adicThickeningTransition f I n) (baseStep I n)
      (adicThickeningToBase f I (n + 1)) := by
  have hbot : IsPullback (adicThickeningToBase f I (n + 1)) (adicThickeningι f I (n + 1)) (adicThickeningBase I (n + 1)) f :=
    (IsPullback.of_hasPullback f (adicThickeningBase I (n + 1))).flip
  have htop : IsPullback (adicThickeningToBase f I n) (adicThickeningTransition f I n ≫ adicThickeningι f I (n + 1))
      (baseStep I n ≫ adicThickeningBase I (n + 1)) f := by
    rw [adicThickeningTransition_ι, show baseStep I n ≫ adicThickeningBase I (n + 1) = adicThickeningBase I n from
      adicThickeningBase_succ_comp I n]
    exact (IsPullback.of_hasPullback f (adicThickeningBase I n)).flip
  exact IsPullback.of_bot htop (adicThickeningTransition_toBase f I n).symm hbot

end GraphKer
p2m_reactivate "P2MW.S_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph.GraphKer"

open GraphKer in
theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated g]
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n)
    (γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n)
    (hγ₁ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n)
    (hγ₂ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g = φ n ≫ adicThickeningι g I n) :
    ∀ n : ℕ, IsClosedImmersion (γ n) ∧
      ((γ (n + 1)).ker).comap (adicThickeningTransition (pullback.fst f g ≫ f) I n) = (γ n).ker := by
  intro n

  let p : pullback f g ⟶ Spec (CommRingCat.of R) := pullback.fst f g ≫ f
  have hp : pullback.snd f g ≫ g = p := pullback.condition.symm

  have wX : ∀ m : ℕ, (adicThickeningι p I m ≫ pullback.fst f g) ≫ f = adicThickeningToBase p I m ≫ adicThickeningBase I m :=
    fun m => by rw [Category.assoc]; exact adicThickeningι_comp p I m
  have wY : ∀ m : ℕ, (adicThickeningι p I m ≫ pullback.snd f g) ≫ g = adicThickeningToBase p I m ≫ adicThickeningBase I m :=
    fun m => by rw [Category.assoc, hp]; exact adicThickeningι_comp p I m
  let prX : ∀ m : ℕ, adicThickening p I m ⟶ adicThickening f I m := fun m =>
    pullback.lift (adicThickeningι p I m ≫ pullback.fst f g) (adicThickeningToBase p I m) (wX m)
  let prY : ∀ m : ℕ, adicThickening p I m ⟶ adicThickening g I m := fun m =>
    pullback.lift (adicThickeningι p I m ≫ pullback.snd f g) (adicThickeningToBase p I m) (wY m)
  have prX₁ : ∀ m, prX m ≫ adicThickeningι f I m = adicThickeningι p I m ≫ pullback.fst f g := fun m => pullback.lift_fst _ _ _
  have prX₂ : ∀ m, prX m ≫ adicThickeningToBase f I m = adicThickeningToBase p I m := fun m => pullback.lift_snd _ _ _
  have prY₁ : ∀ m, prY m ≫ adicThickeningι g I m = adicThickeningι p I m ≫ pullback.snd f g := fun m => pullback.lift_fst _ _ _
  have prY₂ : ∀ m, prY m ≫ adicThickeningToBase g I m = adicThickeningToBase p I m := fun m => pullback.lift_snd _ _ _

  have hγb : ∀ m : ℕ, γ m ≫ adicThickeningToBase p I m = adicThickeningToBase f I m := by
    intro m
    rw [← cancel_mono (adicThickeningBase I m), Category.assoc, ← adicThickeningι_comp p I m,
      show adicThickeningι p I m ≫ p = (adicThickeningι p I m ≫ pullback.fst f g) ≫ f by rw [Category.assoc],
      ← Category.assoc, hγ₁, adicThickeningι_comp]

  have hsec : ∀ m : ℕ, γ m ≫ prX m = 𝟙 _ := by
    intro m
    apply (IsPullback.of_hasPullback f (adicThickeningBase I m)).hom_ext
    · show (γ m ≫ prX m) ≫ adicThickeningι f I m = 𝟙 _ ≫ adicThickeningι f I m
      rw [Category.assoc, prX₁, hγ₁, Category.id_comp]
    · show (γ m ≫ prX m) ≫ adicThickeningToBase f I m = 𝟙 _ ≫ adicThickeningToBase f I m
      rw [Category.assoc, prX₂, hγb, Category.id_comp]
  have hci : ∀ m : ℕ, IsClosedImmersion (γ m) := by
    intro m
    have hsq := AlgebraicGeometry.isPullback_adicThickening_pullback I f g m (prX m) (prX₁ m) (prX₂ m) (prY m) (prY₁ m) (prY₂ m)
    haveI : IsSeparated (adicThickeningToBase g I m) := by
      rw [adicThickeningToBase_def]; exact MorphismProperty.pullback_snd _ _ inferInstance
    haveI : IsSeparated (prX m) := MorphismProperty.of_isPullback hsq.flip inferInstance
    haveI : IsClosedImmersion (γ m ≫ prX m) := by rw [hsec]; infer_instance
    exact IsClosedImmersion.of_comp (γ m) (prX m)
  refine ⟨hci n, ?_⟩

  have hcomm : γ n ≫ adicThickeningTransition p I n = adicThickeningTransition f I n ≫ γ (n + 1) := by
    rw [← cancel_mono (adicThickeningι p I (n + 1))]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [reassoc_of% (adicThickeningTransition_ι p I n), hγ₁, hγ₁, adicThickeningTransition_ι]
    · simp only [Category.assoc]
      rw [reassoc_of% (adicThickeningTransition_ι p I n), hγ₂, hγ₂ (n + 1), reassoc_of% (hφt n),
        adicThickeningTransition_ι]

  have hcart : IsPullback (γ n) (adicThickeningTransition f I n) (adicThickeningTransition p I n) (γ (n + 1)) := by
    refine IsPullback.of_right ?_ hcomm (isPullback_transition I p n)
    rw [hγb n, hγb (n + 1)]
    exact isPullback_transition I f n

  haveI := hci (n + 1)
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (γ (n + 1)) (adicThickeningTransition p I n),
    ← hcart.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end S_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph
end P2MW
export P2MW.S_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph (solution)
