-- Prove2me | solution 1 for AlgebraicGeometry.exists_equalizerLocus_isClosedImmersion_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8bdf0fa5-9a02-5367-b8d1-b1085bfa8e35

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace EqLocus

theorem single {B X Y : Scheme.{u}} (πX : X ⟶ B) (πY : Y ⟶ B) [IsSeparated πY] (a b : X ⟶ Y)
    (ha : a ≫ πY = πX) (hb : b ≫ πY = πX) :
    ∃ (E : Scheme.{u}) (m : E ⟶ X), IsClosedImmersion m ∧ m ≫ a = m ≫ b ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ X), g ≫ a = g ≫ b → ∃! g' : T ⟶ E, g' ≫ m = g) ∧
      (LocallyOfFinitePresentation (pullback.diagonal πY) → LocallyOfFinitePresentation m) := by
  have hab : a ≫ πY = b ≫ πY := ha.trans hb.symm
  have key : pullback.fst (pullback.lift a b hab) (pullback.diagonal πY) ≫ a =
      pullback.fst (pullback.lift a b hab) (pullback.diagonal πY) ≫ b := by
    have h1 := congrArg (· ≫ pullback.fst πY πY) (pullback.condition (f := pullback.lift a b hab) (g := pullback.diagonal πY))
    have h2 := congrArg (· ≫ pullback.snd πY πY) (pullback.condition (f := pullback.lift a b hab) (g := pullback.diagonal πY))
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id] at h1 h2
    rw [h1, h2]
  refine ⟨pullback (pullback.lift a b hab) (pullback.diagonal πY), pullback.fst _ _, inferInstance, key, ?_, ?_⟩
  · intro T g hg
    have hc : g ≫ pullback.lift a b hab = (g ≫ a) ≫ pullback.diagonal πY := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hg]
    refine ⟨pullback.lift g (g ≫ a) hc, pullback.lift_fst _ _ _, ?_⟩
    intro g' hg'
    apply pullback.hom_ext
    · rw [pullback.lift_fst]; exact hg'
    · rw [pullback.lift_snd]
      have h1 := congrArg (· ≫ pullback.fst πY πY)
        (pullback.condition (f := pullback.lift a b hab) (g := pullback.diagonal πY))
      simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id] at h1
      rw [← hg', Category.assoc, h1]
  · intro hΔ
    haveI := hΔ
    infer_instance

theorem finN {B Y : Scheme.{u}} (πY : Y ⟶ B) [IsSeparated πY] (n : ℕ) :
    ∀ (X : Scheme.{u}) (πX : X ⟶ B) (a b : Fin n → (X ⟶ Y)) (_ : ∀ i, a i ≫ πY = πX) (_ : ∀ i, b i ≫ πY = πX),
    ∃ (E : Scheme.{u}) (m : E ⟶ X), IsClosedImmersion m ∧ (∀ i, m ≫ a i = m ≫ b i) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ X), (∀ i, g ≫ a i = g ≫ b i) → ∃! g' : T ⟶ E, g' ≫ m = g) ∧
      (LocallyOfFinitePresentation (pullback.diagonal πY) → LocallyOfFinitePresentation m) := by
  induction n with
  | zero =>
    intro X πX a b ha hb
    exact ⟨X, 𝟙 X, inferInstance, fun i => i.elim0, fun T g _ => ⟨g, Category.comp_id g,
      fun g' h => by simpa only [Category.comp_id] using h⟩, fun _ => inferInstance⟩
  | succ n ih =>
    intro X πX a b ha hb
    obtain ⟨E', m', hm', heq', huniv', hlfp'⟩ :=
      ih X πX (fun i => a i.succ) (fun i => b i.succ) (fun i => ha _) (fun i => hb _)
    haveI := hm'
    obtain ⟨E, m'', hm'', heq'', huniv'', hlfp''⟩ := single (m' ≫ πX) πY (m' ≫ a 0) (m' ≫ b 0)
      (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb])
    haveI := hm''
    refine ⟨E, m'' ≫ m', inferInstance, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Category.assoc] using heq''
      · rw [Category.assoc, Category.assoc, heq' j]
    · intro T g hg
      obtain ⟨g', hg', hu'⟩ := huniv' T g (fun i => hg i.succ)
      obtain ⟨g'', hg'', hu''⟩ := huniv'' T g'
        (by rw [← Category.assoc, ← Category.assoc, hg', hg 0])
      refine ⟨g'', show g'' ≫ m'' ≫ m' = g by rw [← Category.assoc, hg'', hg'], fun l hl => ?_⟩
      apply hu''
      apply hu'
      show (l ≫ m'') ≫ m' = g
      rw [Category.assoc]
      exact hl
    · intro hΔ
      haveI := hlfp' hΔ
      haveI := hlfp'' hΔ
      infer_instance

end EqLocus

theorem solution
    {B X Y : Scheme.{u}} (πX : X ⟶ B) (πY : Y ⟶ B) (hY : IsSeparated πY)
    {ι : Type v} [Fintype ι] (a b : ι → (X ⟶ Y))
    (ha : ∀ i, a i ≫ πY = πX) (hb : ∀ i, b i ≫ πY = πX) :
    ∃ (E : Scheme.{u}) (m : E ⟶ X), IsClosedImmersion m ∧
      (∀ i, m ≫ a i = m ≫ b i) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ X), (∀ i, g ≫ a i = g ≫ b i) → ∃! g' : T ⟶ E, g' ≫ m = g) ∧
      (LocallyOfFinitePresentation (pullback.diagonal πY) → LocallyOfFinitePresentation m) := by
  haveI := hY
  obtain ⟨E, m, h1, h2, h3, h4⟩ := EqLocus.finN πY (Fintype.card ι) X πX
    (fun j => a ((Fintype.equivFin ι).symm j)) (fun j => b ((Fintype.equivFin ι).symm j)) (fun j => ha _) (fun j => hb _)
  refine ⟨E, m, h1, fun i => ?_, fun T g hg => h3 T g (fun j => hg _), h4⟩
  simpa only [Equiv.symm_apply_apply] using h2 (Fintype.equivFin ι i)

end S_AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated (solution)
