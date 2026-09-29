-- Prove2me | solution 1 for AlgebraicGeometry.exists_isClosedImmersion_proj_forall_bijective_pullback_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1a74f3f5-48fc-5b9a-b6cc-ff10537b09db

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_proj_forall_bijective_pullback_points

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (Hilb : Scheme.{0}) (p : Hilb ⟶ Spec (CommRingCat.of ℤ)) (N' : ℕ)
    (ιH : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) ℤ))
    (hιH : IsClosedImmersion ιH) (hιHp : ιH ≫ ProjSpace.π ℤ N' = p)
    (B : Type) [CommRing B] (N k : ℕ) :
    ∃ (W₀ : Scheme.{0}) (πW : W₀ ⟶ Spec (CommRingCat.of B)) (M : ℕ)
      (jW : W₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) B))
      (_ : IsClosedImmersion jW) (_ : jW ≫ ProjSpace.π B M = πW)
      (prH : W₀ ⟶ Hilb)
      (prY : Fin k → (W₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B)))
      (hprY : ∀ i, prY i ≫ ProjSpace.π B N = πW),
      ∀ (R : Type) [CommRing R] [Algebra B R],
        Function.Bijective
          (fun s : {s : Spec (CommRingCat.of R) ⟶ W₀ // s ≫ πW = Spec.map (CommRingCat.ofHom (algebraMap B R))} =>
            (⟨(s.1 ≫ prH, fun i => s.1 ≫ prY i), fun i => by
                rw [Category.assoc, hprY i, s.2]⟩ :
              {y : (Spec (CommRingCat.of R) ⟶ Hilb) ×
                  (Fin k → (Spec (CommRingCat.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B))) //
                ∀ i, y.2 i ≫ ProjSpace.π B N = Spec.map (CommRingCat.ofHom (algebraMap B R))})) := by
  induction k with
  | zero =>

    let sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ B))
    have hsq := ProjSpace.isPullback_map ℤ B N'
    have w : (pullback.fst p sB ≫ ιH) ≫ ProjSpace.π ℤ N' = pullback.snd p sB ≫ sB := by
      rw [Category.assoc, hιHp]; exact pullback.condition
    let jW : pullback p sB ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) B) := hsq.lift _ _ w
    have hj₁ : jW ≫ ProjSpace.map ℤ B N' = pullback.fst p sB ≫ ιH := hsq.lift_fst _ _ w
    have hj₂ : jW ≫ ProjSpace.π B N' = pullback.snd p sB := hsq.lift_snd _ _ w
    have big : IsPullback (pullback.fst p sB) (jW ≫ ProjSpace.π B N') (ιH ≫ ProjSpace.π ℤ N') sB := by
      rw [hj₂, hιHp]; exact IsPullback.of_hasPullback p sB
    have top : IsPullback (pullback.fst p sB) jW ιH (ProjSpace.map ℤ B N') := IsPullback.of_bot big hj₁.symm hsq
    haveI : IsClosedImmersion ιH := hιH
    have hcl : IsClosedImmersion jW := MorphismProperty.of_isPullback (P := @IsClosedImmersion) top hιH
    refine ⟨pullback p sB, pullback.snd p sB, N', jW, hcl, hj₂, pullback.fst p sB, fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro R _ _
    constructor
    · rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ h
      have h1 : s₁ ≫ pullback.fst p sB = s₂ ≫ pullback.fst p sB := congrArg (fun v => v.1.1) h
      exact Subtype.ext (pullback.hom_ext h1 (hs₁.trans hs₂.symm))
    · rintro ⟨⟨h, y⟩, hy⟩
      let σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom (algebraMap B R))
      have hp : h ≫ p = σ ≫ sB := specZIsTerminal.hom_ext _ _
      refine ⟨⟨pullback.lift h σ hp, pullback.lift_snd _ _ _⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact pullback.lift_fst _ _ _
      · funext i; exact i.elim0
  | succ j ih =>
    obtain ⟨W, πW, M, jW, hjW, hjWπ, prH, prY, hprY, hbij⟩ := ih

    obtain ⟨K, ι, -, hι, hιπ⟩ :=
      AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
        πW (ProjSpace.π B N) M jW hjW hjWπ N (𝟙 _) inferInstance (Category.id_comp _)
    let prY' : Fin (j + 1) → (pullback πW (ProjSpace.π B N) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B)) :=
      Fin.snoc (α := fun _ : Fin (j + 1) => (pullback πW (ProjSpace.π B N) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B)))
        (fun i => pullback.fst πW (ProjSpace.π B N) ≫ prY i) (pullback.snd πW (ProjSpace.π B N))
    have hlast : prY' (Fin.last j) = pullback.snd πW (ProjSpace.π B N) :=
      Fin.snoc_last (α := fun _ : Fin (j + 1) => (pullback πW (ProjSpace.π B N) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B))) _ _
    have hcast : ∀ i : Fin j, prY' i.castSucc = pullback.fst πW (ProjSpace.π B N) ≫ prY i := fun i =>
      Fin.snoc_castSucc (α := fun _ : Fin (j + 1) => (pullback πW (ProjSpace.π B N) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B))) _ _ _
    refine ⟨pullback πW (ProjSpace.π B N), pullback.fst πW (ProjSpace.π B N) ≫ πW, K, ι, hι, hιπ,
      pullback.fst πW (ProjSpace.π B N) ≫ prH, prY', ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [hlast]; exact pullback.condition.symm
      · rw [hcast, Category.assoc, hprY]
    intro R _ _
    have hb := hbij R
    constructor
    · rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ h
      have hH : s₁ ≫ pullback.fst πW (ProjSpace.π B N) ≫ prH = s₂ ≫ pullback.fst πW (ProjSpace.π B N) ≫ prH := by
        simpa only using congrArg (fun v => v.1.1) h
      have hY : ∀ i : Fin (j + 1), s₁ ≫ prY' i = s₂ ≫ prY' i := fun i => by
        simpa only using congrFun (congrArg (fun v => v.1.2) h) i
      have hl := hY (Fin.last j)
      rw [hlast] at hl
      have hfst : s₁ ≫ pullback.fst πW (ProjSpace.π B N) = s₂ ≫ pullback.fst πW (ProjSpace.π B N) := by
        have hs₁' : (s₁ ≫ pullback.fst πW (ProjSpace.π B N)) ≫ πW = Spec.map (CommRingCat.ofHom (algebraMap B R)) := by
          rw [Category.assoc]; exact hs₁
        have hs₂' : (s₂ ≫ pullback.fst πW (ProjSpace.π B N)) ≫ πW = Spec.map (CommRingCat.ofHom (algebraMap B R)) := by
          rw [Category.assoc]; exact hs₂
        have key := @hb.1 ⟨_, hs₁'⟩ ⟨_, hs₂'⟩ (Subtype.ext (Prod.ext (by simpa only [Category.assoc] using hH)
          (funext fun i => by
            have := hY i.castSucc
            rw [hcast] at this
            simpa only [Category.assoc] using this)))
        exact congrArg Subtype.val key
      exact Subtype.ext (pullback.hom_ext hfst hl)
    · rintro ⟨⟨h, y⟩, hy⟩
      obtain ⟨⟨s, hs⟩, hsv⟩ := hb.2 ⟨(h, fun i => y i.castSucc), fun i => hy i.castSucc⟩
      have hsH : s ≫ prH = h := by simpa only using congrArg (fun v => v.1.1) hsv
      have hsY : ∀ i : Fin j, s ≫ prY i = y i.castSucc := fun i => by
        simpa only using congrFun (congrArg (fun v => v.1.2) hsv) i
      have hc : s ≫ πW = y (Fin.last j) ≫ ProjSpace.π B N := by rw [hs, hy]
      refine ⟨⟨pullback.lift s (y (Fin.last j)) hc, by rw [pullback.lift_fst_assoc, hs]⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · show pullback.lift s (y (Fin.last j)) hc ≫ pullback.fst πW (ProjSpace.π B N) ≫ prH = h
        rw [pullback.lift_fst_assoc, hsH]
      · funext i
        show pullback.lift s (y (Fin.last j)) hc ≫ prY' i = y i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [hlast, pullback.lift_snd]
        · rw [hcast, pullback.lift_fst_assoc, hsY]

end S_AlgebraicGeometry_exists_isClosedImmersion_proj_forall_bijective_pullback_points
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_proj_forall_bijective_pullback_points (solution)
