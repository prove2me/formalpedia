-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1b6f134b-ef74-57af-9df5-a9b2c21980b5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Spec IsIntegral Scheme germ_injective_of_isIntegral exists_isAffineOpen_mem_and_subset IsAffineOpen"
namespace Spread
p2m_open "AlgebraicGeometry"

theorem primeIdealOf_fromSpec {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (h : hU.fromSpec.base y ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec.base y, h⟩ = y := by
  have h1 : (⟨hU.fromSpec.base y, h⟩ : U) = hU.isoSpec.inv.base y := by
    apply Subtype.ext
    change hU.fromSpec.base y = _
    rw [← hU.isoSpec_inv_ι]
    rfl
  change hU.isoSpec.hom.base _ = y
  rw [h1]
  exact congrArg (fun f : Spec Γ(X, U) ⟶ Spec Γ(X, U) => f.base y) hU.isoSpec.inv_hom_id

end AlgebraicGeometry.Spread

theorem solution
    {X : Scheme.{u}} [IsIntegral X] (x : X) (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (a b : X.presheaf.stalk x) (ha : a ∉ P) (hb : b ∉ P) :
    ∃ U : X.Opens, (X.fromSpecStalk x).base ⟨P, inferInstance⟩ ∈ U ∧
      ∀ y : X, y ∈ U → ∃ u : (X.presheaf.stalk y)ˣ,
        algebraMap (X.presheaf.stalk y) X.functionField (u : X.presheaf.stalk y) *
            algebraMap (X.presheaf.stalk x) X.functionField b =
          algebraMap (X.presheaf.stalk x) X.functionField a := by
  classical

  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨xW, rfl⟩ : ∃ xW : W, (xW : X) = x := ⟨⟨x, hxW⟩, rfl⟩
  haveI hloc := hW.isLocalization_stalk xW
  haveI : Nonempty W := ⟨xW⟩

  obtain ⟨⟨a', s⟩, has⟩ := IsLocalization.surj (hW.primeIdealOf xW).asIdeal.primeCompl a
  obtain ⟨⟨b', t⟩, hbt⟩ := IsLocalization.surj (hW.primeIdealOf xW).asIdeal.primeCompl b
  simp only at has hbt

  let P' : Ideal Γ(X, W) := P.comap (algebraMap Γ(X, W) (X.presheaf.stalk (xW : X)))
  haveI hP' : P'.IsPrime := Ideal.comap_isPrime _ P
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hsu : IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk (xW : X)) (s : Γ(X, W))) := IsLocalization.map_units _ s
  have htu : IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk (xW : X)) (t : Γ(X, W))) := IsLocalization.map_units _ t
  have hsP : algebraMap Γ(X, W) (X.presheaf.stalk (xW : X)) (s : Γ(X, W)) ∉ P := fun h =>
    hPtop (Ideal.eq_top_of_isUnit_mem _ h hsu)
  have htP : algebraMap Γ(X, W) (X.presheaf.stalk (xW : X)) (t : Γ(X, W)) ∉ P := fun h =>
    hPtop (Ideal.eq_top_of_isUnit_mem _ h htu)
  have ha' : a' ∉ P' := by
    intro h
    change algebraMap Γ(X, W) (X.presheaf.stalk (xW : X)) a' ∈ P at h
    rw [← has] at h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha hsP
  have hb' : b' ∉ P' := by
    intro h
    change algebraMap Γ(X, W) (X.presheaf.stalk (xW : X)) b' ∈ P at h
    rw [← hbt] at h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim hb htP
  have hs' : (s : Γ(X, W)) ∉ P' := hsP
  have ht' : (t : Γ(X, W)) ∉ P' := htP
  set f : Γ(X, W) := a' * b' * (s : Γ(X, W)) * (t : Γ(X, W)) with hf
  have hfP : f ∉ P' := by
    intro h
    rcases hP'.mem_or_mem h with h | h
    · rcases hP'.mem_or_mem h with h | h
      · rcases hP'.mem_or_mem h with h | h
        · exact ha' h
        · exact hb' h
      · exact hs' h
    · exact ht' h

  refine ⟨X.basicOpen f, ?_, ?_⟩
  ·
    let y : PrimeSpectrum Γ(X, W) := ⟨P', hP'⟩
    have hξ : (X.fromSpecStalk (xW : X)).base ⟨P, inferInstance⟩ = hW.fromSpec.base y := by
      rw [← hW.fromSpecStalk_eq_fromSpecStalk xW.2]
      rfl
    have hyW : hW.fromSpec.base y ∈ W := by
      have : hW.fromSpec.base y ∈ Set.range hW.fromSpec.base := ⟨y, rfl⟩
      rw [hW.range_fromSpec] at this
      exact this
    obtain ⟨yW, hyWeq⟩ : ∃ yW : W, (yW : X) = hW.fromSpec.base y := ⟨⟨_, hyW⟩, rfl⟩
    rw [hξ, ← hyWeq, Scheme.mem_basicOpen (hx := yW.2)]
    have key : hW.primeIdealOf yW = y := by
      have h := AlgebraicGeometry.Spread.primeIdealOf_fromSpec hW y hyW
      rwa [show (⟨hW.fromSpec.base y, hyW⟩ : W) = yW from Subtype.ext hyWeq.symm] at h
    have h := hW.isLocalization_stalk yW
    rw [key] at h
    haveI := h
    exact IsLocalization.map_units (M := P'.primeCompl) (X.presheaf.stalk (yW : X)) ⟨f, hfP⟩
  · intro z hz
    have hzW : z ∈ W := X.basicOpen_le f hz
    obtain ⟨zW, rfl⟩ : ∃ zW : W, (zW : X) = z := ⟨⟨z, hzW⟩, rfl⟩
    have hu := (Scheme.mem_basicOpen X f (zW : X) zW.2).mp hz
    change IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk (zW : X)) f) at hu
    rw [hf, map_mul, map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff] at hu
    obtain ⟨⟨⟨hua, hub⟩, hus⟩, hut⟩ := hu

    have hgW : genericPoint X ∈ W := ((genericPoint_spec X).specializes (by trivial)).mem_open W.2 xW.2
    have hK : ∀ (w : W) (σ : Γ(X, W)), algebraMap (X.presheaf.stalk (w : X)) X.functionField
        (algebraMap Γ(X, W) (X.presheaf.stalk (w : X)) σ) = (X.presheaf.germ W (genericPoint X) hgW).hom σ :=
      fun w σ => by
        change (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (by trivial))).hom
          ((X.presheaf.germ W (w : X) w.2).hom σ) = _
        exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have hKinj : Function.Injective (X.presheaf.germ W (genericPoint X) hgW).hom :=
      germ_injective_of_isIntegral X (genericPoint X) hgW
    have hne : ∀ σ : Γ(X, W), σ ∉ P' → (X.presheaf.germ W (genericPoint X) hgW).hom σ ≠ 0 := by
      intro σ hσ h0
      exact hσ (by rw [hKinj (h0.trans (map_zero _).symm)]; exact P'.zero_mem)

    refine ⟨(hua.mul hut).unit * ((hub.mul hus).unit)⁻¹, ?_⟩
    have e1 : algebraMap (X.presheaf.stalk (xW : X)) X.functionField a *
        (X.presheaf.germ W (genericPoint X) hgW).hom (s : Γ(X, W)) =
        (X.presheaf.germ W (genericPoint X) hgW).hom a' := by
      rw [← hK xW, ← hK xW, ← map_mul, has]
    have e2 : algebraMap (X.presheaf.stalk (xW : X)) X.functionField b *
        (X.presheaf.germ W (genericPoint X) hgW).hom (t : Γ(X, W)) =
        (X.presheaf.germ W (genericPoint X) hgW).hom b' := by
      rw [← hK xW, ← hK xW, ← map_mul, hbt]
    have hinv : algebraMap (X.presheaf.stalk (zW : X)) X.functionField (↑((hub.mul hus).unit⁻¹) : X.presheaf.stalk (zW : X)) =
        ((X.presheaf.germ W (genericPoint X) hgW).hom b' * (X.presheaf.germ W (genericPoint X) hgW).hom (s : Γ(X, W)))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h := congrArg (algebraMap (X.presheaf.stalk (zW : X)) X.functionField) (hub.mul hus).val_inv_mul
      rw [map_mul, map_one, map_mul, hK zW, hK zW] at h
      exact h
    rw [Units.val_mul, map_mul, IsUnit.unit_spec, map_mul, hK zW, hK zW, hinv, ← e1, ← e2]
    have hS := hne _ hs'
    have hT := hne _ ht'
    have hB := hne _ hb'
    have hbK : algebraMap (X.presheaf.stalk (xW : X)) X.functionField b ≠ 0 := fun h0 => hB (by rw [← e2, h0, zero_mul])
    field_simp

end S_AlgebraicGeometry_Scheme_exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime (solution)
