-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:56.731818+00:00
-- url     : https://prove2.me/theorems/37b5a510-56e4-4c57-a03f-998ca5554cfd
-- title:
--   Res Map Bijective
-- statement:
--   Definitions and structural lemmas for Res Map Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
namespace UpperTheory.V.Alg
class IsCO (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] : Prop
    extends IsLocalRing R, IsNoetherianRing R where
  complete : IsAdicComplete (maximalIdeal R) R
  isLocalHom : IsLocalHom (algebraMap O R)
  res_surj : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ maximalIdeal R
attribute [instance] IsCO.complete IsCO.isLocalHom
instance IsCO.self (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] : IsCO O O where
  complete := inferInstance
  isLocalHom := ⟨fun _ h => h⟩
  res_surj x := ⟨x, by simp⟩
section Res
variable (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
theorem resMap_bijective : Function.Bijective (ResidueField.map (algebraMap O R)) := by
  refine ⟨(ResidueField.map (algebraMap O R)).injective, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  refine ⟨residue O a, ?_⟩
  rw [ResidueField.map_residue]
  exact ((Ideal.Quotient.eq).2 ha).symm
def res : R →ₐ[O] ResidueField O :=
  { ((RingEquiv.ofBijective _ (resMap_bijective O R)).symm.toRingHom.comp (residue R)) with
    commutes' := fun a => by
      show (RingEquiv.ofBijective _ (resMap_bijective O R)).symm (residue R (algebraMap O R a)) = residue O a
      rw [RingEquiv.symm_apply_eq]
      exact (ResidueField.map_residue _ _).symm }
theorem res_eq_zero_iff (x : R) : res O R x = 0 ↔ x ∈ maximalIdeal R := by
  show (RingEquiv.ofBijective _ (resMap_bijective O R)).symm (residue R x) = 0 ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), residue_eq_zero_iff]
variable {O R} in

theorem res_map {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (x : R) :
    res O R' (f x) = res O R x := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 : res O R x = algebraMap O _ a := by
    have := (res_eq_zero_iff O R _).2 ha
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have hm : ∀ y ∈ maximalIdeal R, f y ∈ maximalIdeal R' := fun y hy => by
    obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) (f y)
    by_cases hu : IsUnit b
    · exfalso
      have h2 : IsUnit (y - algebraMap O R b) := by
        by_contra hn
        have h3 : y - algebraMap O R b ∈ maximalIdeal R := hn
        have h4 : algebraMap O R b ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
        exact h4 (hu.map _)
      have h5 := h2.map f
      rw [map_sub, AlgHom.commutes] at h5
      exact hb h5
    · have h6 : algebraMap O R' b ∈ maximalIdeal R' := fun h => hu (IsLocalHom.map_nonunit b h)
      simpa using Ideal.add_mem _ hb h6
  have h2 := (res_eq_zero_iff O R' _).2 (hm _ ha)
  rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_eq_zero] at h2
  rw [h2, h1]
end Res
def AdicCont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f : Γ → R) : Prop :=
  ∀ N : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (I ^ N) (f g)
section Weights
variable (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
def wtPart (j : X) : Submodule O (MvPowerSeries σ O) where
  carrier := {f | ∀ n, Finsupp.weight wt n ≠ j → coeff n f = 0}
  add_mem' ha hb n hn := by rw [map_add, ha n hn, hb n hn, add_zero]
  zero_mem' n _ := map_zero _
  smul_mem' c f hf n hn := by rw [map_smul, hf n hn, smul_zero]
open Classical in

def wcomp (j : X) : MvPowerSeries σ O →ₗ[O] MvPowerSeries σ O where
  toFun f := fun n => if Finsupp.weight wt n = j then coeff n f else 0
  map_add' f g := funext fun n => by
    show (if _ then _ else _) = (if _ then _ else _) + (if _ then _ else (0 : O))
    split_ifs <;> simp
  map_smul' c f := funext fun n => by
    show (if _ then _ else _) = c • (if _ then _ else (0 : O))
    split_ifs <;> simp
theorem mul_mem_wtPart {i j : X} {f g : MvPowerSeries σ O} (hf : f ∈ wtPart O wt i) (hg : g ∈ wtPart O wt j) :
    f * g ∈ wtPart O wt (i + j) := fun n hn => by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  by_cases h1 : Finsupp.weight wt p.1 = i
  · have h2 : Finsupp.weight wt p.2 ≠ j := fun h2 => hn (by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add, h1, h2])
    rw [hg _ h2, mul_zero]
  · rw [hf _ h1, zero_mul]
theorem one_mem_wtPart : (1 : MvPowerSeries σ O) ∈ wtPart O wt 0 := fun n hn => by
  classical
  rw [coeff_one, if_neg]
  rintro rfl
  exact hn (map_zero _)
theorem X_mem_wtPart (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ O) ∈ wtPart O wt (wt i) := fun n hn => by
  classical
  rw [coeff_X, if_neg]
  rintro rfl
  exact hn (by simp [Finsupp.weight_single])
instance : SetLike.GradedMonoid (wtPart O wt) where
  one_mem := one_mem_wtPart O wt
  mul_mem _ _ _ _ := mul_mem_wtPart O wt
def IsHomog (J : Ideal (MvPowerSeries σ O)) : Prop := ∀ f ∈ J, ∀ j, wcomp O wt j f ∈ J
end Weights
def gradedSub {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] (𝒜 : X → Submodule O R)
    [SetLike.GradedMonoid 𝒜] : Subalgebra O R :=
  (⨆ j, 𝒜 j).toSubalgebra (le_iSup 𝒜 0 (SetLike.GradedOne.one_mem)) fun x y hx hy => by
    refine Submodule.iSup_induction 𝒜 (motive := fun x => x * y ∈ ⨆ j, 𝒜 j) hx (fun i a ha => ?_) (by simp)
      (fun a b ha hb => by rw [add_mul]; exact add_mem ha hb)
    exact Submodule.iSup_induction 𝒜 (motive := fun y => a * y ∈ ⨆ j, 𝒜 j) hy
      (fun j b hb => le_iSup 𝒜 (i + j) (SetLike.GradedMul.mul_mem ha hb)) (by simp)
      (fun b c hb hc => by rw [mul_add]; exact add_mem hb hc)
structure WPres (O X R : Type) [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] where
  σ : Type
  [fin : Fintype σ]
  wt : σ → X
  π : MvPowerSeries σ O →ₐ[O] R
  surj : Function.Surjective π
  homog : IsHomog O wt (RingHom.ker π)
attribute [instance] WPres.fin
namespace WPres
variable {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
def free (O : Type) [CommRing O] {σ : Type} [Fintype σ] (wt : σ → X) : WPres O X (MvPowerSeries σ O) where
  σ := σ
  wt := wt
  π := AlgHom.id O _
  surj := Function.surjective_id
  homog f hf j := by
    have : f = 0 := hf
    subst this
    simp
def z (i : W.σ) : R := W.π (MvPowerSeries.X i)
def part (j : X) : Submodule O R := (wtPart O W.wt j).map W.π.toLinearMap
instance : SetLike.GradedMonoid W.part where
  one_mem := ⟨1, one_mem_wtPart O W.wt, map_one W.π⟩
  mul_mem := by
    rintro i j _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, mul_mem_wtPart O W.wt hf hg, map_mul W.π f g⟩
theorem z_mem (i : W.σ) : W.z i ∈ W.part (W.wt i) := ⟨_, X_mem_wtPart O W.wt i, rfl⟩
def A : Subalgebra O R := gradedSub W.part
def gr (j : X) : Submodule O W.A := (W.part j).comap W.A.val.toLinearMap
instance : SetLike.GradedMonoid W.gr where
  one_mem := (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
  mul_mem _ _ _ _ ha hb := (SetLike.GradedMul.mul_mem ha hb : _ ∈ W.part _)
theorem part_le_A {j : X} {x : R} (hx : x ∈ W.part j) : x ∈ W.A := le_iSup W.part j hx
def zA (i : W.σ) : W.A := ⟨W.z i, W.part_le_A (W.z_mem i)⟩
def HasOrigin : Prop := ∀ f, W.π f = 0 → constantCoeff f = 0
def origin (h : W.HasOrigin) : R →ₐ[O] O :=
  (Ideal.Quotient.liftₐ (RingHom.ker W.π)
    ({ (constantCoeff : MvPowerSeries W.σ O →+* O) with commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] } : MvPowerSeries W.σ O →ₐ[O] O)
    h).comp (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
end WPres
section Points
variable {O A X K : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X]
  (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] [CommRing K] [Algebra O K]
def act (t : Multiplicative X →* Kˣ) (ξ : A →ₐ[O] K) : A →ₐ[O] K :=
  (DirectSum.toAlgebra O (fun j => 𝒜 j)
    (fun j => ((t (Multiplicative.ofAdd j) : Kˣ) : K) • (ξ.toLinearMap ∘ₗ (𝒜 j).subtype))
    (by simp) (fun {i j} a b => by
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
        SetLike.coe_gMul, map_mul, ofAdd_add, Units.val_mul, smul_eq_mul]
      ring)).comp (DirectSum.decomposeAlgEquiv 𝒜).toAlgHom
end Points
def PtDer {O A B : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] (x : A →ₐ[O] B)
    (Q : Type) [AddCommGroup Q] [Module O Q] [Module B Q] [SMulCommClass O B Q] : Submodule B (A →ₗ[O] Q) where
  carrier := {D | ∀ f g, D (f * g) = x f • D g + x g • D f}
  add_mem' {D D'} h h' f g := by simp only [LinearMap.add_apply, h f g, h' f g, smul_add]; abel
  zero_mem' f g := by simp
  smul_mem' c D h f g := by simp only [LinearMap.smul_apply, h f g, smul_add, smul_smul, mul_comm]
def HasWt {O A X Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q] [Module O Q]
    (𝒜 : X → Submodule O A) (j : X) (D : A →ₗ[O] Q) : Prop := ∀ i, i ≠ j → ∀ f ∈ 𝒜 i, D f = 0
section Cot
variable {O A X : Type} [CommRing O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
def satSq [IsDomain O] : Submodule O A where
  carrier := {f | ∃ c : O, c ≠ 0 ∧ c • f ∈ RingHom.ker x ^ 2}
  add_mem' := by
    rintro f g ⟨c, hc, hf⟩ ⟨d, hd, hg⟩
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add, mul_comm c d, mul_smul, mul_comm d c, mul_smul]
    exact add_mem (Submodule.smul_of_tower_mem _ d hf) (Submodule.smul_of_tower_mem _ c hg)
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' a f := by
    rintro ⟨c, hc, hf⟩
    exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_of_tower_mem _ a hf⟩
def cotLat [IsDomain O] (𝒜 : X → Submodule O A) (j : X) : Submodule O (A ⧸ satSq x) :=
  (𝒜 j ⊓ (RingHom.ker x).restrictScalars O).map (satSq x).mkQ
def cotSpan [IsDomain O] {ι : Type} (F : ι → A) : Submodule O (A ⧸ satSq x) :=
  Submodule.span O (Set.range fun i => (satSq x).mkQ (F i))
def SpansCot [IsDomain O] (𝒜 : X → Submodule O A) (j : X) {ι : Type} (F : ι → A) : Prop :=
  ∀ p ∈ cotLat x 𝒜 j, ∃ c : O, c ≠ 0 ∧ c • p ∈ cotSpan x F
def cotLen [IsDomain O] (𝒜 : X → Submodule O A) (j : X) {ι : Type} (F : ι → A) : ℕ∞ :=
  Module.length O (cotLat x 𝒜 j ⧸ (cotSpan x F).comap (cotLat x 𝒜 j).subtype)
end Cot
section Lifts
variable (O : Type) [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι]
  [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O))
@[ext] structure Lift (R : Type) [CommRing R] [Algebra O R] [IsCO O R] where
  hom : Γ →* Matrix ι ι R
  cont : ∀ a b, AdicCont (maximalIdeal R) fun g => hom g a b
  red : ∀ g a b, res O R (hom g a b) = rbar g a b
variable {O rbar} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
def Lift.map (f : R →ₐ[O] R') (r : Lift O rbar R) : Lift O rbar R' where
  hom := (f.mapMatrix : Matrix ι ι R →ₐ[O] Matrix ι ι R').toMonoidHom.comp r.hom
  cont a b N := by
    have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
      refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
      show f y ∈ maximalIdeal R'
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    exact (r.cont a b N).comp (Ideal.quotientMap _ (f : R →+* R') hle)
  red g a b := (res_map f _).trans (r.red g a b)
def Lift.comap {H : Type} [Group H] [TopologicalSpace H] (φ : H →* Γ) (hφ : Continuous φ) (r : Lift O rbar R) :
    Lift O (rbar.comp φ) R where
  hom := r.hom.comp φ
  cont a b N := (r.cont a b N).comp_continuous hφ
  red g a b := r.red (φ g) a b
variable (O rbar) in

def Cond : Type 1 := ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], Lift O rbar R → Prop
def polyCond (C : Set (MvPolynomial (Γ × ι × ι) O)) : Cond O rbar :=
  fun _ _ _ _ r => ∀ p ∈ C, MvPolynomial.aeval (fun s : Γ × ι × ι => r.hom s.1 s.2.1 s.2.2) p = 0
def Represents (P : Cond O rbar) (r : Lift O rbar R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'],
    (∀ f : R →ₐ[O] R', P R' (r.map f)) ∧ ∀ r' : Lift O rbar R', P R' r' → ∃! f : R →ₐ[O] R', r.map f = r'
def Lift.Generates (r : Lift O rbar R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R'), r.map f = r.map f' → f = f'
variable {X : Type} [AddCommGroup X] (w : ι → X)
variable (rbar) in

def Centralises : Prop := ∀ g a b, w a ≠ w b → rbar g a b = 0
def IsTorusConj (t : Multiplicative X →* Rˣ) (r r' : Lift O rbar R) : Prop :=
  ∀ g a b, r'.hom g a b = t (Multiplicative.ofAdd (w a - w b)) * r.hom g a b
def Lift.TStable (r : Lift O rbar R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ),
    (∀ j, res O R' (t j) = 1) → ∃ f' : R →ₐ[O] R', IsTorusConj w t (r.map f) (r.map f')
def Lift.Adapted (r : Lift O rbar R) (W : WPres O X R) : Prop :=
  (∀ g a b, r.hom g a b ∈ W.part (w a - w b)) ∧
    ∀ i, ∃ g a b, ∃ c : O, W.z i = r.hom g a b - algebraMap O R c ∧ W.wt i = w a - w b ∧ (w a ≠ w b → c = 0)
variable (Γ) in

def PhiCond (l : ℕ) : Prop :=
  ∀ H : Subgroup Γ, IsOpen (H : Set Γ) →
    Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H)}
end Lifts
end UpperTheory.V.Alg


