-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_algHom_cls_eq_cls_unitPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d3210bb6-1ee5-530a-939f-6aebccf2100d

import Mathlib
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_algHom_cls_eq_cls_unitPullback
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u

theorem solution
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (H : Type u) [Ring H] [Algebra R H] (𝒜 : ℕ → Submodule R H) [SetLike.GradedMonoid 𝒜]
    (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n)) →ₗ[R] H)
    (cls_range : ∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n)
    (cls_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 0)), cls 0 z = 0 ↔ z = 0)
    (cls_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 (n + 1)))),
      cls (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit πY).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit πY).d 𝒦 n))
    (cls_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 b))),
      ∃ hγ : (OModulePresheaf.unit πY).cup 𝒦 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 (a + b)),
        cls (a + b) ⟨_, hγ⟩ = cls a α * cls b β)
    (cls_internal : DirectSum.IsInternal 𝒜)
    (cls_one : ∃ h1 : (fun s => (1 : Γ(Y, 𝒦.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 0),
      cls 0 ⟨fun s => (1 : Γ(Y, 𝒦.inter s)), h1⟩ = 1)
    (H' : Type u) [Ring H'] [Algebra R H'] (𝒜' : ℕ → Submodule R H') [SetLike.GradedMonoid 𝒜']
    (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n)) →ₗ[R] H')
    (cls'_range : ∀ n : ℕ, LinearMap.range (cls' n) = 𝒜' n)
    (cls'_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0)
    (cls'_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 (n + 1)))),
      cls' (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit πX).cochain 𝒲 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 n))
    (cls'_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 b))),
      ∃ hγ : (OModulePresheaf.unit πX).cup 𝒲 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 (a + b)),
        cls' (a + b) ⟨_, hγ⟩ = cls' a α * cls' b β)
    (cls'_one : ∃ h1 : (fun s => (1 : Γ(X, 𝒲.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 0),
      cls' 0 ⟨fun s => (1 : Γ(X, 𝒲.inter s)), h1⟩ = 1)
    :
    ∃ p : H →ₐ[R] H',
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))),
        ∃ hz : OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z.1 ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n),
          p (cls n z) = cls' n ⟨_, hz⟩) ∧
      (∀ n : ℕ, (𝒜 n).map p.toLinearMap ≤ 𝒜' n) := by
  classical

  have hL0 := fun n => AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback πX πY h hh 𝒲 𝒦 lam hlam n
  choose L hL using hL0

  have hker : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))),
      L n z.1 ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n) := by
    intro n z
    rw [LinearMap.mem_ker, hL, AlgebraicGeometry.OModulePresheaf.d_unitPullback, LinearMap.mem_ker.mp z.2, ← hL, map_zero]
  let LZ : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n)) →ₗ[R] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n)) :=
    fun n => (L n).restrict (p := LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))
      (q := LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n)) (fun z hz => hker n ⟨z, hz⟩)
  have hLZ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))), (LZ n z).1 = L n z.1 := fun n z => rfl

  have hwd : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))), cls n z = 0 → cls' n (LZ n z) = 0 := by
    intro n z hz
    cases n with
    | zero =>
      rw [cls_zero] at hz
      rw [hz, map_zero, map_zero]
    | succ m =>
      rw [cls_succ] at hz
      obtain ⟨w, hw⟩ := hz
      rw [cls'_succ]
      refine ⟨L m w, ?_⟩
      rw [hLZ, hL, hL, AlgebraicGeometry.OModulePresheaf.d_unitPullback, hw]

  let f : ∀ n : ℕ, (↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n)) ⧸ LinearMap.ker (cls n)) →ₗ[R] H' :=
    fun n => (LinearMap.ker (cls n)).liftQ ((cls' n).comp (LZ n)) (fun z hz => by
      rw [LinearMap.mem_ker] at hz ⊢
      exact hwd n z hz)
  let pn : ∀ n : ℕ, ↥(𝒜 n) →ₗ[R] H' :=
    fun n => (f n).comp (((cls n).quotKerEquivRange.symm.toLinearMap).comp
      (LinearEquiv.ofEq _ _ (cls_range n)).symm.toLinearMap)
  have hpn : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))) (hx : cls n z ∈ 𝒜 n),
      pn n ⟨cls n z, hx⟩ = cls' n (LZ n z) := by
    intro n z hx
    have e1 : (LinearEquiv.ofEq _ _ (cls_range n)).symm ⟨cls n z, hx⟩ = ⟨cls n z, LinearMap.mem_range_self _ _⟩ := rfl
    show f n ((cls n).quotKerEquivRange.symm ((LinearEquiv.ofEq _ _ (cls_range n)).symm ⟨cls n z, hx⟩)) = _
    rw [e1, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl

  let eA : (⨁ n, ↥(𝒜 n)) ≃ₗ[R] H := LinearEquiv.ofBijective (DirectSum.coeLinearMap 𝒜) cls_internal
  let pL : H →ₗ[R] H' := (DirectSum.toModule R ℕ H' pn).comp eA.symm.toLinearMap
  have hpL : ∀ (n : ℕ) (x : H) (hx : x ∈ 𝒜 n), pL x = pn n ⟨x, hx⟩ := by
    intro n x hx
    have : eA.symm x = DirectSum.lof R ℕ (fun n => ↥(𝒜 n)) n ⟨x, hx⟩ := by
      apply eA.injective
      rw [LinearEquiv.apply_symm_apply, DirectSum.lof_eq_of]
      exact (DirectSum.coeLinearMap_of 𝒜 n ⟨x, hx⟩).symm
    show DirectSum.toModule R ℕ H' pn (eA.symm x) = _
    rw [this, DirectSum.toModule_lof]
  have hcls : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))),
      pL (cls n z) = cls' n (LZ n z) := by
    intro n z
    have hx : cls n z ∈ 𝒜 n := by rw [← cls_range n]; exact LinearMap.mem_range_self _ _
    rw [hpL n _ hx, hpn]

  have cls_mul' : ∀ (a b n : ℕ) (hn : a + b = n) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 a)))
      (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 b))),
      ∃ hγ : (OModulePresheaf.unit πY).cup 𝒦 a b n hn α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n),
        cls n ⟨_, hγ⟩ = cls a α * cls b β := by
    intro a b n hn α β; subst hn; exact cls_mul a b α β
  have cls'_mul' : ∀ (a b n : ℕ) (hn : a + b = n) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 a)))
      (β : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 b))),
      ∃ hγ : (OModulePresheaf.unit πX).cup 𝒲 a b n hn α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n),
        cls' n ⟨_, hγ⟩ = cls' a α * cls' b β := by
    intro a b n hn α β; subst hn; exact cls'_mul a b α β

  have hmul_hom' : ∀ (a b n : ℕ) (hn : a + b = n) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 a)))
      (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 b))),
      pL (cls a α * cls b β) = pL (cls a α) * pL (cls b β) := by
    intro a b n hn α β
    obtain ⟨hγ, hmul⟩ := cls_mul' a b n hn α β
    obtain ⟨hγ', hmul'⟩ := cls'_mul' a b n hn (LZ a α) (LZ b β)
    rw [← hmul, hcls, hcls, hcls, ← hmul', ← sub_eq_zero, ← map_sub]
    have key := AlgebraicGeometry.OModulePresheaf.unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker πX πY h 𝒲 𝒦 lam hlam
      a b n hn α β
    have hdiff : ((LZ n ⟨_, hγ⟩ - ⟨_, hγ'⟩ : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n))) :
        (OModulePresheaf.unit πX).cochain 𝒲 n) =
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).cup 𝒦 a b n hn α.1 β.1) -
          (OModulePresheaf.unit πX).cup 𝒲 a b n hn
            (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam a α.1)
            (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam b β.1) := by
      simp only [Submodule.coe_sub, hLZ, hL]
    cases n with
    | zero =>
      have h0 : (LZ 0 ⟨_, hγ⟩ - ⟨_, hγ'⟩ : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 0))) = 0 := by
        apply Subtype.ext
        rw [hdiff]
        simpa using key
      rw [h0, map_zero]
    | succ m =>
      rw [cls'_succ, hdiff]
      exact key

  have htop : ∀ x : H, x ∈ iSup 𝒜 := fun x => by rw [cls_internal.submodule_iSup_eq_top]; trivial
  have hmul : ∀ x y : H, pL (x * y) = pL x * pL y := by
    intro x y
    induction htop x using Submodule.iSup_induction' with
    | mem i x hx =>
      induction htop y using Submodule.iSup_induction' with
      | mem j y hy =>
        have hx' : x ∈ LinearMap.range (cls i) := by rw [cls_range]; exact hx
        have hy' : y ∈ LinearMap.range (cls j) := by rw [cls_range]; exact hy
        obtain ⟨α, rfl⟩ := hx'
        obtain ⟨β, rfl⟩ := hy'
        exact hmul_hom' i j (i + j) rfl α β
      | zero => simp
      | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂]

  have hone1 : OModulePresheaf.unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam 0 (fun s => (1 : Γ(Y, 𝒦.inter s))) =
      fun s => (1 : Γ(X, 𝒲.inter s)) := by
    funext s
    have hinj : Function.Injective (lam ∘ s.1) := fun i j _ =>
      Fin.ext (by have h1 := i.isLt; have h2 := j.isLt; omega)
    rw [AlgebraicGeometry.OModulePresheaf.unitPullback_apply_of_injective (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam 0 _ s hinj]
    have hσ : Tuple.sort (lam ∘ s.1) = 1 := Equiv.ext fun i =>
      Fin.ext (by have h1 := (Tuple.sort (lam ∘ s.1) i).isLt; have h2 := i.isLt; simp only [Equiv.Perm.coe_one, id_eq]; omega)
    rw [hσ, Equiv.Perm.sign_one, Units.val_one, one_smul, map_one, map_one]
  have hone : pL 1 = 1 := by
    obtain ⟨h1, hcls1⟩ := cls_one
    obtain ⟨h1', hcls1'⟩ := cls'_one
    rw [← hcls1, hcls, ← hcls1']
    congr 1
    apply Subtype.ext
    exact (hL 0 _).trans hone1
  refine ⟨AlgHom.ofLinearMap pL hone hmul, fun n z => ⟨(hL n z.1) ▸ hker n z, ?_⟩, fun n => ?_⟩
  · show pL (cls n z) = _
    rw [hcls]
    congr 1
    apply Subtype.ext
    exact hL n z.1
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ LinearMap.range (cls n) := by rw [cls_range]; exact hx
    obtain ⟨z, rfl⟩ := hx'
    show pL (cls n z) ∈ 𝒜' n
    rw [hcls, ← cls'_range]
    exact LinearMap.mem_range_self _ _

end S_AlgebraicGeometry_OModulePresheaf_exists_algHom_cls_eq_cls_unitPullback
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_algHom_cls_eq_cls_unitPullback (solution)
