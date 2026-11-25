-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_Procyclic
-- name    : GroundTheory_ProfiniteCohomology_Procyclic
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:40:37.643331+00:00
-- url     : https://prove2.me/theorems/a2787e89-dd6a-4375-920e-fc7b5dc122b6
-- title:
--   Procyclic
-- statement:
--   Definitions and structural lemmas for Procyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Procyclic.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Theorems.Thm_GroundTheory_ProfCoh_IsTopologicalGenerator_eq_of_forall_zpow
import Theorems.Thm_GroundTheory_ProfCoh_IsTopologicalGenerator_eq_of_forall_zpow_pi
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyCoindCokernelIso_hom
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isOpen_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.cohomologyCoindCokernelIso_hom
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory Limits groupCohomology
universe u
section Formulas
variable {k G : Type u} [CommRing k] [Group G]
theorem inhomogeneousD_zero_apply (A : Rep.{u} k G) (f : (Fin 0 → G) → A) (g : Fin 1 → G) :
    (inhomogeneousCochains.d A 0).hom f g = A.ρ (g 0) (f Fin.elim0) - f Fin.elim0 := by
  have h1 : (fun i : Fin 0 => g i.succ) = Fin.elim0 := funext fun i => i.elim0
  have h2 : Fin.contractNth 0 (· * ·) g = Fin.elim0 := funext fun i => i.elim0
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_one, h1, h2]
  simp [sub_eq_add_neg]
theorem inhomogeneousD_one_apply (A : Rep.{u} k G) (f : (Fin 1 → G) → A) (g : Fin 2 → G) :
    (inhomogeneousCochains.d A 1).hom f g =
      A.ρ (g 0) (f fun _ => g 1) - f (fun _ => g 0 * g 1) + f (fun _ => g 0) := by
  have h1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := funext fun i => by
    rw [Subsingleton.elim i 0]; rfl
  have h2 : Fin.contractNth 0 (· * ·) g = fun _ : Fin 1 => g 0 * g 1 := funext fun i => by
    rw [Subsingleton.elim i 0]; simp [Fin.contractNth]
  have h3 : Fin.contractNth 1 (· * ·) g = fun _ : Fin 1 => g 0 := funext fun i => by
    rw [Subsingleton.elim i 0]; simp [Fin.contractNth]
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_two, h1, h2, h3]
  simp [sub_eq_add_neg, add_assoc]
theorem cocycle_mul_of_d_eq_zero {A : Rep.{u} k G} {f : (Fin 1 → G) → A}
    (hf : (inhomogeneousCochains.d A 1).hom f = 0) (g h : G) :
    f (fun _ => g * h) = A.ρ g (f fun _ => h) + f fun _ => g := by
  have this : A.ρ g (f fun _ => h) - f (fun _ => g * h) + f (fun _ => g) = 0 := by
    have h0 := congrFun hf ![g, h]
    rw [inhomogeneousD_one_apply] at h0
    exact h0
  apply eq_of_sub_eq_zero
  rw [← neg_eq_zero, ← this]
  abel
theorem eq_const_of_fin_one {X : Type*} (x : Fin 1 → X) : x = fun _ => x 0 := by
  funext i
  rw [Subsingleton.elim i 0]
end Formulas
section Generator
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem _root_.MonoidHom.isLocallyConstant_of_isOpen_ker {H : Type*} [Group H] (φ : G →* H)
    (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : G => x⁻¹ * y := continuous_const.mul continuous_id
  have : ∀ᶠ y in nhds x, x⁻¹ * y ∈ φ.ker :=
    hc.continuousAt.preimage_mem_nhds (by rw [inv_mul_cancel]; exact h.mem_nhds (one_mem _))
  filter_upwards [this] with y hy
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hy
  exact hy.symm
theorem exists_pow_mem_of_isOpen [CompactSpace G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    (σ : G) : ∃ N : ℕ, 0 < N ∧ σ ^ N ∈ H := by
  have := Subgroup.quotient_finite_of_isOpen H hH
  obtain ⟨N, hN, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero H.index_ne_zero_of_finite σ
  exact ⟨N, hN, h⟩
theorem IsTopologicalGenerator.eq_top_of_isOpen {σ : G} (hσ : IsTopologicalGenerator σ)
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (hσH : σ ∈ H) : H = ⊤ := by
  have hcl : IsClosed (H : Set G) := H.isClosed_of_isOpen hH
  have hle : (Subgroup.zpowers σ : Set G) ⊆ H := (Subgroup.zpowers_le.2 hσH)
  have := hcl.closure_subset_iff.2 hle
  rw [hσ.closure_eq] at this
  exact eq_top_iff.2 fun x _ => this (Set.mem_univ x)
end Generator
section Cocycles
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Rep.{u} k G} {σ : G}
omit [IsTopologicalGroup G] in

theorem IsTopologicalGenerator.cocycle_eq_zero (hσ : IsTopologicalGenerator σ)
    {f : (Fin 1 → G) → A} (hlc : IsLocallyConstant f)
    (hf : (inhomogeneousCochains.d A 1).hom f = 0) (hσf : f (fun _ => σ) = 0) : f = 0 := by
  set F : G → A := fun g => f fun _ => g with hFdef
  have hF1 : F 1 = 0 := by
    have := cocycle_mul_of_d_eq_zero hf 1 1
    simp only [mul_one, map_one, Module.End.one_apply] at this
    simpa using this
  have hpow : ∀ n : ℤ, F (σ ^ n) = 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => simpa using hF1
    | succ n ih =>
      have := cocycle_mul_of_d_eq_zero hf (σ ^ (n : ℤ)) σ
      simp only [hσf, map_zero, zero_add] at this
      change F (σ ^ (n : ℤ) * σ) = F (σ ^ (n : ℤ)) at this
      rw [zpow_add_one, this, ih]
    | pred n ih =>
      have := cocycle_mul_of_d_eq_zero hf (σ ^ (-(n : ℤ) - 1)) σ
      simp only [hσf, map_zero, zero_add] at this
      change F (σ ^ (-(n : ℤ) - 1) * σ) = F (σ ^ (-(n : ℤ) - 1)) at this
      rw [← zpow_add_one, sub_add_cancel, ih] at this
      exact this.symm
  have hFlc : IsLocallyConstant F :=
    hlc.comp_continuous (continuous_pi fun _ => continuous_id)
  have hF0 : F = 0 := hσ.eq_of_forall_zpow hFlc (IsLocallyConstant.const 0) hpow
  funext x
  calc f x = F (x 0) := congrArg f (eq_const_of_fin_one x)
    _ = 0 := congrFun hF0 (x 0)
end Cocycles
section Existence
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Rep.{u} k G} {σ : G}
omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem sum_range_mul_eq_zero {a : A} {N m : ℕ} (hN : A.ρ (σ ^ N) a = a) (hm : m • a = 0) :
    ∑ i ∈ Finset.range (N * m), A.ρ (σ ^ i) a = 0 := by
  have hmem : σ ^ N ∈ stabilizer A.ρ a := hN
  have key : ∀ q : ℕ, ∑ i ∈ Finset.range (N * q), A.ρ (σ ^ i) a =
      q • ∑ i ∈ Finset.range N, A.ρ (σ ^ i) a := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have hq : A.ρ (σ ^ (N * q)) a = a := by
        rw [pow_mul]
        exact (mem_stabilizer _ _ _).1 (pow_mem hmem q)
      rw [add_comm, pow_add, map_mul, Module.End.mul_apply, hq]
  rw [key, Finset.smul_sum]
  simp_rw [← map_nsmul, hm, map_zero, Finset.sum_const_zero]
variable [CompactSpace G] [IsDiscreteRep A]
theorem IsZHatGenerator.exists_cocycle (hσ : IsZHatGenerator σ) (a : A) (ha : IsOfFinAddOrder a) :
    ∃ f : (Fin 1 → G) → A, IsLocallyConstant f ∧ (inhomogeneousCochains.d A 1).hom f = 0 ∧
      f (fun _ => σ) = a := by
  obtain ⟨N, hN0, hN⟩ := exists_pow_mem_of_isOpen _ (isOpen_stabilizer A a) σ
  have hmem : σ ^ N ∈ stabilizer A.ρ a := hN
  rw [mem_stabilizer] at hN
  have hm0 : 0 < addOrderOf a := ha.addOrderOf_pos
  have hm : addOrderOf a • a = 0 := addOrderOf_nsmul_eq_zero a
  obtain ⟨L, hLdef⟩ : ∃ L, L = N * addOrderOf a := ⟨_, rfl⟩
  have hL0 : 0 < L := hLdef ▸ Nat.mul_pos hN0 hm0
  have : NeZero L := ⟨hL0.ne'⟩
  obtain ⟨φ, hφo, hφσ⟩ := hσ.exists_hom L hL0
  have hρ : ∀ (x y : ℤ) (v : A), A.ρ (σ ^ x) (A.ρ (σ ^ y) v) = A.ρ (σ ^ (x + y)) v := by
    intro x y v
    rw [zpow_add, map_mul, Module.End.mul_apply]
  have hper : ∀ q : ℤ, A.ρ (σ ^ ((L : ℤ) * q)) a = a := by
    intro q
    have : σ ^ ((L : ℤ) * q) = (σ ^ N) ^ ((addOrderOf a : ℤ) * q) := by
      rw [← zpow_natCast σ N, ← zpow_mul, hLdef]
      push_cast
      ring_nf
    rw [this]
    exact (mem_stabilizer _ _ _).1 (zpow_mem hmem _)
  have hsum : ∑ i ∈ Finset.range L, A.ρ (σ ^ i) a = 0 := hLdef ▸ sum_range_mul_eq_zero hN hm
  obtain ⟨c, hc⟩ : ∃ c : ℤ → A, ∀ n, c n = ∑ i ∈ Finset.range ((n : ZMod L).val), A.ρ (σ ^ i) a :=
    ⟨_, fun _ => rfl⟩
  have hc0 : c 0 = 0 := by rw [hc]; simp
  have hrec : ∀ n : ℤ, c (n + 1) = c n + A.ρ (σ ^ n) a := by
    intro n
    obtain ⟨r, hr⟩ : ∃ r, r = (n : ZMod L).val := ⟨_, rfl⟩
    have hrL : r < L := hr ▸ ZMod.val_lt _
    have hrn : A.ρ (σ ^ n) a = A.ρ (σ ^ r) a := by
      have h1 : (r : ℤ) = n % L := by rw [hr, ZMod.val_intCast]
      have h2 : n = r + L * (n / L) := by rw [h1]; exact (Int.emod_add_mul_ediv n L).symm
      conv_lhs => rw [h2]
      rw [zpow_add, map_mul, Module.End.mul_apply, hper, zpow_natCast]
    have hval : ((n + 1 : ℤ) : ZMod L).val = (r + 1) % L := by
      rw [Int.cast_add, Int.cast_one, ZMod.val_add, ZMod.val_one_eq_one_mod, ← hr, Nat.add_mod_mod]
    rw [hc, hc, hval, hrn, ← hr]
    rcases Nat.lt_or_ge (r + 1) L with h | h
    · rw [Nat.mod_eq_of_lt h, Finset.sum_range_succ]
    · have h' : r + 1 = L := le_antisymm (by omega) h
      rw [h', Nat.mod_self, Finset.range_zero, Finset.sum_empty, ← Finset.sum_range_succ, h', hsum]
  have hcoc : ∀ x y : ℤ, c (x + y) = c x + A.ρ (σ ^ x) (c y) := by
    intro x y
    induction y using Int.induction_on with
    | zero => simp [hc0]
    | succ y ih =>
      rw [← add_assoc, hrec, ih, hrec, map_add, hρ, add_assoc]
    | pred y ih =>
      have e1 := hrec (x + (-(y : ℤ) - 1))
      have e2 := hrec (-(y : ℤ) - 1)
      rw [show x + (-(y : ℤ) - 1) + 1 = x + -(y : ℤ) by ring, ih] at e1
      rw [show -(y : ℤ) - 1 + 1 = -(y : ℤ) by ring] at e2
      rw [e2, map_add, hρ] at e1
      have e3 := e1.symm
      rw [← add_assoc] at e3
      exact add_right_cancel e3
  obtain ⟨F, hF⟩ : ∃ F : G → A, ∀ g, F g =
      ∑ i ∈ Finset.range (Multiplicative.toAdd (φ g)).val, A.ρ (σ ^ i) a := ⟨_, fun _ => rfl⟩
  have hFpow : ∀ n : ℤ, F (σ ^ n) = c n := by
    intro n
    rw [hF, hc, map_zpow, hφσ, toAdd_zpow, toAdd_ofAdd, zsmul_one]
  have hFlc : IsLocallyConstant F := by
    have h1 : IsLocallyConstant φ := φ.isLocallyConstant_of_isOpen_ker hφo
    have : F = (fun z : Multiplicative (ZMod L) =>
        ∑ i ∈ Finset.range (Multiplicative.toAdd z).val, A.ρ (σ ^ i) a) ∘ φ := funext hF
    rw [this]
    exact h1.comp _
  have hflc : IsLocallyConstant fun x : Fin 1 → G => F (x 0) :=
    hFlc.comp_continuous (continuous_apply 0)
  refine ⟨fun x => F (x 0), hflc, ?_, ?_⟩
  · refine hσ.dense.eq_of_forall_zpow_pi (isLocallyConstant_d A hflc)
      (IsLocallyConstant.const 0) fun n => ?_
    show (inhomogeneousCochains.d A 1).hom (fun x => F (x 0)) (fun i => σ ^ n i) = 0
    rw [inhomogeneousD_one_apply]
    dsimp only
    rw [← zpow_add, hFpow, hFpow, hFpow, hcoc]
    abel
  · show F σ = a
    have h1 := hFpow 1
    rw [zpow_one] at h1
    rw [h1, ← zero_add (1 : ℤ), hrec, hc0, zpow_zero, map_one, Module.End.one_apply, zero_add]
end Existence
section H1
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A] (σ : G)
noncomputable def cocycleFun (z : cocycles A 1) : (Fin 1 → G) → A :=
  ((show locallyConstantCochains A 1 from ((cochainsComplex A).iCycles 1).hom z) : (Fin 1 → G) → A)
theorem isLocallyConstant_cocycleFun (z : cocycles A 1) : IsLocallyConstant (cocycleFun A z) :=
  (show locallyConstantCochains A 1 from ((cochainsComplex A).iCycles 1).hom z).2
theorem d_cocycleFun (z : cocycles A 1) :
    (inhomogeneousCochains.d A 1).hom (cocycleFun A z) = 0 := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ z) ((cochainsComplex A).iCycles_d 1 2)
  rw [show (2 : ℕ) = 1 + 1 from rfl, cochainsComplex_d] at h
  exact congrArg Subtype.val h
theorem cocycleFun_toCycles (b : (cochainsComplex A).X 0) :
    cocycleFun A (((cochainsComplex A).toCycles 0 1).hom b) =
      (inhomogeneousCochains.d A 0).hom
        ((show locallyConstantCochains A 0 from b) : (Fin 0 → G) → A) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ b) ((cochainsComplex A).toCycles_i 0 1)
  rw [cochainsComplex_d_zero_one] at h
  exact congrArg Subtype.val h
theorem cocycleFun_injective : Function.Injective (cocycleFun A) := fun _ _ h =>
  (ModuleCat.mono_iff_injective ((cochainsComplex A).iCycles 1)).1 inferInstance (Subtype.ext h)
noncomputable def evalCocycles :
    cocycles A 1 ⟶ ModuleCat.of k (A ⧸ LinearMap.range (A.ρ σ - 1)) :=
  ModuleCat.ofHom
    { toFun := fun z => Submodule.Quotient.mk (cocycleFun A z fun _ => σ)
      map_add' := fun _ _ => by
        rw [← Submodule.Quotient.mk_add]
        congr 1
        exact congrArg (fun c : locallyConstantCochains A 1 => (c : (Fin 1 → G) → A) fun _ => σ)
          (map_add ((cochainsComplex A).iCycles 1).hom _ _)
      map_smul' := fun r z => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1
        exact congrArg (fun c : locallyConstantCochains A 1 => (c : (Fin 1 → G) → A) fun _ => σ)
          (map_smul ((cochainsComplex A).iCycles 1).hom r z) }
theorem evalCocycles_apply (z : cocycles A 1) :
    (evalCocycles A σ).hom z = Submodule.Quotient.mk (cocycleFun A z fun _ => σ) :=
  rfl
theorem toCycles_evalCocycles : (cochainsComplex A).toCycles 0 1 ≫ evalCocycles A σ = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
  change (evalCocycles A σ).hom (((cochainsComplex A).toCycles 0 1).hom b) = 0
  rw [evalCocycles_apply, cocycleFun_toCycles, inhomogeneousD_zero_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨((show locallyConstantCochains A 0 from b) : (Fin 0 → G) → A) Fin.elim0, rfl⟩
noncomputable def H1Eval : cohomology A 1 ⟶ ModuleCat.of k (A ⧸ LinearMap.range (A.ρ σ - 1)) :=
  ((cochainsComplex A).homologyIsCokernel 0 1 (by simp)).desc
    (Limits.CokernelCofork.ofπ _ (toCycles_evalCocycles A σ))
@[reassoc (attr := simp)]
theorem cohomologyπ_H1Eval : cohomologyπ A 1 ≫ H1Eval A σ = evalCocycles A σ :=
  ((cochainsComplex A).homologyIsCokernel 0 1 (by simp)).fac _ Limits.WalkingParallelPair.one
theorem H1Eval_cohomology_class_apply (z : cocycles A 1) :
    (H1Eval A σ).hom ((cohomologyπ A 1).hom z) =
      Submodule.Quotient.mk (cocycleFun A z fun _ => σ) := by
  rw [← evalCocycles_apply, ← cohomologyπ_H1Eval]
  rfl
theorem H1Eval_injective {σ : G} (hσ : IsTopologicalGenerator σ) :
    Function.Injective (H1Eval A σ).hom := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((cochainsComplex A).homologyπ 1)).1
    inferInstance y
  change (H1Eval A σ).hom ((cohomologyπ A 1).hom z) = 0 at hy
  rw [H1Eval_cohomology_class_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨b, hb⟩ := hy
  let b0' : locallyConstantCochains A 0 := ⟨fun _ => b, IsLocallyConstant.const _⟩
  let b0 : (cochainsComplex A).X 0 := b0'
  have hlc0 : IsLocallyConstant ((inhomogeneousCochains.d A 0).hom (b0' : (Fin 0 → G) → A)) :=
    isLocallyConstant_d A b0'.2
  have hdd : (inhomogeneousCochains.d A 1).hom ((inhomogeneousCochains.d A 0).hom
      (b0' : (Fin 0 → G) → A)) = 0 :=
    congrArg (fun φ => ModuleCat.Hom.hom φ (b0' : (Fin 0 → G) → A))
      (inhomogeneousCochains.d_comp_d (A := A) (n := 0))
  have hzero : cocycleFun A z - (inhomogeneousCochains.d A 0).hom (b0' : (Fin 0 → G) → A) = 0 := by
    refine hσ.cocycle_eq_zero ((isLocallyConstant_cocycleFun A z).sub hlc0) ?_ ?_
    · rw [map_sub, d_cocycleFun, hdd, sub_zero]
    · rw [Pi.sub_apply, inhomogeneousD_zero_apply, ← hb]
      simp [b0']
  have hz : z = ((cochainsComplex A).toCycles 0 1).hom b0 := by
    apply cocycleFun_injective A
    rw [cocycleFun_toCycles]
    exact sub_eq_zero.1 hzero
  rw [hz]
  exact congrArg (fun φ => ModuleCat.Hom.hom φ b0) ((cochainsComplex A).toCycles_comp_homologyπ 0 1)
theorem H1Eval_surjective [CompactSpace G] {σ : G} (hσ : IsZHatGenerator σ)
    (hA : IsAddTorsion A) : Function.Surjective (H1Eval A σ).hom := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨f, hlc, hd, hfσ⟩ := hσ.exists_cocycle a (hA a)
  let x : locallyConstantCochains A 1 := ⟨f, hlc⟩
  have hx : ((cochainsComplex A).d 1 2).hom x = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, cochainsComplex_d]
    exact Subtype.ext hd
  refine ⟨(cohomologyπ A 1).hom ((cochainsComplex A).cyclesMk x 2 (by simp) hx), ?_⟩
  rw [H1Eval_cohomology_class_apply]
  have h : cocycleFun A ((cochainsComplex A).cyclesMk x 2 (by simp) hx) = f :=
    congrArg Subtype.val ((cochainsComplex A).i_cyclesMk x 2 (by simp) hx)
  rw [h, hfσ]
end H1
section Iso
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A] {σ : G}
theorem invariants_eq_ker (hσ : IsTopologicalGenerator σ) :
    A.ρ.invariants = LinearMap.ker (A.ρ σ - 1) := by
  ext a
  rw [Representation.mem_invariants, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]
  refine ⟨fun h => h σ, fun h g => ?_⟩
  have hσa : σ ∈ stabilizer A.ρ a := h
  have htop := hσ.eq_top_of_isOpen _ (isOpen_stabilizer A a) hσa
  have hg : g ∈ stabilizer A.ρ a := htop ▸ Subgroup.mem_top g
  exact hg
noncomputable def H0IsoKer (hσ : IsTopologicalGenerator σ) :
    cohomology A 0 ≅ ModuleCat.of k (LinearMap.ker (A.ρ σ - 1)) :=
  H0Iso A ≪≫ (LinearEquiv.ofEq _ _ (invariants_eq_ker A hσ)).toModuleIso
variable [CompactSpace G]
noncomputable def H1Iso (hσ : IsZHatGenerator σ) (hA : IsAddTorsion A) :
    cohomology A 1 ≅ ModuleCat.of k (A ⧸ LinearMap.range (A.ρ σ - 1)) :=
  (LinearEquiv.ofBijective (H1Eval A σ).hom
    ⟨H1Eval_injective A hσ.dense, H1Eval_surjective A hσ hA⟩).toModuleIso
end Iso
section Vanishing
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable {σ : G}
end Vanishing
section Dimension
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {σ : G}
end Dimension
end GroundTheory.ProfCoh


