-- Prove2me | solution 1 for Algebra.PatchingLevel.free_and_ker_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4149cb92-faf3-5863-8e81-7022645f6d25

import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_Algebra_PatchingDatum
import Theorems.Thm_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
import Theorems.Thm_MvPowerSeries_isRegular_C_cons_X
import Theorems.Thm_MvPowerSeries_ofList_C_cons_X_eq_maximalIdeal
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_PatchingLevel_free_and_ker_eq_span

namespace PDescent

open MvPowerSeries IsLocalRing RingTheory.Sequence

variable {𝒪 : Type} [CommRing 𝒪]
variable {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
variable {M : Type} [AddCommGroup M] [Module R M]

local notation "B" => MvPowerSeries (Fin r) 𝒪
local notation "Level" => Algebra.PatchingLevel 𝒪 r R M ⊥

noncomputable def I (L : Level) : Ideal B := Ideal.span (Set.range fun i : Fin r => L.φ (X i))

theorem I_le_ker (L : Level) : I L ≤ RingHom.ker L.ψ := by
  rw [I, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact (RingHom.mem_ker).mpr (L.ψ_φ_X i)

theorem ker_π_iff (L : Level) (x : L.N) : L.π x = 0 ↔ x ∈ (I L • ⊤ : Submodule B L.N) := L.ker_π x

noncomputable def theta (L : Level) : (Fin L.d → B) →+ L.N where
  toFun c := ∑ i, L.φ (c i) • L.b i
  map_zero' := by simp
  map_add' c c' := by simp [Finset.sum_add_distrib, add_smul]

theorem theta_apply (L : Level) (c : Fin L.d → B) : theta L c = ∑ i, L.φ (c i) • L.b i := rfl

theorem theta_smul (L : Level) (a : B) (c : Fin L.d → B) : theta L (a • c) = L.φ a • theta L c := by
  simp only [theta_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem theta_injective (L : Level) : Function.Injective (theta L) := by
  refine (injective_iff_map_eq_zero (theta L)).mpr fun c hc => ?_
  funext i
  exact (Submodule.mem_bot B).mp (((L.b_rel c).mp hc) i)

theorem theta_bijective (L : Level) : Function.Bijective (theta L) :=
  ⟨theta_injective L, fun x => by obtain ⟨c, hc⟩ := L.b_span x; exact ⟨c, hc.symm⟩⟩

noncomputable def thetaEquiv (L : Level) : (Fin L.d → B) ≃+ L.N :=
  AddEquiv.ofBijective (theta L) (theta_bijective L)

theorem span_range_b (L : Level) : Submodule.span B (Set.range L.b) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨c, rfl⟩ := (theta_bijective L).2 x
  rw [theta_apply]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Set.mem_range_self i)

theorem finite_N (L : Level) : Module.Finite B L.N :=
  ⟨Submodule.fg_def.mpr ⟨Set.range L.b, Set.finite_range _, span_range_b L⟩⟩

section Nontrivial

variable [Nontrivial M]

theorem nontrivial_R (_L : Level) : Nontrivial R := Module.nontrivial R M

theorem nontrivial_N (L : Level) : Nontrivial L.N :=
  L.π_surjective.nontrivial

theorem d_pos (L : Level) : 0 < L.d := by
  rcases Nat.eq_zero_or_pos L.d with h | h
  · exfalso
    haveI := nontrivial_N L
    obtain ⟨x, hx⟩ := exists_ne (0 : L.N)
    obtain ⟨c, rfl⟩ := (theta_bijective L).2 x
    apply hx
    rw [theta_apply]
    exact Finset.sum_eq_zero fun i _ => absurd i.2 (by omega)
  · exact h

theorem not_isUnit_of_ψ_eq_zero (L : Level) {f : B} (hf : L.ψ f = 0) : ¬IsUnit f := by
  haveI : Nontrivial R := nontrivial_R L
  rintro ⟨u, rfl⟩
  have h1 : L.ψ ((u⁻¹ : Bˣ) : B) * L.ψ (u : B) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [hf, mul_zero] at h1
  exact zero_ne_one h1

theorem phi_X_mem_maximalIdeal [IsLocalRing 𝒪] (L : Level) (i : Fin r) : L.φ (X i) ∈ maximalIdeal B :=
  (mem_maximalIdeal _).mpr (not_isUnit_of_ψ_eq_zero L (L.ψ_φ_X i))

end Nontrivial

noncomputable def s (L : Level) (ϖ : 𝒪) : List B := C ϖ :: List.ofFn fun i : Fin r => L.φ (X i)

theorem length_s (L : Level) (ϖ : 𝒪) : (s L ϖ).length = r + 1 := by
  simp [s]

omit [Algebra 𝒪 R] in

theorem isWeaklyRegular_pi {d : ℕ} {xs : List B} (hxs : IsWeaklyRegular B xs) :
    IsWeaklyRegular (Fin d → B) xs :=
  ((TensorProduct.rid B (Fin d → B)).isWeaklyRegular_congr xs).mp hxs.isWeaklyRegular_lTensor

theorem forall₂_s (L : Level) (ϖ : 𝒪) :
    List.Forall₂ (fun (a : B) (t : B) => ∀ c, thetaEquiv L (a • c) = t • thetaEquiv L c)
      (C ϖ :: List.ofFn (X : Fin r → B)) (s L ϖ) := by
  have key : ∀ a : B, ∀ c, thetaEquiv L (a • c) = L.φ a • thetaEquiv L c := fun a c => theta_smul L a c
  refine List.Forall₂.cons (fun c => ?_) ?_
  · rw [key, c_eq_algebraMap, AlgHom.commutes]
  · simp only [List.forall₂_iff_get, List.length_ofFn, List.get_eq_getElem, List.getElem_ofFn,
      true_and]
    intro i h₁ h₂ c
    exact key _ c

theorem isWeaklyRegular_s (L : Level) {ϖ : 𝒪} (hϖ : ϖ ∈ nonZeroDivisors 𝒪) (hu : ¬IsUnit ϖ) :
    IsWeaklyRegular L.N (s L ϖ) :=
  ((thetaEquiv L).isWeaklyRegular_congr (forall₂_s L ϖ)).mp
    (isWeaklyRegular_pi (MvPowerSeries.isRegular_C_cons_X r hϖ hu).toIsWeaklyRegular)

theorem s_subset_maximalIdeal [IsLocalRing 𝒪] (L : Level) [Nontrivial M] {ϖ : 𝒪} (hu : ¬IsUnit ϖ) :
    ∀ x ∈ s L ϖ, x ∈ maximalIdeal B := by
  intro x hx
  simp only [s, List.mem_cons, List.mem_ofFn] at hx
  rcases hx with rfl | ⟨i, rfl⟩
  · exact (mem_maximalIdeal _).mpr fun h => hu (by
      rw [isUnit_iff_constantCoeff, constantCoeff_C] at h; exact h)
  · exact phi_X_mem_maximalIdeal L i

@[reducible] noncomputable def moduleO (L : Level) : Module 𝒪 L.N :=
  Module.compHom L.N (algebraMap 𝒪 B)

attribute [local instance] moduleO

theorem isScalarTower_O (L : Level) : IsScalarTower 𝒪 B L.N :=
  ⟨fun c f n => by
    change (c • f) • n = algebraMap 𝒪 B c • (f • n)
    rw [Algebra.smul_def, mul_smul]⟩

theorem smulO_def (L : Level) (c : 𝒪) (n : L.N) : c • n = (C c : B) • n := rfl

attribute [local instance] isScalarTower_O

omit [Algebra 𝒪 R] in

theorem sub_C_constantCoeff_mem_span_X (c : B) :
    c - C (constantCoeff c) ∈ Ideal.span (Set.range (X : Fin r → B)) := by
  have h := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 (c - C (constantCoeff c)) fun m hm => by
    obtain rfl : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (Nat.lt_one_iff.mp hm)
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, constantCoeff_C, sub_self]
  rwa [pow_one] at h

theorem phi_sub_C_mem_I (L : Level) (c : B) : L.φ (c - C (constantCoeff c)) ∈ I L := by
  have h : Ideal.map L.φ (Ideal.span (Set.range (X : Fin r → B))) ≤ I L := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  exact h (Ideal.mem_map_of_mem _ (sub_C_constantCoeff_mem_span_X c))

theorem exists_sub_sum_mem (L : Level) (x : L.N) :
    ∃ c₀ : Fin L.d → 𝒪, x - ∑ i, c₀ i • L.b i ∈ (I L • ⊤ : Submodule B L.N) := by
  obtain ⟨c, rfl⟩ := (theta_bijective L).2 x
  refine ⟨fun i => constantCoeff (c i), ?_⟩
  rw [theta_apply, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hC : (C (constantCoeff (c i)) : B) = L.φ (C (constantCoeff (c i))) := by
    rw [c_eq_algebraMap, AlgHom.commutes]
  rw [smulO_def, ← sub_smul, hC, ← map_sub]
  exact Submodule.smul_mem_smul (phi_sub_C_mem_I L (c i)) Submodule.mem_top

theorem I_le_ofList (L : Level) (ϖ : 𝒪) : I L ≤ Ideal.ofList (s L ϖ) := by
  rw [I, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.subset_span (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem C_mem_ofList (L : Level) (ϖ : 𝒪) : (C ϖ : B) ∈ Ideal.ofList (s L ϖ) :=
  Ideal.subset_span (List.mem_cons_self)

theorem isFiniteLength_quotient [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (L : Level) {ϖ : 𝒪}
    (hϖ : maximalIdeal 𝒪 = Ideal.span {ϖ}) :
    IsFiniteLength B (L.N ⧸ (Ideal.ofList (s L ϖ) • ⊤ : Submodule B L.N)) := by
  set P : Submodule B L.N := Ideal.ofList (s L ϖ) • ⊤ with hP

  have hgen : Submodule.span 𝒪 (Set.range fun i => (Submodule.Quotient.mk (L.b i) : L.N ⧸ P)) = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
    obtain ⟨c₀, hc₀⟩ := exists_sub_sum_mem L x
    have hx : (Submodule.Quotient.mk x : L.N ⧸ P) = ∑ i, c₀ i • Submodule.Quotient.mk (L.b i) := by
      have h := (Submodule.Quotient.eq P).mpr (Submodule.smul_mono_left (I_le_ofList L ϖ) hc₀)
      rw [h, ← Submodule.mkQ_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  haveI hfin : Module.Finite 𝒪 (L.N ⧸ P) :=
    ⟨Submodule.fg_def.mpr ⟨_, Set.finite_range _, hgen⟩⟩

  have hT : Module.IsTorsionBySet 𝒪 (L.N ⧸ P) (maximalIdeal 𝒪 : Set 𝒪) := by
    rintro q ⟨a, ha⟩
    obtain ⟨t, rfl⟩ : ∃ t, t * ϖ = a := by
      have ha' : a ∈ Ideal.span {ϖ} := hϖ ▸ ha
      exact Ideal.mem_span_singleton'.mp ha'
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
    change (t * ϖ) • Submodule.Quotient.mk x = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul, smulO_def L ϖ]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul (C_mem_ofList L ϖ) Submodule.mem_top)

  letI : Module (𝒪 ⧸ maximalIdeal 𝒪) (L.N ⧸ P) := hT.module
  haveI : IsScalarTower 𝒪 (𝒪 ⧸ maximalIdeal 𝒪) (L.N ⧸ P) :=
    ⟨fun a b q => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Module.IsTorsionBySet.mk_smul,
        Module.IsTorsionBySet.mk_smul, mul_smul]⟩
  haveI : Module.Finite (𝒪 ⧸ maximalIdeal 𝒪) (L.N ⧸ P) :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _
  letI : Field (𝒪 ⧸ maximalIdeal 𝒪) := Ideal.Quotient.field _
  have hA : IsArtinian 𝒪 (L.N ⧸ P) :=
    isArtinian_of_surjective_algebraMap (R := 𝒪 ⧸ maximalIdeal 𝒪) Ideal.Quotient.mk_surjective
  have hNo : IsNoetherian 𝒪 (L.N ⧸ P) := inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower 𝒪 hNo, isArtinian_of_tower 𝒪 hA⟩

theorem free_N [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (L : Level) [Nontrivial M] :
    Module.Free B L.N := by
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hϖ : maximalIdeal 𝒪 = Ideal.span {ϖ} := hirr.maximalIdeal_eq
  have hnz : ϖ ∈ nonZeroDivisors 𝒪 := mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  have hu : ¬IsUnit ϖ := hirr.not_isUnit
  haveI : IsNoetherianRing B := MvPowerSeries.isNoetherianRing_of_finite
  haveI := finite_N L
  exact Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
    (C ϖ :: List.ofFn (X : Fin r → B)) (MvPowerSeries.isRegular_C_cons_X r hnz hu)
    (MvPowerSeries.ofList_C_cons_X_eq_maximalIdeal r hϖ) (s L ϖ) (s_subset_maximalIdeal L hu)
    (isWeaklyRegular_s L hnz hu) (by simp [s]) (isFiniteLength_quotient L hϖ)

omit [Algebra 𝒪 R] in

theorem apply_mem_of_mem_smul_top {N : Type} [AddCommGroup N] [Module B N] (J : Ideal B)
    (lam : N →ₗ[B] B) {x : N} (hx : x ∈ (J • ⊤ : Submodule B N)) : lam x ∈ J := by
  refine Submodule.smul_induction_on hx (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, smul_eq_mul]; exact J.mul_mem_right _ ha
  · rw [map_add]; exact J.add_mem hx hy

theorem smul_mem_of_mem_ker (L : Level) {f : B} (hf : f ∈ RingHom.ker L.ψ) (x : L.N) :
    f • x ∈ (I L • ⊤ : Submodule B L.N) := by
  rw [← ker_π_iff, L.π_smul, RingHom.mem_ker.mp hf, zero_smul]

theorem ker_le_I [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (L : Level) [Nontrivial M] :
    RingHom.ker L.ψ ≤ I L := by
  haveI := free_N L
  haveI := nontrivial_N L
  intro f hf
  let e := Module.Free.chooseBasis B L.N
  obtain ⟨i₀⟩ := e.index_nonempty
  have h : e.coord i₀ (f • e i₀) = f := by
    rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul,
      mul_one]
  rw [← h]
  exact apply_mem_of_mem_smul_top (I L) (e.coord i₀) (smul_mem_of_mem_ker L hf _)

theorem free_M [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (L : Level) [Nontrivial M] :
    Module.Free R M := by
  haveI := free_N L
  haveI := finite_N L
  let e := Module.Free.chooseBasis B L.N

  have hsp : ⊤ ≤ Submodule.span R (Set.range fun i => L.π (e i)) := by
    rintro m -
    obtain ⟨x, rfl⟩ := L.π_surjective m
    rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [L.π_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hli : LinearIndependent R fun i => L.π (e i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose f hf using fun i => L.ψ_surjective (g i)
    have hx : (∑ j, f j • e j) ∈ (I L • ⊤ : Submodule B L.N) := by
      rw [← ker_π_iff, map_sum]
      rw [← hg]
      exact Finset.sum_congr rfl fun j _ => by rw [L.π_smul, hf]
    have hfi : f i ∈ I L := by
      have h := apply_mem_of_mem_smul_top (I L) (e.coord i) hx
      rwa [Module.Basis.coord_apply, e.repr_sum_self] at h
    rw [← hf i]
    exact RingHom.mem_ker.mp (I_le_ker L hfi)
  exact Module.Free.of_basis (Module.Basis.mk hli hsp)

end PDescent

open PDescent in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (L : Algebra.PatchingLevel 𝒪 r R M ⊥) :
    Module.Free R M ∧ Module.annihilator R M = ⊥ ∧
      RingHom.ker L.ψ = Ideal.span (Set.range fun i : Fin r => L.φ (MvPowerSeries.X i)) := by
  haveI := free_M L
  exact ⟨free_M L, Module.annihilator_eq_bot.mpr inferInstance,
    le_antisymm (ker_le_I L) (I_le_ker L)⟩

end S_Algebra_PatchingLevel_free_and_ker_eq_span
end P2MW
export P2MW.S_Algebra_PatchingLevel_free_and_ker_eq_span (solution)
