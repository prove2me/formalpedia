-- Prove2me | solution 1 for AddCommGroup.moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/971f1c83-16a1-5c49-9b09-c55c52d48ac8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul

set_option autoImplicit false

namespace P2mEndFG

open Module

variable {R : Type*} [AddCommGroup R]

def Saturated (S : AddSubgroup R) : Prop := ∀ (k : ℤ) (x : R), k ≠ 0 → k • x ∈ S → x ∈ S

theorem saturated_of_iff {M M' : AddSubgroup R}
    (h : ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M) : M ≤ M' ∧ Saturated M' := by
  refine ⟨fun x hx => (h x).2 ⟨1, one_ne_zero, by simpa using hx⟩, ?_⟩
  intro k x hk hkx
  obtain ⟨k', hk', hk'x⟩ := (h _).1 hkx
  exact (h x).2 ⟨k' * k, mul_ne_zero hk' hk, by simpa [mul_smul] using hk'x⟩

section Bound

variable [IsAddTorsionFree R]
variable {G : Type*} [AddCommGroup G] [Finite G] (ρ : R →+ G) (n : ℕ)
  (hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y)

include hρ in

theorem pow_finrank_le_card (S : AddSubgroup R) (hS : Saturated S) (hfg : S.FG) (hn : n ≠ 0) :
    n ^ finrank ℤ S ≤ Nat.card G := by
  haveI : Module.Finite ℤ S :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg S).mpr hfg)
  haveI : IsAddTorsionFree S := inferInstance
  haveI : Module.Free ℤ S := Module.free_of_finite_type_torsion_free'

  set ρ' : S →+ G := ρ.comp S.subtype with hρ'

  have hker : ρ'.ker ≤ (nsmulAddMonoidHom (α := S) n).range := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    obtain ⟨y, hy⟩ := hρ (x : R) hx
    have hyS : y ∈ S := by
      refine hS n y (by exact_mod_cast hn) ?_
      rw [natCast_zsmul, ← hy]
      exact x.2
    refine ⟨⟨y, hyS⟩, ?_⟩
    apply Subtype.ext
    simp [hy]
  have h1 : (nsmulAddMonoidHom (α := S) n).range.index = n ^ finrank ℤ S :=
    AddSubgroup.index_range_nsmul S n
  have h2 : (nsmulAddMonoidHom (α := S) n).range.index ∣ ρ'.ker.index :=
    AddSubgroup.index_dvd_of_le hker
  have h3 : ρ'.ker.index = Nat.card ρ'.range := AddSubgroup.index_ker ρ'
  have h4 : Nat.card ρ'.range ≤ Nat.card G :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have h5 : Nat.card ρ'.range ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨0, zero_mem _⟩, inferInstance⟩
  calc n ^ finrank ℤ S = (nsmulAddMonoidHom (α := S) n).range.index := h1.symm
    _ ≤ ρ'.ker.index := Nat.le_of_dvd (by rw [h3]; exact Nat.pos_of_ne_zero h5) h2
    _ = Nat.card ρ'.range := h3
    _ ≤ Nat.card G := h4

end Bound

theorem linearIndependent_cod {ι : Type*} (S : AddSubgroup R) (v : ι → R)
    (hv : LinearIndependent ℤ v) (hmem : ∀ i, v i ∈ S) :
    LinearIndependent ℤ (fun i => (⟨v i, hmem i⟩ : S)) := by
  refine LinearIndependent.of_comp S.subtype.toIntLinearMap ?_
  exact hv

theorem main [IsAddTorsionFree R]
    (hsat : ∀ M : AddSubgroup R, M.FG →
      ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M)
    {G : Type*} [AddCommGroup G] [Finite G] (ρ : R →+ G) (n : ℕ) (hn : 1 < n)
    (hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y) :
    Module.Finite ℤ R ∧ Module.Free ℤ R := by
  classical
  have hn0 : n ≠ 0 := by omega

  have hbound : ∀ s : Finset R, LinearIndependent ℤ ((↑) : s → R) → s.card < Nat.card G := by
    intro s hs
    obtain ⟨M', hM'fg, hM'⟩ := hsat (Submodule.span ℤ (s : Set R)).toAddSubgroup
      (by
        rw [← Submodule.fg_iff_addSubgroup_fg]
        exact Submodule.fg_span s.finite_toSet)
    obtain ⟨hle, hsatM'⟩ := saturated_of_iff hM'
    have hmem : ∀ i : s, (i : R) ∈ M' := fun i =>
      hle (Submodule.subset_span (by exact_mod_cast i.2))
    haveI : Module.Finite ℤ M' :=
      Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg M').mpr hM'fg)
    have hli : LinearIndependent ℤ (fun i : s => (⟨(i : R), hmem i⟩ : M')) :=
      linearIndependent_cod M' _ hs hmem
    have hcard : s.card ≤ finrank ℤ M' := by
      simpa using hli.fintype_card_le_finrank
    have hpow : n ^ finrank ℤ M' ≤ Nat.card G := pow_finrank_le_card ρ n hρ M' hsatM' hM'fg hn0
    calc s.card < n ^ s.card := Nat.lt_pow_self hn
      _ ≤ n ^ finrank ℤ M' := Nat.pow_le_pow_right (by omega) hcard
      _ ≤ Nat.card G := hpow

  obtain ⟨I, hIli, hImax⟩ := exists_maximal_linearIndepOn ℤ (id : R → R)
  have hIfin : I.Finite := by
    by_contra hinf
    obtain ⟨t, htI, htcard⟩ := Set.Infinite.exists_subset_card_eq hinf (Nat.card G)
    have hli : LinearIndependent ℤ ((↑) : t → R) := by
      have := hIli.mono htI
      exact this.linearIndependent
    exact absurd (htcard ▸ hbound t hli) (lt_irrefl _)

  set M : AddSubgroup R := (Submodule.span ℤ I).toAddSubgroup with hMdef
  have hMfg : M.FG := by
    rw [hMdef, ← Submodule.fg_iff_addSubgroup_fg]
    exact Submodule.fg_span hIfin
  obtain ⟨M', hM'fg, hM'⟩ := hsat M hMfg
  obtain ⟨hle, hsatM'⟩ := saturated_of_iff hM'
  have htop : M' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hx : x ∈ I
    · exact hle (Submodule.subset_span hx)
    · obtain ⟨a, ha, hax⟩ := hImax x hx
      refine hsatM' a x ha (hle ?_)
      simpa [hMdef] using hax
  have hfgtop : (⊤ : AddSubgroup R).FG := htop ▸ hM'fg
  haveI hfin : Module.Finite ℤ R :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_def).mpr hfgtop)
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

end P2mEndFG

theorem solution
    {R : Type*} [AddCommGroup R] [IsAddTorsionFree R]
    (hsat : ∀ M : AddSubgroup R, M.FG →
      ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M)
    {G : Type*} [AddCommGroup G] [Finite G] (ρ : R →+ G) (n : ℕ) (hn : 1 < n)
    (hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y) :
    Module.Finite ℤ R ∧ Module.Free ℤ R :=
  P2mEndFG.main hsat ρ n hn hρ

end S_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul
end P2MW
export P2MW.S_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul (solution)
