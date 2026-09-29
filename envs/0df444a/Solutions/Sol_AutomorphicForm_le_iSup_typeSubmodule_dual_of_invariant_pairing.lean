-- Prove2me | solution 1 for AutomorphicForm.le_iSup_typeSubmodule_dual_of_invariant_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/564846bd-d678-530e-b78f-17beb6aa4e20

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_Representation_exists_extend_forall_apply_mul_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing

set_option autoImplicit false

open AutomorphicForm

noncomputable section

namespace PairToDualType

section Pair
variable {K : Type*} [Group K] {G : Type*} [Group G]

private abbrev TW (ι : K →* G) {n : ℕ} (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ K (W i)) : Type _ :=
  Σ i : Fin n, {T₀ : W i →ₗ[ℂ] (G → ℂ) // ∀ (k : K) (v : W i) (x : G), T₀ (ρ i k v) x = T₀ v (x * ι k)}

private theorem exists_finset_of_mem_iSup_span (ι : K →* G) {n : ℕ} (W : Fin n → Type*) [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i)) {s : G → ℂ}
    (hs : s ∈ ⨆ i, typeSubmodule ι (ρ i)) :
    ∃ J : Finset (TW ι W ρ), s ∈ ⨆ j ∈ J, LinearMap.range j.2.1 := by
  classical
  have mono : ∀ (A B : Finset (TW ι W ρ)), A ⊆ B →
      (⨆ j ∈ A, LinearMap.range j.2.1) ≤ ⨆ j ∈ B, LinearMap.range j.2.1 := fun A B h =>
    biSup_mono fun j hj => h hj
  refine Submodule.iSup_induction _
    (motive := fun s => ∃ J : Finset (TW ι W ρ), s ∈ ⨆ j ∈ J, LinearMap.range j.2.1) hs ?_ ?_ ?_
  · intro i f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro f ⟨T₀, hT₀, hfT⟩
      refine ⟨{⟨i, T₀, hT₀⟩}, ?_⟩
      simp only [Finset.mem_singleton, iSup_iSup_eq_left]
      exact hfT
    · exact ⟨∅, by simp⟩
    · rintro a b - - ⟨Ja, ha⟩ ⟨Jb, hb⟩
      exact ⟨Ja ∪ Jb, Submodule.add_mem _ (mono _ _ Finset.subset_union_left ha) (mono _ _ Finset.subset_union_right hb)⟩
    · rintro c a - ⟨J, ha⟩
      exact ⟨J, Submodule.smul_mem _ c ha⟩
  · exact ⟨∅, by simp⟩
  · rintro a b ⟨Ja, ha⟩ ⟨Jb, hb⟩
    exact ⟨Ja ∪ Jb, Submodule.add_mem _ (mono _ _ Finset.subset_union_left ha) (mono _ _ Finset.subset_union_right hb)⟩

end Pair

end PairToDualType

open PairToDualType in
theorem solution
    {K : Type*} [Group K] {G : Type*} [Group G]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ}
    (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i))
    (S T : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k : K, ∀ s ∈ S, (fun x => s (x * ι k)) ∈ S) (hT : ∀ k : K, ∀ t ∈ T, (fun x => t (x * ι k)) ∈ T)
    (β : S →ₗ[ℂ] T →ₗ[ℂ] ℂ)
    (hβ : ∀ (k : K) (s : S) (t : T), β ⟨fun x => (s : G → ℂ) (x * ι k), hS k s s.2⟩ ⟨fun x => (t : G → ℂ) (x * ι k), hT k t t.2⟩ = β s t)
    (hnd : ∀ t : T, (∀ s : S, β s t = 0) → t = 0)
    (hSle : S ≤ ⨆ i, typeSubmodule ι (ρ i)) :
    T ≤ ⨆ i, typeSubmodule ι (ρ i).dual := by
  classical

  obtain ⟨J, hJ⟩ : ∃ J : Finset (TW ι W ρ), S ≤ ⨆ j ∈ J, LinearMap.range j.2.1 := by
    let b := Module.finBasis ℂ S
    choose Jf hJf using fun l => exists_finset_of_mem_iSup_span ι W ρ (hSle (b l).2)
    refine ⟨Finset.univ.biUnion Jf, ?_⟩
    have mono : ∀ (A B : Finset (TW ι W ρ)), A ⊆ B →
        (⨆ j ∈ A, LinearMap.range j.2.1) ≤ ⨆ j ∈ B, LinearMap.range j.2.1 := fun A B h =>
      biSup_mono fun j hj => h hj
    intro s hs
    have hs' : (⟨s, hs⟩ : S) ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
    have hs'' : s ∈ Submodule.span ℂ (Set.range fun l => (b l : G → ℂ)) := by
      have := Submodule.mem_map_of_mem (f := S.subtype) hs'
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact this
    refine (Submodule.span_le.mpr ?_) hs''
    rintro _ ⟨l, rfl⟩
    exact mono _ _ (Finset.subset_biUnion_of_mem Jf (Finset.mem_univ l)) (hJf l)

  let WJ : Type _ := ∀ j : J, W j.1.1
  let ρJ : Representation ℂ K WJ :=
    { toFun := fun k => LinearMap.pi fun j => ((ρ j.1.1) k) ∘ₗ LinearMap.proj j
      map_one' := by ext x j; simp
      map_mul' := fun a c => by ext x j; simp }
  have hρJ : ∀ (k : K) (x : WJ) (j : J), ρJ k x j = (ρ j.1.1) k (x j) := fun k x j => rfl
  let TJ : WJ →ₗ[ℂ] (G → ℂ) := ∑ j : J, (j.1.2.1) ∘ₗ LinearMap.proj j
  have hTJ_apply : ∀ x : WJ, TJ x = ∑ j : J, j.1.2.1 (x j) := fun x => by
    simp only [TJ, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  have hTJ : ∀ (k : K) (x : WJ) (y : G), TJ (ρJ k x) y = TJ x (y * ι k) := by
    intro k x y
    simp only [hTJ_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hρJ]; exact j.1.2.2 k (x j) y
  have hSrange : S ≤ LinearMap.range TJ := by
    refine hJ.trans (iSup₂_le fun j hj => ?_)
    rintro _ ⟨v, rfl⟩
    refine ⟨Pi.single ⟨j, hj⟩ v, ?_⟩
    rw [hTJ_apply, Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro j' _ hj'; simp [Pi.single_eq_of_ne hj']
    · simp

  let P : Submodule ℂ WJ := S.comap TJ
  have hP : ∀ k : K, ∀ x ∈ P, ρJ k x ∈ P := by
    intro k x hx
    show TJ (ρJ k x) ∈ S
    have : TJ (ρJ k x) = fun y => (TJ x) (y * ι k) := funext fun y => hTJ k x y
    rw [this]; exact hS k _ hx
  let Psub : Subrepresentation ρJ := ⟨P, fun k x hx => hP k x hx⟩
  let ρP : Representation ℂ K P := Psub.toRepresentation
  have hρP : ∀ (k : K) (p : P), ((ρP k p : P) : WJ) = ρJ k p := fun k p => rfl

  let D : T →ₗ[ℂ] Module.Dual ℂ P :=
    { toFun := fun t =>
        { toFun := fun p => β ⟨TJ p, p.2⟩ t
          map_add' := fun p p' => by
            have : (⟨TJ ((p + p' : P) : WJ), (p + p').2⟩ : S) = ⟨TJ p, p.2⟩ + ⟨TJ p', p'.2⟩ :=
              Subtype.ext (by simp)
            rw [this, map_add, LinearMap.add_apply]
          map_smul' := fun c p => by
            have : (⟨TJ ((c • p : P) : WJ), (c • p).2⟩ : S) = c • ⟨TJ p, p.2⟩ := Subtype.ext (by simp)
            rw [this, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
      map_add' := fun t t' => by ext p; simp
      map_smul' := fun c t => by ext p; simp }
  have hD : ∀ (t : T) (p : P), D t p = β ⟨TJ p, p.2⟩ t := fun t p => rfl

  let R : K → T → T := fun k t => ⟨fun x => (t : G → ℂ) (x * ι k), hT k t t.2⟩

  have hDeq : ∀ (k : K) (t : T), ρP.dual k (D t) = D (R k t) := by
    intro k t
    apply LinearMap.ext
    intro p
    simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hD]

    have h1 : (⟨TJ ((ρP k⁻¹ p : P) : WJ), (ρP k⁻¹ p).2⟩ : S) =
        ⟨fun x => (TJ (p : WJ)) (x * ι k⁻¹), hS k⁻¹ _ p.2⟩ := by
      apply Subtype.ext
      funext x
      show TJ ((ρP k⁻¹ p : P) : WJ) x = TJ (p : WJ) (x * ι k⁻¹)
      rw [hρP, hTJ]
    rw [h1, ← hβ k]
    have h2 : (⟨fun x => (fun x => (TJ (p : WJ)) (x * ι k⁻¹)) (x * ι k), hS k _ (hS k⁻¹ _ p.2)⟩ : S) = ⟨TJ p, p.2⟩ := by
      apply Subtype.ext
      funext x
      show TJ (p : WJ) (x * ι k * ι k⁻¹) = TJ (p : WJ) x
      rw [map_inv, mul_inv_cancel_right]
    rw [h2]

  have hDinj : Function.Injective D := by
    intro t t' h
    rw [← sub_eq_zero]
    apply hnd
    intro s
    obtain ⟨x, hx⟩ : ∃ x : WJ, TJ x = s := hSrange s.2
    have hxP : x ∈ P := by show TJ x ∈ S; rw [hx]; exact s.2
    have := congrArg (fun φ : Module.Dual ℂ P => φ ⟨x, hxP⟩) h
    simp only [hD] at this
    have hs : (⟨TJ x, hxP⟩ : S) = s := Subtype.ext hx
    rw [hs] at this
    rw [map_sub, this, sub_self]

  let Q : Submodule ℂ (Module.Dual ℂ P) := LinearMap.range D
  have hQ : ∀ k : K, ∀ φ ∈ Q, ρP.dual k φ ∈ Q := by
    rintro k _ ⟨t, rfl⟩
    exact ⟨R k t, (hDeq k t).symm⟩
  let eD : T ≃ₗ[ℂ] Q := LinearEquiv.ofInjective D hDinj
  let f : Q →ₗ[ℂ] (G → ℂ) := T.subtype ∘ₗ eD.symm.toLinearMap
  have hfD : ∀ t : T, f ⟨D t, ⟨t, rfl⟩⟩ = t := by
    intro t
    show ((eD.symm ⟨D t, ⟨t, rfl⟩⟩ : T) : G → ℂ) = t
    have : (⟨D t, ⟨t, rfl⟩⟩ : Q) = eD t := rfl
    rw [this, LinearEquiv.symm_apply_apply]
  have hf : ∀ (k : K) (φ : Q) (x : G), f ⟨ρP.dual k φ, hQ k φ φ.2⟩ x = f φ (x * ι k) := by
    rintro k ⟨_, ⟨t, rfl⟩⟩ x
    have h1 : (⟨ρP.dual k (D t), hQ k (D t) ⟨t, rfl⟩⟩ : Q) = ⟨D (R k t), ⟨R k t, rfl⟩⟩ := Subtype.ext (hDeq k t)
    rw [h1, hfD, hfD]
  obtain ⟨T', hT'eq, hT'ext⟩ := Representation.exists_extend_forall_apply_mul_of_injective ι hι ρP.dual Q hQ f hf

  let res : Module.Dual ℂ WJ →ₗ[ℂ] Module.Dual ℂ P := P.dualRestrict
  have hres : ∀ (k : K) (φ : Module.Dual ℂ WJ), res (ρJ.dual k φ) = ρP.dual k (res φ) := by
    intro k φ
    apply LinearMap.ext
    intro p
    simp only [res, Submodule.dualRestrict_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply, hρP]
  let T'' : Module.Dual ℂ WJ →ₗ[ℂ] (G → ℂ) := T' ∘ₗ res
  have hT'' : ∀ (k : K) (φ : Module.Dual ℂ WJ) (x : G), T'' (ρJ.dual k φ) x = T'' φ (x * ι k) := by
    intro k φ x
    show T' (res (ρJ.dual k φ)) x = T' (res φ) (x * ι k)
    rw [hres, hT'eq]
  intro t ht

  obtain ⟨φ, hφ⟩ := Subspace.dualRestrict_surjective (W := P) (D ⟨t, ht⟩)
  have ht_eq : t = T'' φ := by
    show t = T' (res φ)
    change t = T' (P.dualRestrict φ)
    rw [hφ]
    have := hT'ext ⟨D ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩⟩
    rw [hfD] at this
    exact this.symm

  have hsplit : φ = ∑ j : J, (φ ∘ₗ LinearMap.single ℂ (fun j : J => W j.1.1) j) ∘ₗ LinearMap.proj j := by
    apply LinearMap.ext
    intro x
    conv_lhs => rw [show x = ∑ j : J, Pi.single j (x j) from (Finset.univ_sum_single x).symm]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  rw [ht_eq, hsplit, map_sum]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j.1.1 (Submodule.subset_span ?_)

  refine ⟨T'' ∘ₗ (LinearMap.proj (R := ℂ) (φ := fun j : J => W j.1.1) j).dualMap, ?_, ?_⟩
  · intro k ψ x
    show T'' ((LinearMap.proj (R := ℂ) (φ := fun j : J => W j.1.1) j).dualMap ((ρ j.1.1).dual k ψ)) x =
      T'' ((LinearMap.proj (R := ℂ) (φ := fun j : J => W j.1.1) j).dualMap ψ) (x * ι k)
    have hψ : (LinearMap.proj (R := ℂ) (φ := fun j : J => W j.1.1) j).dualMap ((ρ j.1.1).dual k ψ) =
        ρJ.dual k ((LinearMap.proj (R := ℂ) (φ := fun j : J => W j.1.1) j).dualMap ψ) := by
      apply LinearMap.ext
      intro y
      show ψ ((ρ j.1.1) k⁻¹ (y j)) = ψ ((ρJ k⁻¹ y) j)
      rfl
    rw [hψ, hT'']
  · refine ⟨φ ∘ₗ LinearMap.single ℂ (fun j : J => W j.1.1) j, ?_⟩
    rw [LinearMap.comp_apply, LinearMap.dualMap_apply']

end

end S_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing
end P2MW
export P2MW.S_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing (solution)
