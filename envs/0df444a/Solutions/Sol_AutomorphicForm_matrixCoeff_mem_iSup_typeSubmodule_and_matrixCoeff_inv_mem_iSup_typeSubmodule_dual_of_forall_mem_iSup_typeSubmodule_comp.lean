-- Prove2me | solution 1 for AutomorphicForm.matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9bf98bf1-185b-5615-a9b2-e65a7b9d7511

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp

set_option autoImplicit false

section Carry3

noncomputable section

namespace KcCentralRepro

open AutomorphicForm

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  rw [hmk, map_mul, ← mul_assoc, out_mul_cosetCoord]

theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ (k : H), ∀ v ∈ P, ρ k v ∈ P)
    (S : P →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : P) (x : G), S ⟨ρ k v, hP k v v.2⟩ x = S v (x * ι k)) (v : P) :
    S v ∈ AutomorphicForm.typeSubmodule ι ρ := by
  classical

  let ℓ : G ⧸ ι.range → (P →ₗ[ℂ] ℂ) := fun c =>
    { toFun := fun p => S p c.out
      map_add' := fun p q => by rw [map_add]; rfl
      map_smul' := fun a p => by rw [map_smul]; rfl }
  have hext : ∀ c, ∃ g : W →ₗ[ℂ] ℂ, g.comp P.subtype = ℓ c := fun c => LinearMap.exists_extend (ℓ c)
  let ℓ' : G ⧸ ι.range → (W →ₗ[ℂ] ℂ) := fun c => (hext c).choose
  have hℓ' : ∀ c (p : P), ℓ' c (p : W) = S p c.out := fun c p => by
    have := LinearMap.congr_fun (hext c).choose_spec p
    simpa [ℓ] using this

  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) w)
      map_add' := fun w₁ w₂ => funext fun x => by simp only [map_add, Pi.add_apply]
      map_smul' := fun a w => funext fun x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hT : AutomorphicForm.IsRightEquivariant ι ρ T := by
    intro k w x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (ρ k w)) =
      ℓ' (QuotientGroup.mk (x * ι k)) (ρ (cosetCoord ι (x * ι k)) w)
    have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq]
      exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
    rw [hmk, cosetCoord_mul hι, map_mul]
    rfl
  have hTS : T (v : W) = S v := by
    funext x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (v : W)) = S v x
    have hmem : ρ (cosetCoord ι x) (v : W) ∈ P := hP _ _ v.2
    have h1 := hℓ' (QuotientGroup.mk x) ⟨_, hmem⟩
    simp only at h1
    rw [h1, hS (cosetCoord ι x) v, out_mul_cosetCoord]
  rw [← hTS]
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT _

end TypePiece

section PiRep

variable {H : Type*} [Group H]
variable {A : Type*} {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]

def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
    (v : W a) : piRep ρ k (Pi.single a v) = Pi.single a (ρ a k v) := by
  funext b
  rw [piRep_apply]
  by_cases hb : b = a
  · subst hb
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hb, map_zero]

end PiRep

section Transport

variable {H G : Type*} [Group H] [Group G]

theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] (ι : H →* G)
    (ρ : ∀ a, Representation ℂ H (W a)) :
    typeSubmodule ι (piRep ρ) ≤ ⨆ a, typeSubmodule ι (ρ a) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  show T v ∈ ⨆ a, typeSubmodule ι (ρ a)
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ?_
  have hTa : IsRightEquivariant ι (ρ a) (T.comp (LinearMap.single ℂ W a)) := by
    intro k w x
    show T (Pi.single a (ρ a k w)) x = T (Pi.single a w) (x * ι k)
    rw [← piRep_single]
    exact hT k (Pi.single a w) x
  exact mem_typeSubmodule_of_isRightEquivariant hTa (v a)

theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) {θ : G → ℂ} (hθ : θ ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ θ ∈ LinearMap.range Φ := by
  classical
  have h1 : θ ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hθ
  obtain ⟨t, ht, hθt⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hgen : ∀ f : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (f : G → ℂ) ∈ LinearMap.range T := fun f => by
    have hf := ht f.2
    rw [Set.mem_iUnion] at hf
    obtain ⟨j, T, hT, hfT⟩ := hf
    exact ⟨j, T, hT, hfT⟩
  choose i T hT hfT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · refine (Submodule.span_le.mpr ?_) hθt
    intro f hf
    obtain ⟨v, hv⟩ := hfT ⟨f, hf⟩
    refine ⟨Pi.single (⟨f, hf⟩ : t) v, ?_⟩
    rw [hΦ, Finset.sum_eq_single (⟨f, hf⟩ : t)]
    · rw [Pi.single_eq_same]
      exact hv
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G) {ι' : H →* G'}
    (hι' : Function.Injective ι') (ρ : ∀ j, Representation ℂ H (W j)) (P₀ : Submodule ℂ (G → ℂ))
    (hP₀ : ∀ (k : H), ∀ θ ∈ P₀, (fun x => θ (x * ι k)) ∈ P₀) (A : P₀ →ₗ[ℂ] (G' → ℂ))
    (hA : ∀ (k : H) (θ : P₀) (y : G'), A ⟨fun x => (θ : G → ℂ) (x * ι k), hP₀ k θ θ.2⟩ y =
      A θ (y * ι' k))
    (θ : P₀) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    A θ ∈ ⨆ j, typeSubmodule ι' (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, v, hv⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hθ
  have hQ : ∀ (k : H), ∀ w ∈ P₀.comap Φ, piRep (fun a => ρ (i a)) k w ∈ P₀.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι k) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hP₀ k _ hw
  let ΦQ : P₀.comap Φ →ₗ[ℂ] P₀ :=
    LinearMap.codRestrict P₀ (Φ.comp (P₀.comap Φ).subtype) fun w => w.2
  have hΦQ : ∀ w : P₀.comap Φ, ((ΦQ w : P₀) : G → ℂ) = Φ (w : ∀ a : t, W (i a)) := fun _ => rfl
  let S : P₀.comap Φ →ₗ[ℂ] (G' → ℂ) := A.comp ΦQ
  have hS : ∀ (k : H) (w : P₀.comap Φ) (y : G'),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ y = S w (y * ι' k) := by
    intro k w y
    have h1 : ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ =
        ⟨fun x => ((ΦQ w : P₀) : G → ℂ) (x * ι k), hP₀ k _ (ΦQ w).2⟩ := by
      apply Subtype.ext
      funext x
      exact hΦ k w x
    show A (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩) y = A (ΦQ w) (y * ι' k)
    rw [h1]
    exact hA k (ΦQ w) y
  have hv' : v ∈ P₀.comap Φ := by
    rw [Submodule.mem_comap, hv]
    exact θ.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hι' (fun a => ρ (i a)) (P₀.comap Φ)
    hQ S hS ⟨v, hv'⟩
  have hSv : S ⟨v, hv'⟩ = A θ := by
    show A (ΦQ ⟨v, hv'⟩) = A θ
    congr 1
    exact Subtype.ext hv
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι' (ρ j)) (i a)) hmem

end Transport

section Coeff

variable {Kc : Type*} [Group Kc]
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def coeffFun (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) : E →ₗ[ℂ] (Kc → ℂ) where
  toFun v κ := lam (π κ v)
  map_add' v w := funext fun κ => by simp only [map_add, Pi.add_apply]
  map_smul' a v := funext fun κ => by simp only [map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]

theorem coeffFun_apply (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) (v : E) (κ : Kc) :
    coeffFun π lam v κ = lam (π κ v) :=
  rfl

theorem isRightEquivariant_coeffFun (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) :
    IsRightEquivariant (MonoidHom.id Kc) π (coeffFun π lam) := by
  intro k v κ
  show lam (π κ (π k v)) = lam (π (κ * k) v)
  rw [map_mul]
  rfl

def dualCoeffFun (π : Representation ℂ Kc E) (v : E) : Module.Dual ℂ E →ₗ[ℂ] (Kc → ℂ) where
  toFun lam κ := lam (π κ⁻¹ v)
  map_add' l m := funext fun κ => by simp only [LinearMap.add_apply, Pi.add_apply]
  map_smul' a l := funext fun κ => by
    simp only [LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]

theorem dualCoeffFun_apply (π : Representation ℂ Kc E) (v : E) (lam : Module.Dual ℂ E) (κ : Kc) :
    dualCoeffFun π v lam κ = lam (π κ⁻¹ v) :=
  rfl

theorem isRightEquivariant_dualCoeffFun (π : Representation ℂ Kc E) (v : E) :
    IsRightEquivariant (MonoidHom.id Kc) π.dual (dualCoeffFun π v) := by
  intro k lam κ
  show (π.dual k lam) (π κ⁻¹ v) = lam (π (κ * k)⁻¹ v)
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, mul_inv_rev, map_mul]
  rfl

end Coeff

section LeftTypes

variable {Kw Kc G : Type*} [Group Kw] [Group Kc] [Group G]

def transRep (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E) : Representation ℂ Kc E where
  toFun κ :=
    { toFun := fun v => ⟨fun x => (v : G → ℂ) (x * ι κ), hE κ v v.2⟩
      map_add' := fun v w => by ext x; rfl
      map_smul' := fun c v => by ext x; rfl }
  map_one' := by
    ext v x
    show (v : G → ℂ) (x * ι 1) = (v : G → ℂ) x
    rw [map_one, mul_one]
  map_mul' κ κ' := by
    ext v x
    show (v : G → ℂ) (x * ι (κ * κ')) = (v : G → ℂ) (x * ι κ * ι κ')
    rw [map_mul, mul_assoc]

theorem transRep_apply (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E) (κ : Kc) (v : E) (x : G) :
    ((transRep ι E hE κ v : E) : G → ℂ) x = (v : G → ℂ) (x * ι κ) :=
  rfl

theorem coeffFun_transRep_mem_iSup {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] {incl : Kw →* Kc} (hincl : Function.Injective incl) (ι : Kc →* G)
    (ρ : ∀ j, Representation ℂ Kw (W j)) (E : Submodule ℂ (G → ℂ))
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)
    (hEcut : ∀ v ∈ E, v ∈ ⨆ j, typeSubmodule (ι.comp incl) (ρ j))
    (lam : Module.Dual ℂ E) (v : E) :
    coeffFun (transRep ι E hE) lam v ∈ ⨆ j, typeSubmodule incl (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, m, hm⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule (ι.comp incl) ρ (hEcut v v.2)
  have hQ : ∀ (k : Kw), ∀ w ∈ E.comap Φ, piRep (fun a => ρ (i a)) k w ∈ E.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι (incl k)) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hE (incl k) _ hw
  let ΦQ : E.comap Φ →ₗ[ℂ] E := LinearMap.codRestrict E (Φ.comp (E.comap Φ).subtype) fun w => w.2
  let S : E.comap Φ →ₗ[ℂ] (Kc → ℂ) := (coeffFun (transRep ι E hE) lam).comp ΦQ
  have hS : ∀ (k : Kw) (w : E.comap Φ) (κ : Kc),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ κ = S w (κ * incl k) := by
    intro k w κ
    show lam (transRep ι E hE κ (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩)) =
      lam (transRep ι E hE (κ * incl k) (ΦQ w))
    congr 1
    apply Subtype.ext
    funext x
    show Φ (piRep (fun a => ρ (i a)) k w) (x * ι κ) = Φ (w : ∀ a : t, W (i a)) (x * ι (κ * incl k))
    rw [hΦ k w, map_mul, mul_assoc]
    rfl
  have hm' : m ∈ E.comap Φ := by
    rw [Submodule.mem_comap, hm]
    exact v.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hincl (fun a => ρ (i a)) (E.comap Φ)
    hQ S hS ⟨m, hm'⟩
  have hSv : S ⟨m, hm'⟩ = coeffFun (transRep ι E hE) lam v := by
    show coeffFun (transRep ι E hE) lam (ΦQ ⟨m, hm'⟩) = coeffFun (transRep ι E hE) lam v
    congr 1
    exact Subtype.ext hm
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule incl (ρ j)) (i a)) hmem

end LeftTypes

section DualTypes

variable {Kw Kc G : Type*} [Group Kw] [Group Kc] [Group G]

theorem exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule {H : Type*} [Group H] {J : Type*}
    {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) (P : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ P]
    (hP : P ≤ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ P ≤ LinearMap.range Φ := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional P).mpr inferInstance
  have hgenset : ∀ f ∈ s, f ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    intro f hf
    rw [Submodule.span_iUnion]
    exact hP (hs ▸ Submodule.subset_span hf)
  choose tf htf hftf using fun f : s => Submodule.mem_span_finite_of_mem_span (hgenset f f.2)
  let t : Finset (G → ℂ) := Finset.univ.biUnion tf
  have ht : ↑t ⊆ ⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T} := by
    intro g hg
    obtain ⟨f, -, hgf⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hg)
    exact htf f hgf
  have hgen : ∀ g : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (g : G → ℂ) ∈ LinearMap.range T := fun g => by
    have hg := ht g.2
    rw [Set.mem_iUnion] at hg
    obtain ⟨j, T, hT, hgT⟩ := hg
    exact ⟨j, T, hT, hgT⟩
  choose i T hT hgT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · have hspan : Submodule.span ℂ (↑t : Set (G → ℂ)) ≤ LinearMap.range Φ := by
      refine Submodule.span_le.mpr ?_
      intro g hg
      obtain ⟨v, hv⟩ := hgT ⟨g, hg⟩
      refine ⟨Pi.single (⟨g, hg⟩ : t) v, ?_⟩
      rw [hΦ, Finset.sum_eq_single (⟨g, hg⟩ : t)]
      · rw [Pi.single_eq_same]
        exact hv
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, map_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [← hs]
    refine Submodule.span_le.mpr fun f hf => hspan ?_
    have hsub : ↑(tf ⟨f, hf⟩) ⊆ (↑t : Set (G → ℂ)) := fun g hg =>
      Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨⟨f, hf⟩, Finset.mem_univ _, hg⟩)
    exact Submodule.span_mono hsub (hftf ⟨f, hf⟩)

theorem dualCoeffFun_transRep_mem_iSup {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] {incl : Kw →* Kc} (hincl : Function.Injective incl) (ι : Kc →* G)
    (ρ : ∀ j, Representation ℂ Kw (W j)) (E : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ E]
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)
    (hEcut : ∀ v ∈ E, v ∈ ⨆ j, typeSubmodule (ι.comp incl) (ρ j))
    (v : E) (lam : Module.Dual ℂ E) :
    dualCoeffFun (transRep ι E hE) v lam ∈ ⨆ j, typeSubmodule incl (ρ j).dual := by
  classical
  obtain ⟨t, i, Φ, hΦ, hEΦ⟩ :=
    exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule (ι.comp incl) ρ E hEcut

  have hQ : ∀ (k : Kw), ∀ w ∈ E.comap Φ, piRep (fun a => ρ (i a)) k w ∈ E.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι (incl k)) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hE (incl k) _ hw
  let π : Representation ℂ Kc E := transRep ι E hE
  let Q : Submodule ℂ (∀ a : t, W (i a)) := E.comap Φ
  let q : Q →ₗ[ℂ] E := LinearMap.codRestrict E (Φ.comp Q.subtype) fun w => w.2
  have hq : ∀ (k : Kw) (w : Q), q ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ = π (incl k) (q w) := by
    intro k w
    apply Subtype.ext
    funext x
    show Φ (piRep (fun a => ρ (i a)) k w) x = Φ (w : ∀ a : t, W (i a)) (x * ι (incl k))
    exact hΦ k w x
  have hqsurj : Function.Surjective q := by
    intro e
    obtain ⟨m, hm⟩ := hEΦ e.2
    exact ⟨⟨m, by rw [Submodule.mem_comap, hm]; exact e.2⟩, Subtype.ext hm⟩
  have hqinj : Function.Injective q.dualMap := LinearMap.dualMap_injective_of_surjective hqsurj

  let glue : (∀ a : t, Module.Dual ℂ (W (i a))) ≃ₗ[ℂ] Module.Dual ℂ (∀ a : t, W (i a)) :=
    LinearMap.lsum ℂ (fun a : t => W (i a)) ℂ
  have hglue : ∀ (ν : ∀ a : t, Module.Dual ℂ (W (i a))) (m : ∀ a : t, W (i a)),
      glue ν m = ∑ a : t, ν a (m a) := fun ν m => by
    simp only [glue, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  let r : Module.Dual ℂ (∀ a : t, W (i a)) →ₗ[ℂ] Module.Dual ℂ Q := Q.subtype.dualMap
  have hrsurj : Function.Surjective r := LinearMap.dualMap_surjective_of_injective Q.injective_subtype

  let S' : Submodule ℂ (∀ a : t, Module.Dual ℂ (W (i a))) :=
    (LinearMap.range q.dualMap).comap (r.comp glue.toLinearMap)
  have hS'mem : ∀ ν : ∀ a : t, Module.Dual ℂ (W (i a)),
      ν ∈ S' ↔ ∃ l : Module.Dual ℂ E, ∀ w : Q, glue ν (w : ∀ a : t, W (i a)) = l (q w) := by
    intro ν
    simp only [S', Submodule.mem_comap, LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l, fun w => ?_⟩
      have := LinearMap.congr_fun hl w
      rw [LinearMap.dualMap_apply] at this
      rw [this]
      rfl
    · rintro ⟨l, hl⟩
      refine ⟨l, LinearMap.ext fun w => ?_⟩
      rw [LinearMap.dualMap_apply]
      exact (hl w).symm

  have hpi : ∀ (k : Kw) (ν : ∀ a : t, Module.Dual ℂ (W (i a))) (m : ∀ a : t, W (i a)),
      glue (piRep (fun a => (ρ (i a)).dual) k ν) m = glue ν (piRep (fun a => ρ (i a)) k⁻¹ m) := by
    intro k ν m
    rw [hglue, hglue]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [piRep_apply, piRep_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply]
  have hS' : ∀ (k : Kw), ∀ ν ∈ S', piRep (fun a => (ρ (i a)).dual) k ν ∈ S' := by
    intro k ν hν
    obtain ⟨l, hl⟩ := (hS'mem ν).mp hν
    refine (hS'mem _).mpr ⟨π.dual (incl k) l, fun w => ?_⟩
    have hw : piRep (fun a => ρ (i a)) k⁻¹ (w : ∀ a : t, W (i a)) ∈ Q := hQ k⁻¹ _ w.2
    rw [hpi, hl ⟨_, hw⟩, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      ← map_inv, hq k⁻¹ w]

  have hσex : ∀ ν : S', ∃! l : Module.Dual ℂ E, ∀ w : Q, glue (ν : ∀ a, _) (w : ∀ a : t, W (i a)) = l (q w) := by
    intro ν
    obtain ⟨l, hl⟩ := (hS'mem ν).mp ν.2
    refine ⟨l, hl, fun l' hl' => ?_⟩
    apply hqinj
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← hl w, ← hl' w]
  choose σf hσf hσu using hσex
  let σ : S' →ₗ[ℂ] Module.Dual ℂ E :=
    { toFun := σf
      map_add' := fun ν₁ ν₂ => by
        symm
        apply hσu
        intro w
        rw [LinearMap.add_apply, ← hσf ν₁ w, ← hσf ν₂ w, Submodule.coe_add, map_add, LinearMap.add_apply]
      map_smul' := fun c ν => by
        symm
        apply hσu
        intro w
        rw [RingHom.id_apply, LinearMap.smul_apply, ← hσf ν w, Submodule.coe_smul, map_smul,
          LinearMap.smul_apply] }
  have hσ : ∀ (ν : S') (w : Q), glue (ν : ∀ a, _) (w : ∀ a : t, W (i a)) = σ ν (q w) := hσf
  have hσeq : ∀ (k : Kw) (ν : S'), σ ⟨piRep (fun a => (ρ (i a)).dual) k ν, hS' k ν ν.2⟩ = π.dual (incl k) (σ ν) := by
    intro k ν
    refine (hσu ⟨_, hS' k ν ν.2⟩ _ fun w => ?_).symm
    have hw : piRep (fun a => ρ (i a)) k⁻¹ (w : ∀ a : t, W (i a)) ∈ Q := hQ k⁻¹ _ w.2
    show glue (piRep (fun a => (ρ (i a)).dual) k (ν : ∀ a, _)) (w : ∀ a : t, W (i a)) = _
    rw [hpi, hσ ν ⟨_, hw⟩, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      ← map_inv, hq k⁻¹ w]

  let S : S' →ₗ[ℂ] (Kc → ℂ) := (dualCoeffFun π v).comp σ
  have hS : ∀ (k : Kw) (ν : S') (κ : Kc),
      S ⟨piRep (fun a => (ρ (i a)).dual) k ν, hS' k ν ν.2⟩ κ = S ν (κ * incl k) := by
    intro k ν κ
    show dualCoeffFun π v (σ ⟨piRep (fun a => (ρ (i a)).dual) k ν, hS' k ν ν.2⟩) κ =
      dualCoeffFun π v (σ ν) (κ * incl k)
    rw [hσeq]
    exact isRightEquivariant_dualCoeffFun π v (incl k) (σ ν) κ

  obtain ⟨μ, hμ⟩ := hrsurj (q.dualMap lam)
  have hν₀ : glue.symm μ ∈ S' := by
    refine (hS'mem _).mpr ⟨lam, fun w => ?_⟩
    rw [LinearEquiv.apply_symm_apply]
    have := LinearMap.congr_fun hμ w
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply] at this
    exact this
  have hlam : σ ⟨glue.symm μ, hν₀⟩ = lam := by
    symm
    apply hσu
    intro w
    show glue (glue.symm μ) (w : ∀ a : t, W (i a)) = lam (q w)
    rw [LinearEquiv.apply_symm_apply]
    have := LinearMap.congr_fun hμ w
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply] at this
    exact this
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hincl (fun a => (ρ (i a)).dual) S' hS' S hS
    ⟨glue.symm μ, hν₀⟩
  have hSv : S ⟨glue.symm μ, hν₀⟩ = dualCoeffFun π v lam := by
    show dualCoeffFun π v (σ ⟨glue.symm μ, hν₀⟩) = dualCoeffFun π v lam
    rw [hlam]
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule incl (ρ j).dual) (i a)) hmem

end DualTypes

end KcCentralRepro

end

end Carry3

theorem solution
    {G Kc H : Type*} [Group G] [Group Kc] [Group H] (ι : Kc →* G) (j : H →* Kc)
    (hj : Function.Injective j) (E : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ E]
    (hE : ∀ κ : Kc, ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)
    {J : Type*} {W : J → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i))
    (hEρ : ∀ v ∈ E, v ∈ ⨆ i, AutomorphicForm.typeSubmodule (ι.comp j) (ρ i))
    (lam : Module.Dual ℂ E) (v : E) :
    (fun κ : Kc => lam ⟨fun x => (v : G → ℂ) (x * ι κ), hE κ v v.2⟩) ∈
        ⨆ i, AutomorphicForm.typeSubmodule j (ρ i) ∧
      (fun κ : Kc => lam ⟨fun x => (v : G → ℂ) (x * ι κ⁻¹), hE κ⁻¹ v v.2⟩) ∈
        ⨆ i, AutomorphicForm.typeSubmodule j (ρ i).dual := by
  refine ⟨?_, ?_⟩
  · exact KcCentralRepro.coeffFun_transRep_mem_iSup hj ι ρ E hE hEρ lam v
  · exact KcCentralRepro.dualCoeffFun_transRep_mem_iSup hj ι ρ E hE hEρ v lam

end S_AutomorphicForm_matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp
end P2MW
export P2MW.S_AutomorphicForm_matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp (solution)
