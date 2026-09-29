-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/75c2ad09-22ea-57c3-bea7-32edfea6cbda

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

section KSpanAlg

noncomputable section

namespace R5bE

open AutomorphicForm

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

private noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

private theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

private theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

private theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  rw [hmk, map_mul, ← mul_assoc, out_mul_cosetCoord]

private theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
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

private def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

private theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

private theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
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

private theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
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

private theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

private theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
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

private theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
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

private def coeffFun (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) : E →ₗ[ℂ] (Kc → ℂ) where
  toFun v κ := lam (π κ v)
  map_add' v w := funext fun κ => by simp only [map_add, Pi.add_apply]
  map_smul' a v := funext fun κ => by simp only [map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]

private theorem coeffFun_apply (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) (v : E) (κ : Kc) :
    coeffFun π lam v κ = lam (π κ v) :=
  rfl

private theorem isRightEquivariant_coeffFun (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) :
    IsRightEquivariant (MonoidHom.id Kc) π (coeffFun π lam) := by
  intro k v κ
  show lam (π κ (π k v)) = lam (π (κ * k) v)
  rw [map_mul]
  rfl

private def dualCoeffFun (π : Representation ℂ Kc E) (v : E) : Module.Dual ℂ E →ₗ[ℂ] (Kc → ℂ) where
  toFun lam κ := lam (π κ⁻¹ v)
  map_add' l m := funext fun κ => by simp only [LinearMap.add_apply, Pi.add_apply]
  map_smul' a l := funext fun κ => by
    simp only [LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]

private theorem dualCoeffFun_apply (π : Representation ℂ Kc E) (v : E) (lam : Module.Dual ℂ E) (κ : Kc) :
    dualCoeffFun π v lam κ = lam (π κ⁻¹ v) :=
  rfl

private theorem isRightEquivariant_dualCoeffFun (π : Representation ℂ Kc E) (v : E) :
    IsRightEquivariant (MonoidHom.id Kc) π.dual (dualCoeffFun π v) := by
  intro k lam κ
  show (π.dual k lam) (π κ⁻¹ v) = lam (π (κ * k)⁻¹ v)
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, mul_inv_rev, map_mul]
  rfl

end Coeff

section LeftTypes

variable {Kw Kc G : Type*} [Group Kw] [Group Kc] [Group G]

private def transRep (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
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

private theorem transRep_apply (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E) (κ : Kc) (v : E) (x : G) :
    ((transRep ι E hE κ v : E) : G → ℂ) x = (v : G → ℂ) (x * ι κ) :=
  rfl

private theorem coeffFun_transRep_mem_iSup {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
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

private theorem exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule {H : Type*} [Group H] {J : Type*}
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

private theorem dualCoeffFun_transRep_mem_iSup {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
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

section SpanTranslates

variable {H G : Type*} [Group H] [Group G]

private def rt (x₀ : G) (v : G → ℂ) : G → ℂ := fun x => v (x * x₀)

private theorem rt_apply (x₀ : G) (v : G → ℂ) (x : G) : rt x₀ v x = v (x * x₀) := rfl

private def rtLinear (x₀ : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := rt x₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rtLinear_apply (x₀ : G) (v : G → ℂ) : rtLinear x₀ v = rt x₀ v := rfl

private theorem rt_mul (x₀ x₁ : G) (v : G → ℂ) : rt (x₀ * x₁) v = rt x₀ (rt x₁ v) := by
  funext x
  simp only [rt_apply, mul_assoc]

private theorem rt_mem_typeSubmodule_of_commute {W : Type*} [AddCommGroup W] [Module ℂ W] {ι : H →* G}
    {ρ : Representation ℂ H W} {x₀ : G} (hx₀ : ∀ k : H, x₀ * ι k = ι k * x₀) {v : G → ℂ}
    (hv : v ∈ typeSubmodule ι ρ) : rt x₀ v ∈ typeSubmodule ι ρ := by
  have hmap : ∀ f ∈ typeSubmodule ι ρ, rtLinear x₀ f ∈ typeSubmodule ι ρ := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro g ⟨T, hT, w, rfl⟩
      have hT' : IsRightEquivariant ι ρ ((rtLinear x₀).comp T) := by
        intro k u x
        show T (ρ k u) (x * x₀) = T u (x * ι k * x₀)
        rw [hT k u (x * x₀), mul_assoc, hx₀ k, ← mul_assoc]
      exact mem_typeSubmodule_of_isRightEquivariant hT' w
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro f g _ _ hf hg
      rw [map_add]
      exact Submodule.add_mem _ hf hg
    · intro c f _ hf
      rw [map_smul]
      exact Submodule.smul_mem _ c hf
  exact hmap v hv

private theorem rt_mem_typeSubmodule_self {W : Type*} [AddCommGroup W] [Module ℂ W] {ι : H →* G}
    {ρ : Representation ℂ H W} (k : H) {v : G → ℂ} (hv : v ∈ typeSubmodule ι ρ) :
    rt (ι k) v ∈ typeSubmodule ι ρ := by
  have hmap : ∀ f ∈ typeSubmodule ι ρ, rtLinear (ι k) f ∈ typeSubmodule ι ρ := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro g ⟨T, hT, w, rfl⟩
      have h1 : rtLinear (ι k) (T w) = T (ρ k w) := funext fun x => (hT k w x).symm
      rw [h1]
      exact mem_typeSubmodule_of_isRightEquivariant hT _
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro f g _ _ hf hg
      rw [map_add]
      exact Submodule.add_mem _ hf hg
    · intro c f _ hf
      rw [map_smul]
      exact Submodule.smul_mem _ c hf
  exact hmap v hv

private def spanTranslates (ι : H →* G) (V : Submodule ℂ (G → ℂ)) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {g | ∃ k : H, ∃ v ∈ V, g = rt (ι k) v}

private theorem le_spanTranslates (ι : H →* G) (V : Submodule ℂ (G → ℂ)) : V ≤ spanTranslates ι V := by
  intro v hv
  refine Submodule.subset_span ⟨1, v, hv, ?_⟩
  funext x
  simp only [rt_apply, map_one, mul_one]

private theorem rt_mem_spanTranslates (ι : H →* G) (V : Submodule ℂ (G → ℂ)) (k : H) {v : G → ℂ} (hv : v ∈ V) :
    rt (ι k) v ∈ spanTranslates ι V :=
  Submodule.subset_span ⟨k, v, hv, rfl⟩

private theorem rt_mem_spanTranslates_of_mem (ι : H →* G) (V : Submodule ℂ (G → ℂ)) (k : H) {g : G → ℂ}
    (hg : g ∈ spanTranslates ι V) : rt (ι k) g ∈ spanTranslates ι V := by
  have hmap : ∀ f ∈ spanTranslates ι V, rtLinear (ι k) f ∈ spanTranslates ι V := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro g ⟨k', v, hv, rfl⟩
      show rt (ι k) (rt (ι k') v) ∈ spanTranslates ι V
      rw [← rt_mul, ← map_mul]
      exact rt_mem_spanTranslates ι V _ hv
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro f g _ _ hf hg
      rw [map_add]
      exact Submodule.add_mem _ hf hg
    · intro c f _ hf
      rw [map_smul]
      exact Submodule.smul_mem _ c hf
  exact hmap g hg

private theorem finiteDimensional_spanTranslates {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] [∀ j, Module.Finite ℂ (W j)] (ι : H →* G) (ρ : ∀ j, Representation ℂ H (W j))
    (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] (hV : V ≤ ⨆ j, typeSubmodule ι (ρ j)) :
    FiniteDimensional ℂ (spanTranslates ι V) := by
  classical
  obtain ⟨t, i, Φ, hΦ, hVΦ⟩ := exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule ι ρ V hV
  have hle : spanTranslates ι V ≤ LinearMap.range Φ := by
    refine Submodule.span_le.mpr ?_
    rintro g ⟨k, v, hv, rfl⟩
    obtain ⟨m, hm⟩ := hVΦ hv
    refine ⟨piRep (fun a => ρ (i a)) k m, ?_⟩
    funext x
    rw [hΦ k m x, rt_apply, hm]
  haveI : Module.Finite ℂ (∀ a : t, W (i a)) := Module.Finite.pi
  exact Submodule.finiteDimensional_of_le hle

end SpanTranslates

section MultiPlace

variable {G : Type*} [Group G]
variable {Pl : Type*} [Fintype Pl] [DecidableEq Pl] {K : Pl → Type*} [∀ w, Group (K w)]

private theorem exists_finiteDimensional_stable {J : Pl → Type*} {W : ∀ w, J w → Type*}
    [∀ w j, AddCommGroup (W w j)] [∀ w j, Module ℂ (W w j)] [∀ w j, Module.Finite ℂ (W w j)]
    (ι : ∀ w, K w →* G) (hcomm : ∀ (w w' : Pl), w ≠ w' → ∀ (k : K w) (k' : K w'), ι w k * ι w' k' = ι w' k' * ι w k)
    (ρ : ∀ w j, Representation ℂ (K w) (W w j)) (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ w, V ≤ ⨆ j, typeSubmodule (ι w) (ρ w j)) :
    ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧ V ≤ E ∧
      (∀ w, E ≤ ⨆ j, typeSubmodule (ι w) (ρ w j)) ∧ ∀ (w : Pl) (k : K w), ∀ v ∈ E, rt (ι w k) v ∈ E := by
  classical

  have hstab : ∀ (w w' : Pl) (k : K w), ∀ v ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j),
      rt (ι w k) v ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j) := by
    intro w w' k v hv
    have hmap : ∀ f ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j), rtLinear (ι w k) f ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j) := by
      intro f hf
      refine Submodule.iSup_induction _ (motive := fun f => rtLinear (ι w k) f ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j))
        hf ?_ ?_ ?_
      · intro j f hfj
        refine Submodule.mem_iSup_of_mem j ?_
        by_cases hww : w = w'
        · subst hww
          exact rt_mem_typeSubmodule_self k hfj
        · exact rt_mem_typeSubmodule_of_commute (fun k' => hcomm w w' hww k k') hfj
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro f g hf hg
        rw [map_add]
        exact Submodule.add_mem _ hf hg
    exact hmap v hv

  suffices h : ∀ s : Finset Pl, ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧ V ≤ E ∧
      (∀ w, E ≤ ⨆ j, typeSubmodule (ι w) (ρ w j)) ∧ ∀ w ∈ s, ∀ (k : K w), ∀ v ∈ E, rt (ι w k) v ∈ E by
    obtain ⟨E, h1, h2, h3, h4⟩ := h Finset.univ
    exact ⟨E, h1, h2, h3, fun w k v hv => h4 w (Finset.mem_univ w) k v hv⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨V, inferInstance, le_rfl, hV, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | @insert w₀ s hw₀ ih =>
    obtain ⟨E, hEfd, hVE, hEcut, hEst⟩ := ih
    haveI := hEfd
    haveI : FiniteDimensional ℂ (spanTranslates (ι w₀) E) :=
      finiteDimensional_spanTranslates (ι w₀) (ρ w₀) E (hEcut w₀)
    refine ⟨spanTranslates (ι w₀) E, inferInstance, hVE.trans (le_spanTranslates _ _), ?_, ?_⟩
    · intro w
      refine Submodule.span_le.mpr ?_
      rintro g ⟨k, v, hv, rfl⟩
      exact hstab w₀ w k v (hEcut w hv)
    · intro w hw k g hg
      rcases Finset.mem_insert.mp hw with rfl | hws
      · exact rt_mem_spanTranslates_of_mem (ι w) E k hg
      · have hmap : ∀ f ∈ spanTranslates (ι w₀) E, rtLinear (ι w k) f ∈ spanTranslates (ι w₀) E := by
          intro f hf
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
          · rintro g ⟨k₀, v, hv, rfl⟩
            have hne : w ≠ w₀ := fun h => hw₀ (h ▸ hws)
            show rt (ι w k) (rt (ι w₀ k₀) v) ∈ spanTranslates (ι w₀) E
            rw [← rt_mul, hcomm w w₀ hne k k₀, rt_mul]
            exact rt_mem_spanTranslates (ι w₀) E k₀ (hEst w hws k v hv)
          · rw [map_zero]
            exact Submodule.zero_mem _
          · intro f g _ _ hf hg
            rw [map_add]
            exact Submodule.add_mem _ hf hg
          · intro c f _ hf
            rw [map_smul]
            exact Submodule.smul_mem _ c hf
        exact hmap g hg

end MultiPlace

end R5bE

end

end KSpanAlg

section KSpanMain

open AutomorphicForm AutomorphicForm.CuspidalConstituent

namespace R5bE

variable (F : Type) [Field F] [NumberField F]

private theorem kspan_main (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
      Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        rightTranslate F (rowIsometryInclAt₀ F w k) φ)
    FiniteDimensional ℂ ↥S ∧
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) ∧
      S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) := by
  intro S

  let ι : rowIsometrySubgroup₀ w.Completion →* AdelicGL2 (𝓞 F) F := rowIsometryInclAt₀ F w
  let ρ : ∀ i : Fin m, Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin (ρs i).n → ℂ) := fun i => (ρs i).ρ
  have hcut : (⨆ i, archTypeSubmoduleAt F w (ρs i)) = ⨆ i, typeSubmodule ι (ρ i) := rfl

  let V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ {φ}
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton φ)
  have hV : V ≤ ⨆ i, typeSubmodule ι (ρ i) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hφ

  have hS : S ≤ spanTranslates ι V := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact rt_mem_spanTranslates ι V k (Submodule.subset_span rfl)
  refine ⟨?_, ?_, ?_⟩
  · haveI := finiteDimensional_spanTranslates ι ρ V hV
    exact Submodule.finiteDimensional_of_le hS
  · intro k g hg
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨k', rfl⟩
      rw [rightTranslate_rightTranslate, ← map_mul]
      exact Submodule.subset_span ⟨k * k', rfl⟩
    · rw [rightTranslate_zero]
      exact Submodule.zero_mem _
    · intro f g _ _ hf hg
      rw [rightTranslate_add]
      exact Submodule.add_mem _ hf hg
    · intro c f _ hf
      rw [rightTranslate_smul]
      exact Submodule.smul_mem _ c hf
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [hcut] at hφ ⊢
    have key : ∀ i : Fin m, (typeSubmodule ι (ρ i)).map (rightRegular F (ι k)) ≤ typeSubmodule ι (ρ i) := by
      intro i f hf
      obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
      exact rt_mem_typeSubmodule_self k hf₀
    have hmap : (⨆ i, typeSubmodule ι (ρ i)).map (rightRegular F (ι k)) ≤ ⨆ i, typeSubmodule ι (ρ i) := by
      rw [Submodule.map_iSup]
      exact iSup_mono key
    exact hmap (Submodule.mem_map_of_mem hφ)

end R5bE

end KSpanMain

section SolutionBlock

theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
      Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        rightTranslate F (rowIsometryInclAt₀ F w k) φ)
    FiniteDimensional ℂ ↥S ∧
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) ∧
      S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) :=
  R5bE.kspan_main F w m ρs φ hφ

end SolutionBlock

end S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt (solution)
