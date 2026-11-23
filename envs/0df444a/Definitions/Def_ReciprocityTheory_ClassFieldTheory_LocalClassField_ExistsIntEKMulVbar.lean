-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:23.995288+00:00
-- url     : https://prove2.me/theorems/ad83842b-ebdf-461c-b59d-cb1f230d6e4b
-- title:
--   Exists Int EKMul Vbar
-- statement:
--   Definitions and structural lemmas for Exists Int EKMul Vbar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsIntEKMulVbar.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_invariants_isInvRep
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe


set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
def fK : ℕ := Nat.log p (qK p K)
def vbar : KbarMult p →+ ℝ where
  toFun x := - Real.logb p ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖
  map_zero' := by
    show - Real.logb p ‖((1 : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 0
    simp
  map_add' x y := by
    show - Real.logb p ‖((Additive.toMul x * Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = _
    rw [Units.val_mul, norm_mul, Real.logb_mul (norm_ne_zero_iff.2 (Units.ne_zero _))
      (norm_ne_zero_iff.2 (Units.ne_zero _))]
    ring
theorem vbar_apply (x : KbarMult p) :
    vbar p x = - Real.logb p ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ := rfl
def multOf : AddSubgroup (KbarMult p) where
  carrier := {x | ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) ∈ K}
  zero_mem' := K.one_mem
  add_mem' := fun {x y} hx hy => K.mul_mem hx hy
  neg_mem' := fun {x} hx => by
    show (((Additive.toMul x : (PadicAlgCl p)ˣ)⁻¹ : (PadicAlgCl p)ˣ) : PadicAlgCl p) ∈ K
    rw [Units.val_inv_eq_inv_val]
    exact K.inv_mem hx
def ofK : Additive Kˣ →+ KbarMult p :=
  MonoidHom.toAdditive (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p))
theorem ofK_mem (x : Additive Kˣ) : ofK p K x ∈ multOf p K := (Additive.toMul x : Kˣ).1.2
def valueGroup : AddSubgroup ℝ := (multOf p K).map (vbar p)
def eK : ℕ := (AddSubgroup.zmultiples (1 : ℝ)).relIndex (valueGroup p K)
theorem exists_int_eK_mul_vbar (x : KbarMult p) (hx : x ∈ multOf p K) :
    ∃ n : ℤ, (n : ℝ) = eK p K * vbar p x := by
  have h : eK p K • vbar p x ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    AddSubgroup.nsmul_relIndex_mem _ (AddSubgroup.mem_map_of_mem _ hx)
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h
  refine ⟨k, ?_⟩
  have hk' : (k : ℝ) = (eK p K) • vbar p x := by simpa using hk
  rw [hk', nsmul_eq_mul]
def vOnFun (x : multOf p K) : ℤ := (exists_int_eK_mul_vbar p K x.1 x.2).choose
theorem vOnFun_spec (x : multOf p K) : (vOnFun p K x : ℝ) = eK p K * vbar p x.1 :=
  (exists_int_eK_mul_vbar p K x.1 x.2).choose_spec
def vOn : multOf p K →+ ℤ where
  toFun := vOnFun p K
  map_zero' := by
    apply Int.cast_injective (α := ℝ)
    rw [vOnFun_spec]; simp
  map_add' x y := by
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_add, vOnFun_spec, vOnFun_spec, vOnFun_spec, AddSubgroup.coe_add, map_add, mul_add]
def vK (x : Kˣ) : ℤ := vOn p K ⟨ofK p K (Additive.ofMul x), ofK_mem p K _⟩
def Ubar : Submodule ℤ (KbarMult p) := AddSubgroup.toIntSubmodule (vbar p).ker
def UK : Subgroup Kˣ where
  carrier := {x | ‖((x : K) : PadicAlgCl p)‖ = 1}
  one_mem' := by
    show ‖(((1 : Kˣ) : K) : PadicAlgCl p)‖ = 1
    simp
  mul_mem' := fun {x y} hx hy => by
    have hx' : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx
    have hy' : ‖((y : K) : PadicAlgCl p)‖ = 1 := hy
    show ‖(((x * y : Kˣ) : K) : PadicAlgCl p)‖ = 1
    rw [Units.val_mul, MulMemClass.coe_mul, norm_mul, hx', hy', one_mul]
  inv_mem' := fun {x} hx => by
    have hx' : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx
    show ‖(((x⁻¹ : Kˣ) : K) : PadicAlgCl p)‖ = 1
    rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv, norm_inv, hx', inv_one]
def subG : Subgroup (GK p K) where
  carrier := {σ | ∀ x ∈ L, σ x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {σ τ} hσ hτ x hx => by
    show σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  inv_mem' := fun {σ} hσ x hx => by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]; exact (hσ x hx).symm
def degLK : ℕ := (subG p K L).index
abbrev GalLK : Type := GK p K ⧸ subG p K L
variable {p K L} in

def resGK (h : K ≤ L) : GK p L →* GK p K where
  toFun σ := { σ.toRingEquiv with commutes' := fun x => σ.commutes ⟨x.1, h x.2⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl
variable {p K L} in
theorem resGK_continuous (h : K ≤ L) : Continuous (resGK h) := by
  have hint : Algebra.IsIntegral L (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  refine Filter.tendsto_def.2 fun s hs => ?_
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  let b := Module.finBasis K E
  have hopen : IsOpen (⋂ i, {σ : GK p L | σ (b i : PadicAlgCl p) = b i}) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := L) (b i : PadicAlgCl p)
  refine Filter.mem_of_superset (hopen.mem_nhds (Set.mem_iInter.2 fun i => rfl)) fun σ hσ => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    exact this.symm
  rw [hx']
  show resGK h σ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes]
  exact congrArg _ (Set.mem_iInter.1 hσ i)
variable {p K L} in

theorem subG_normal_of_stable (h : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L) : (subG p K L).Normal := by
  refine ⟨fun n hn g x hx => ?_⟩
  show g (n (g⁻¹ x)) = x
  rw [hn _ (h g⁻¹ x hx)]
  show (g * g⁻¹) x = x
  rw [mul_inv_cancel]; rfl
theorem norm_map_GK (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm
theorem vbar_kbarRep (σ : GK p K) (x : KbarMult p) : vbar p (kbarRep p K σ x) = vbar p x := by
  rw [vbar_apply, vbar_apply]
  show - Real.logb p ‖σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = _
  rw [norm_map_GK]
def MaximalUnramifiedExtension : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n : ℕ, Kn p K (n + 1)
theorem Kn_stable (n : ℕ) (σ : GK p K) (x : PadicAlgCl p) (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by
  have h : Kn p K n ≤ (Kn p K n).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) := by
    refine sup_le (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 fun ζ hζ => ?_)
    · show σ y ∈ Kn p K n
      rw [show σ y = y from σ.commutes ⟨y, hy⟩]
      exact (le_sup_left : K ≤ Kn p K n) hy
    · show σ ζ ∈ Kn p K n
      refine (le_sup_right : _ ≤ Kn p K n) (IntermediateField.subset_adjoin _ _ ?_)
      show (σ ζ) ^ (qK p K ^ n - 1) = 1
      rw [← map_pow, show ζ ^ (qK p K ^ n - 1) = 1 from hζ, map_one]
  exact h hx
theorem Kur_stable (σ : GK p K) (x : PadicAlgCl p) (hx : x ∈ MaximalUnramifiedExtension p K) : σ x ∈ MaximalUnramifiedExtension p K := by
  have h : MaximalUnramifiedExtension p K ≤ (MaximalUnramifiedExtension p K).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) :=
    iSup_le fun n y hy => (le_iSup (fun n : ℕ => Kn p K (n + 1)) n) (Kn_stable p K (n + 1) σ y hy)
  exact h hx
scoped instance subG_Kn_normal (n : ℕ) : (subG p K (Kn p K n)).Normal := subG_normal_of_stable (Kn_stable p K n)
scoped instance subG_Kur_normal : (subG p K (MaximalUnramifiedExtension p K)).Normal := subG_normal_of_stable (Kur_stable p K)
def IsFrob (σ : GK p K) : Prop := ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x ^ qK p K‖ < 1
def frobK : GK p K := Classical.epsilon (IsFrob p K)
def frobLK : GalLK p K L := QuotientGroup.mk (frobK p K)
def ubarRep : Representation ℤ (GK p K) (Ubar p) where
  toFun σ := (kbarRep p K σ).restrict (p := Ubar p) (q := Ubar p)
    (fun x hx => (vbar_kbarRep p K σ x).trans hx)
  map_one' := LinearMap.ext fun x => Subtype.ext (by
    show kbarRep p K 1 x.1 = x.1
    rw [map_one]; rfl)
  map_mul' σ τ := LinearMap.ext fun x => Subtype.ext (by
    show kbarRep p K (σ * τ) x.1 = kbarRep p K σ (kbarRep p K τ x.1)
    rw [map_mul]; rfl)
scoped instance : TopologicalSpace (Ubar p) := instTopologicalSpaceSubtype
scoped instance : DiscreteTopology (Ubar p) := inferInstanceAs (DiscreteTopology ((Ubar p : Set (KbarMult p))))
scoped instance : IsTopologicalAddGroup (Ubar p) := inferInstance
def ubarT : TRep ℤ (GK p K) where
  V := Ubar p
  rho := ubarRep p K
  cont := by
    exact Continuous.subtype_mk ((kbarT p K).cont.comp (f := fun x : GK p K × Ubar p => (x.1, x.2.1))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
scoped instance : DiscreteTopology (ubarT p K).V := inferInstanceAs (DiscreteTopology (Ubar p))
def ubarIncl : Pair (ubarT p K) (kbarT p K) :=
  Pair.ofMap (M := ubarT p K) (M' := kbarT p K) (Ubar p).subtype continuous_subtype_val (fun _ _ => rfl)
def mkLin {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] {A : TRep ℤ G}
    {B : TRep ℤ G'} (f : A.V →+ B.V) : A.V →ₗ[ℤ] B.V where
  toFun := f
  map_add' := f.map_add
  map_smul' n x := by simp
abbrev layer [(subG p K L).Normal] : TRep ℤ (GalLK p K L) := InflationRestrictionInvariants.invQ (kbarT p K) (subG p K L)
abbrev layerInf [(subG p K L).Normal] : Pair (layer p K L) (kbarT p K) := InflationRestrictionInvariants.invP (kbarT p K) (subG p K L)
abbrev layerU [(subG p K L).Normal] : TRep ℤ (GalLK p K L) := InflationRestrictionInvariants.invQ (ubarT p K) (subG p K L)
scoped instance [(subG p K L).Normal] : DiscreteTopology (layer p K L).V :=
  (InflationRestrictionInvariants.invariants_isInvRep (kbarT p K) (subG p K L)).2.1.discreteTopology
scoped instance [(subG p K L).Normal] : DiscreteTopology (layerU p K L).V :=
  (InflationRestrictionInvariants.invariants_isInvRep (ubarT p K) (subG p K L)).2.1.discreteTopology
def layerUIncl [(subG p K L).Normal] : Pair (layerU p K L) (layer p K L) :=
  Pair.ofMap (M := layerU p K L) (M' := layer p K L)
    (mkLin (A := layerU p K L) (B := layer p K L)
      { toFun := fun x => ⟨(ubarIncl p K).u x.1, fun g => congrArg (ubarIncl p K).u (x.2 g)⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl })
    continuous_of_discreteTopology
    (fun g x => by
      induction g using QuotientGroup.induction_on with
      | H σ => rfl)
variable {p K} in

def layerInfl {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] : Pair (layer p K L) (layer p K L') where
  φ := QuotientGroup.map (subG p K L') (subG p K L) (MonoidHom.id _) (fun _ hσ x hx => hσ x (h hx))
  u := mkLin (A := layer p K L) (B := layer p K L')
    { toFun := fun x => ⟨x.1, fun g => x.2 ⟨g.1, fun y hy => g.2 y (h hy)⟩⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  φ_cont := (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2 continuous_quot_mk
  u_cont := continuous_of_discreteTopology
  equiv g m := by
    induction g using QuotientGroup.induction_on with
    | H σ => rfl
open Classical in

def vLayerMap [(subG p K L).Normal] : (layer p K L).V →+ ℤ :=
  if h : ∃ f : (layer p K L).V →+ ℤ, ∀ x, (f x : ℝ) = eK p L * vbar p x.1 then h.choose else 0
theorem vLayerMap_rho [(subG p K L).Normal] (g : GalLK p K L) (x : (layer p K L).V) :
    vLayerMap p K L ((layer p K L).rho g x) = vLayerMap p K L x := by
  induction g using QuotientGroup.induction_on with
  | H σ =>
    unfold vLayerMap
    split_ifs with h
    · apply Int.cast_injective (α := ℝ)
      rw [h.choose_spec, h.choose_spec]
      exact congrArg _ (vbar_kbarRep p K σ x.1)
    · rfl
def vLayer [(subG p K L).Normal] : Pair (layer p K L) (trivRep (GalLK p K L) ℤ) :=
  Pair.ofMap (M := layer p K L) (M' := trivRep (GalLK p K L) ℤ)
    (mkLin (A := layer p K L) (B := trivRep (GalLK p K L) ℤ) (vLayerMap p K L))
    continuous_of_discreteTopology (fun g x => vLayerMap_rho p K L g x)
abbrev Br : Type := (kbarT p K).H 2
def BrLK [(subG p K L).Normal] : Submodule ℤ (Br p K) := LinearMap.range ((layerInf p K L).hom.H 2)
variable {p K L} in

def resPair (h : K ≤ L) : Pair (kbarT p K) (kbarT p L) where
  φ := resGK h
  u := LinearMap.id
  φ_cont := resGK_continuous h
  u_cont := continuous_id
  equiv _ _ := rfl
variable {p K L} in

def BrKer (h : K ≤ L) : Submodule ℤ (Br p K) := LinearMap.ker ((resPair h).hom.H 2)
abbrev urT : TRep ℤ (GalLK p K (MaximalUnramifiedExtension p K)) := layer p K (MaximalUnramifiedExtension p K)
def IsInv (f : (urT p K).H 2 →+ QZ) : Prop :=
  ∀ (π : (urT p K).V) (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ)
    (z : (urT p K).coch.X 2) (hz : (urT p K).coch.d 2 z = 0),
    π.1 ∈ multOf p K → (eK p K : ℝ) * vbar p π.1 = 1 → IsLocallyConstant t →
    (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) → (∀ g, z.1 g = m g • π) →
    f ((urT p K).coch.cls 2 z hz) = QuotientAddGroup.mk (t (frobLK p K (MaximalUnramifiedExtension p K)))
open Classical in

def invUr : (urT p K).H 2 →+ QZ := if h : ∃ f, IsInv p K f then h.choose else 0
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


