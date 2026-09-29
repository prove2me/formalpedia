-- Prove2me | solution 1 for AlgebraicGeometry.nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/92af8d83-6cbe-5ddf-a6aa-a25120c887ec

import Definitions.Def_ModularCurve_JZeroNeronTorsionFlag
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_FppfH0Identification
import Theorems.Thm_HopfAlgebra_exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
p2m_open "Opposite CategoryTheory.Limits WithConv"

attribute [local instance] FppfRepresentableGroupSchemeSheaf.instTopologicalSpaceZMod_definitions

namespace P2mConstLayerSheaf

noncomputable section

scoped instance instDiscreteTopologyZMod (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

section Model

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] {q : ℕ} [NeZero q]

structure IsModel (e : ZMod q → K) : Prop where
  coi : CompleteOrthogonalIdempotents e
  conv : ∀ (T : Type) [CommRing T] (φ ψ : K →ₐ[ℤ] T) (c : ZMod q),
    (toConv φ * toConv ψ) (e c) = ∑ a, φ (e a) * ψ (e (c - a))
  one : ∀ (T : Type) [CommRing T] (a : ZMod q), (1 : WithConv (K →ₐ[ℤ] T)) (e a) = if a = 0 then 1 else 0

variable {e : ZMod q → K} (he : IsModel e)
variable {X : Scheme.{0}}

abbrev ev (X : Scheme.{0}) (x : X) : Γ(X, ⊤) →+* X.residueField x := (X.Γevaluation x).hom

theorem ev_ne_zero_iff (x : X) (s : Γ(X, ⊤)) : ev X x s ≠ 0 ↔ x ∈ X.basicOpen s :=
  X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) x trivial s

theorem existsUnique_apply_ne_zero {D : Type*} [CommRing D] [IsDomain D] {u : ZMod q → D}
    (hu : CompleteOrthogonalIdempotents u) : ∃! a, u a ≠ 0 := by
  have hsum : (∑ a, u a) ≠ 0 := by rw [hu.complete]; exact one_ne_zero
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨a, ha, fun b hb => ?_⟩
  by_contra hab
  rcases mul_eq_zero.mp (hu.ortho hab) with h | h
  · exact hb h
  · exact ha h

include he in

theorem coi_map (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) :
    CompleteOrthogonalIdempotents (fun a => f (e a)) :=
  he.coi.map (f.ofConv : K →+* Γ(X, ⊤))

include he in

theorem existsUnique_ev_ne_zero (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) :
    ∃! a, ev X x (f (e a)) ≠ 0 :=
  existsUnique_apply_ne_zero ((coi_map he f).map (ev X x))

include he in

theorem existsUnique_mem_basicOpen (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) :
    ∃! a, x ∈ X.basicOpen (f (e a)) := by
  simpa only [ev_ne_zero_iff] using existsUnique_ev_ne_zero he f x

private def _root_.P2mConstLayerSheaf.idx (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) : ZMod q :=
  Classical.choose (existsUnique_mem_basicOpen he f x).exists

p2m_export "P2mConstLayerSheaf" "idx"
theorem mem_basicOpen_idx (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) :
    x ∈ X.basicOpen (f (e (idx he f x))) :=
  Classical.choose_spec (existsUnique_mem_basicOpen he f x).exists

theorem idx_eq_iff (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) (a : ZMod q) :
    idx he f x = a ↔ x ∈ X.basicOpen (f (e a)) :=
  ⟨fun h => h ▸ mem_basicOpen_idx he f x,
    fun ha => (existsUnique_mem_basicOpen he f x).unique (mem_basicOpen_idx he f x) ha⟩

theorem idx_eq_iff_ev_ne_zero (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) (a : ZMod q) :
    idx he f x = a ↔ ev X x (f (e a)) ≠ 0 := by
  rw [idx_eq_iff, ev_ne_zero_iff]

theorem ev_apply_model (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) (a : ZMod q) :
    ev X x (f (e a)) = if idx he f x = a then 1 else 0 := by
  have hcoi : CompleteOrthogonalIdempotents (fun a => ev X x (f (e a))) :=
    (he.coi.map (f.ofConv : K →+* Γ(X, ⊤))).map (ev X x)
  split_ifs with h
  · rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (hcoi.idem a)) with h0 | h1
    · exact absurd h0 ((idx_eq_iff_ev_ne_zero he f x a).mp h)
    · exact h1
  · by_contra hne
    exact h ((idx_eq_iff_ev_ne_zero he f x a).mpr hne)

theorem isLocallyConstant_idx (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) : IsLocallyConstant (idx he f) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro a
  have : idx he f ⁻¹' {a} = (X.basicOpen (f (e a)) : Set X) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    exact idx_eq_iff he f x a
  rw [this]
  exact (X.basicOpen _).isOpen

def index (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) : C(X, ZMod q) :=
  ⟨idx he f, (isLocallyConstant_idx he f).continuous⟩

@[scoped simp] theorem index_apply (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) : index he f x = idx he f x := rfl

theorem index_mul (f g : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) : index he (f * g) = index he f + index he g := by
  ext x
  simp only [ContinuousMap.add_apply, index_apply]
  rw [idx_eq_iff_ev_ne_zero]
  have hfg : (f * g) (e (idx he f x + idx he g x)) =
      ∑ a, f (e a) * g (e (idx he f x + idx he g x - a)) := by
    have := he.conv Γ(X, ⊤) f.ofConv g.ofConv (idx he f x + idx he g x)
    simpa using this
  rw [hfg, map_sum]
  simp_rw [map_mul, ev_apply_model he]
  rw [Finset.sum_eq_single (idx he f x)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem index_one : index he (1 : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) = 0 := by
  ext x
  simp only [ContinuousMap.zero_apply, index_apply]
  rw [idx_eq_iff_ev_ne_zero, he.one]
  simp

def pullbackPoint {X Y : Scheme.{0}} (π : Y ⟶ X) (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) :
    WithConv (K →ₐ[ℤ] Γ(Y, ⊤)) :=
  toConv ((π.appTop).hom.toIntAlgHom.comp f.ofConv)

theorem pullbackPoint_apply {X Y : Scheme.{0}} (π : Y ⟶ X) (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (k : K) :
    (pullbackPoint π f) k = (Scheme.Γ.map π.op) (f k) := rfl

theorem index_pullbackPoint_apply {X Y : Scheme.{0}} (π : Y ⟶ X)
    (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (y : Y) :
    index he (pullbackPoint π f) y = index he f (π y) := by
  rw [index_apply, index_apply, idx_eq_iff]
  change y ∈ Y.basicOpen (π.appTop (f (e (idx he f (π y)))))
  rw [← Scheme.preimage_basicOpen_top, Scheme.Hom.mem_preimage]
  exact mem_basicOpen_idx he f (π y)

theorem index_pullbackPoint {X Y : Scheme.{0}} (π : Y ⟶ X) (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) :
    index he (pullbackPoint π f) = (index he f).comp π.base.hom :=
  ContinuousMap.ext fun y => index_pullbackPoint_apply he π f y

omit [NeZero q] in

abbrev res (X : Scheme.{0}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

omit [NeZero q] in
theorem res_eq_one_of_isIdempotentElem (s : Γ(X, ⊤)) (hs : IsIdempotentElem s) :
    res X (X.basicOpen s) s = 1 :=
  (IsIdempotentElem.iff_eq_one_of_isUnit
    (RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toRingedSpace) s)).mp
      (hs.map (res X _))

omit [NeZero q] in
theorem res_eq_zero_of_isIdempotentElem (s : Γ(X, ⊤)) (hs : IsIdempotentElem s) :
    res X (X.basicOpen (1 - s)) s = 0 := by
  have h1 : res X (X.basicOpen (1 - s)) (1 - s) = 1 :=
    res_eq_one_of_isIdempotentElem (1 - s) hs.one_sub
  have h2 : res X (X.basicOpen (1 - s)) (s * (1 - s)) = 0 := by
    rw [mul_sub, mul_one, hs.eq, sub_self, map_zero]
  rwa [map_mul, h1, mul_one] at h2

omit [NeZero q] in
theorem basicOpen_one_sub_eq (s : Γ(X, ⊤)) (hs : IsIdempotentElem s) :
    (X.basicOpen (1 - s) : Set X) = (X.basicOpen s : Set X)ᶜ := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_compl_iff]
  rw [← ev_ne_zero_iff, ← ev_ne_zero_iff, map_sub, map_one]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hs.map (ev X x)) with h | h
  · rw [h]; simp
  · rw [h]; simp

omit [NeZero q] in

theorem eq_of_isIdempotentElem_of_basicOpen_eq (s t : Γ(X, ⊤)) (hs : IsIdempotentElem s)
    (ht : IsIdempotentElem t) (h : X.basicOpen s = X.basicOpen t) : s = t := by
  have h' : X.basicOpen (1 - s) = X.basicOpen (1 - t) := by
    apply TopologicalSpace.Opens.ext
    rw [basicOpen_one_sub_eq s hs, basicOpen_one_sub_eq t ht, h]

  let U : Bool → X.Opens := fun b => cond b (X.basicOpen s) (X.basicOpen (1 - s))
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hx : x ∈ X.basicOpen s
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      change x ∈ X.basicOpen (1 - s)
      rw [← SetLike.mem_coe, basicOpen_one_sub_eq s hs]
      exact hx
  refine X.sheaf.eq_of_locally_eq' U ⊤ (fun b => homOfLE le_top) hcover s t fun b => ?_
  cases b with
  | true =>
    change res X (X.basicOpen s) s = res X (X.basicOpen s) t
    rw [res_eq_one_of_isIdempotentElem s hs, h]
    exact (res_eq_one_of_isIdempotentElem t ht).symm
  | false =>
    change res X (X.basicOpen (1 - s)) s = res X (X.basicOpen (1 - s)) t
    rw [res_eq_zero_of_isIdempotentElem s hs, h']
    exact (res_eq_zero_of_isIdempotentElem t ht).symm

theorem apply_e_eq_of_index_eq (f g : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (h : index he f = index he g)
    (a : ZMod q) : f (e a) = g (e a) := by
  apply eq_of_isIdempotentElem_of_basicOpen_eq
  · exact (he.coi.idem a).map (f.ofConv : K →+* Γ(X, ⊤))
  · exact (he.coi.idem a).map (g.ofConv : K →+* Γ(X, ⊤))
  · ext x
    change x ∈ X.basicOpen (f (e a)) ↔ x ∈ X.basicOpen (g (e a))
    rw [← idx_eq_iff he f x a, ← idx_eq_iff he g x a]
    have := congrArg (fun F : C(X, ZMod q) => F x) h
    simpa using congrArg (· = a) this

end Model

section SheafPart

variable {q : ℕ} [Fact q.Prime]
variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] {e : ZMod q → K} (he : IsModel e)

abbrev Rq (q : ℕ) : (specInt.Fppf)ᵒᵖ ⥤ Ab.{1} :=
  (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
    (FppfKummerSES.sheafULift.{0}.obj (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} q)).obj

theorem Rq_map_up {U V : specInt.Fppf} (g : U ⟶ V) (γ : C(V.left, ZMod q)) :
    (Rq q).map g.op (ULift.up γ) = ULift.up (γ.comp g.left.base.hom) := rfl

variable (L : Sheaf (smallFppfTopology specInt) Ab.{1})
  (eL : ∀ U : specInt.Fppf, L.1.obj (op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
  (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (op V)) (k : K),
    (Additive.toMul (eL U (L.1.map f.op s))) k = (Scheme.Γ.map f.left.op) ((Additive.toMul (eL V s)) k))
  (C : Sheaf (smallFppfTopology specInt) Ab.{1}) (iC : C.obj ≅ Rq q)

def toC (U : specInt.Fppf) (γ : C(U.left, ZMod q)) : C.obj.obj (op U) := iC.inv.app (op U) (ULift.up γ)

def secC (U : specInt.Fppf) (c : C.obj.obj (op U)) : C(U.left, ZMod q) := (iC.hom.app (op U) c).down

theorem toC_secC (U : specInt.Fppf) (c : C.obj.obj (op U)) : toC C iC U (secC C iC U c) = c := by
  change (iC.hom.app (op U) ≫ iC.inv.app (op U)) c = c
  rw [Iso.hom_inv_id_app]; rfl

theorem secC_toC (U : specInt.Fppf) (γ : C(U.left, ZMod q)) : secC C iC U (toC C iC U γ) = γ := by
  change ((iC.inv.app (op U) ≫ iC.hom.app (op U)) (ULift.up γ)).down = γ
  rw [Iso.inv_hom_id_app]; rfl

theorem toC_injective (U : specInt.Fppf) : Function.Injective (toC C iC U) := fun γ γ' h => by
  rw [← secC_toC C iC U γ, ← secC_toC C iC U γ', h]

theorem toC_add (U : specInt.Fppf) (γ γ' : C(U.left, ZMod q)) :
    toC C iC U (γ + γ') = toC C iC U γ + toC C iC U γ' :=
  (iC.inv.app (op U)).hom.map_add (ULift.up γ) (ULift.up γ')

theorem toC_zero (U : specInt.Fppf) : toC C iC U 0 = 0 :=
  (iC.inv.app (op U)).hom.map_zero

theorem secC_sub (U : specInt.Fppf) (c c' : C.obj.obj (op U)) :
    secC C iC U (c - c') = secC C iC U c - secC C iC U c' :=
  congrArg ULift.down ((iC.hom.app (op U)).hom.map_sub c c')

theorem map_toC {U V : specInt.Fppf} (g : U ⟶ V) (γ : C(V.left, ZMod q)) :
    C.obj.map g.op (toC C iC V γ) = toC C iC U (γ.comp g.left.base.hom) := by
  change (iC.inv.app (op V) ≫ C.obj.map g.op) (ULift.up γ) = _
  rw [← iC.inv.naturality]
  rfl

theorem secC_map {U V : specInt.Fppf} (g : U ⟶ V) (c : C.obj.obj (op V)) :
    secC C iC U (C.obj.map g.op c) = (secC C iC V c).comp g.left.base.hom := by
  conv_lhs => rw [← toC_secC C iC V c, map_toC, secC_toC]

def point (U : specInt.Fppf) (s : L.1.obj (op U)) : WithConv (K →ₐ[ℤ] Γ(U.left, ⊤)) :=
  Additive.toMul (eL U s)

include hnat in
theorem point_map {U V : specInt.Fppf} (g : U ⟶ V) (s : L.1.obj (op V)) :
    point L eL U (L.1.map g.op s) = pullbackPoint g.left (point L eL V s) := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  exact hnat g s k

theorem point_add (U : specInt.Fppf) (s s' : L.1.obj (op U)) :
    point L eL U (s + s') = point L eL U s * point L eL U s' := by
  simp [point]

theorem point_zero (U : specInt.Fppf) : point L eL U 0 = 1 := by simp [point]

theorem point_injective (U : specInt.Fppf) : Function.Injective (point L eL U) := by
  intro s s' h
  exact (eL U).injective (Additive.toMul.injective h)

def fvalApp (U : specInt.Fppf) : L.1.obj (op U) →+ C.obj.obj (op U) where
  toFun s := toC C iC U (index he (point L eL U s))
  map_zero' := by rw [point_zero, index_one, toC_zero]
  map_add' s s' := by rw [point_add, index_mul, toC_add]

theorem fvalApp_apply (U : specInt.Fppf) (s : L.1.obj (op U)) :
    fvalApp he L eL C iC U s = toC C iC U (index he (point L eL U s)) := rfl

def fval : L ⟶ C :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom (fvalApp he L eL C iC (unop U))
      naturality := fun V U g => by
        ext s
        change fvalApp he L eL C iC (unop U) (L.1.map g s) = C.obj.map g (fvalApp he L eL C iC (unop V) s)
        rw [fvalApp_apply, fvalApp_apply, show g = g.unop.op from rfl, point_map L eL hnat,
          index_pullbackPoint, map_toC] }

theorem fval_app_apply (U : specInt.Fppf) (s : L.1.obj (op U)) :
    (fval he L eL hnat C iC).hom.app (op U) s = toC C iC U (index he (point L eL U s)) := rfl

theorem secC_fval (U : specInt.Fppf) (s : L.1.obj (op U)) :
    secC C iC U ((fval he L eL hnat C iC).hom.app (op U) s) = index he (point L eL U s) := by
  rw [fval_app_apply, secC_toC]

variable (huniq : ∀ (T : Type) [CommRing T] (φ ψ : K →ₐ[ℤ] T), (∀ a, φ (e a) = ψ (e a)) → φ = ψ)

include huniq in
theorem fvalApp_injective (U : specInt.Fppf) : Function.Injective (fvalApp he L eL C iC U) := by
  intro s s' h
  apply point_injective L eL U
  have hidx : index he (point L eL U s) = index he (point L eL U s') := toC_injective C iC U h
  refine WithConv.ext (huniq _ _ _ fun a => ?_)
  exact apply_e_eq_of_index_eq he _ _ hidx a

include huniq in

theorem mono_fval : Mono (fval he L eL hnat C iC) := by
  haveI : ∀ U : (specInt.Fppf)ᵒᵖ, Mono ((fval he L eL hnat C iC).hom.app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).mpr (fvalApp_injective he L eL C iC huniq (unop U))
  have : Mono (fval he L eL hnat C iC).hom := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

def SES : ShortComplex (Sheaf (smallFppfTopology specInt) Ab.{1}) :=
  ShortComplex.mk (fval he L eL hnat C iC) (cokernel.π (fval he L eL hnat C iC)) (cokernel.condition _)

include huniq in
theorem SES_shortExact : (SES he L eL hnat C iC).ShortExact :=
  haveI : Mono (SES he L eL hnat C iC).f := mono_fval he L eL hnat C iC huniq
  haveI : Epi (SES he L eL hnat C iC).g := coequalizer.π_epi
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

end SheafPart

section Indicator

variable {q : ℕ} [Fact q.Prime]
variable {X : Scheme.{0}} (γ : C(X, ZMod q))

def piece (a : ZMod q) : X.Opens :=
  ⟨γ ⁻¹' {a}, (isClopen_discrete ({a} : Set (ZMod q))).isOpen.preimage γ.continuous⟩

theorem mem_piece {a : ZMod q} {x : X} : x ∈ piece γ a ↔ γ x = a := Iff.rfl

theorem iSup_piece : (⊤ : X.Opens) ≤ iSup (piece γ) := fun x _ =>
  TopologicalSpace.Opens.mem_iSup.mpr ⟨γ x, (mem_piece γ).mpr rfl⟩

theorem piece_inf_piece {a a' : ZMod q} (h : a ≠ a') : piece γ a ⊓ piece γ a' = ⊥ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_piece,
    TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hx'
  exact h (hx.symm.trans hx')

theorem eq_of_eq_bot {V : X.Opens} (hV : V = ⊥) (s t : Γ(X, V)) : s = t := by
  subst hV; exact Subsingleton.elim s t

theorem exists_glue (v : ∀ a : ZMod q, Γ(X, piece γ a)) :
    ∃ s : Γ(X, ⊤), ∀ a, res X (piece γ a) s = v a := by
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf (piece γ) v := by
    intro a a'
    by_cases h : a = a'
    · subst h; rfl
    · exact eq_of_eq_bot (piece_inf_piece γ h) _ _
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (piece γ) ⊤ (fun a => homOfLE le_top)
    (iSup_piece γ) v hcomp
  exact ⟨s, hs⟩

theorem eq_of_res_piece_eq (s t : Γ(X, ⊤)) (h : ∀ a, res X (piece γ a) s = res X (piece γ a) t) :
    s = t :=
  X.sheaf.eq_of_locally_eq' (piece γ) ⊤ (fun a => homOfLE le_top) (iSup_piece γ) s t h

theorem exists_indicator :
    ∃ b : ZMod q → Γ(X, ⊤), CompleteOrthogonalIdempotents b ∧
      ∀ a c, res X (piece γ a) (b c) = if a = c then 1 else 0 := by
  have h := fun c : ZMod q => exists_glue γ (fun a => if a = c then (1 : Γ(X, piece γ a)) else 0)
  choose b hb using h
  refine ⟨b, ⟨⟨fun c => ?_, fun c c' hcc' => ?_⟩, ?_⟩, fun a c => hb c a⟩
  · apply eq_of_res_piece_eq γ; intro a
    rw [map_mul, hb]; split_ifs <;> simp
  · apply eq_of_res_piece_eq γ; intro a
    rw [map_mul, hb, hb, map_zero]
    by_cases h : a = c
    · rw [if_pos h, if_neg (fun h' => hcc' (h.symm.trans h')), one_mul]
    · rw [if_neg h, zero_mul]
  · apply eq_of_res_piece_eq γ; intro a
    rw [map_sum, map_one, Finset.sum_eq_single a]
    · rw [hb, if_pos rfl]
    · intro c _ hc; rw [hb, if_neg (Ne.symm hc)]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem piece_le_basicOpen {b : ZMod q → Γ(X, ⊤)}
    (hb : ∀ a c, res X (piece γ a) (b c) = if a = c then 1 else 0) (a : ZMod q) :
    piece γ a ≤ X.basicOpen (b a) := by
  have h1 : X.basicOpen (res X (piece γ a) (b a)) = piece γ a := by
    rw [hb, if_pos rfl]; exact X.basicOpen_of_isUnit isUnit_one
  have h2 := Scheme.basicOpen_res X (b a) (homOfLE (le_top : piece γ a ≤ ⊤)).op
  change X.basicOpen (res X (piece γ a) (b a)) = _ at h2
  rw [h1] at h2
  exact inf_eq_left.mp h2.symm

theorem exists_mul_mul_eq {b : ZMod q → Γ(X, ⊤)}
    (hb : ∀ a c, res X (piece γ a) (b c) = if a = c then 1 else 0) (r : Γ(X, ⊤)) (a : ZMod q)
    (hr : IsUnit (res X (piece γ a) r)) : ∃ v : Γ(X, ⊤), v * (r * b a) = b a := by
  obtain ⟨v, hv⟩ := exists_glue γ
    (fun c => if h : c = a then (by subst h; exact ((hr.unit⁻¹ : (Γ(X, piece γ c))ˣ) : Γ(X, piece γ c))) else 0)
  refine ⟨v, eq_of_res_piece_eq γ _ _ fun c => ?_⟩
  rw [map_mul, map_mul, hv, hb]
  by_cases h : c = a
  · subst h
    simp only [dite_true, if_true, mul_one]
    exact hr.unit.inv_val
  · rw [if_neg h, mul_zero, mul_zero]

end Indicator

section Fibre

variable {p : ℕ} [Fact p.Prime] {q : ℕ} [Fact q.Prime]
variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] {e : ZMod q → K} (he : IsModel e)

def fib (p : ℕ) (X : Scheme.{0}) : Set X := {x | x ∉ X.basicOpen ((p : Γ(X, ⊤)))}

theorem mem_fib_iff_map (p : ℕ) {X Y : Scheme.{0}} (π : Y ⟶ X) (y : Y) :
    y ∈ fib p Y ↔ π y ∈ fib p X := by
  simp only [fib, Set.mem_setOf_eq]
  rw [← Scheme.Hom.mem_preimage (f := π), Scheme.preimage_basicOpen_top, map_natCast]

include he in

theorem index_eq_zero_of_mem_fib (hfib : ∀ a : ZMod q, a ≠ 0 → ∃ u : K, u * (p * e a) = e a)
    {X : Scheme.{0}} (f : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) (x : X) (hx : x ∈ fib p X) :
    index he f x = 0 := by
  by_contra hne
  obtain ⟨u, hu⟩ := hfib _ hne
  have h1 : ev X x (f (e (index he f x))) = 1 := by rw [index_apply, ev_apply_model he, if_pos rfl]
  have h2 := congrArg (fun k => ev X x (f k)) hu
  simp only [map_mul, map_natCast, h1, mul_one] at h2
  have hp0 : (p : X.residueField x) = 0 := by
    have : ¬ (ev X x (p : Γ(X, ⊤)) ≠ 0) := by rw [ev_ne_zero_iff]; exact hx
    rwa [not_not, map_natCast] at this
  rw [hp0, mul_zero] at h2
  exact zero_ne_one h2

theorem isUnit_res_natCast {X : Scheme.{0}} (V : X.Opens) (hV : ∀ x ∈ V, x ∉ fib p X) :
    IsUnit (res X V (p : Γ(X, ⊤))) := by
  apply RingedSpace.isUnit_of_isUnit_germ (X := X.toLocallyRingedSpace.toRingedSpace) V
  intro x hx
  have hxD : x ∈ X.basicOpen ((p : Γ(X, ⊤))) := by
    have := hV x hx; simp only [fib, Set.mem_setOf_eq, not_not] at this; exact this
  have := (X.mem_basicOpen ((p : Γ(X, ⊤))) x trivial).mp hxD
  rwa [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE le_top) x hx]

theorem exists_point_index_eq
    (hex : ∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
      (∀ a, a ≠ 0 → ∃ v : T, v * (p * b a) = b a) → ∃ φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a)
    {X : Scheme.{0}} (γ : C(X, ZMod q)) (hγ : ∀ x ∈ fib p X, γ x = 0) :
    ∃ φ : K →ₐ[ℤ] Γ(X, ⊤), index he (toConv φ) = γ := by
  obtain ⟨b, hb, hbres⟩ := exists_indicator γ
  have hv : ∀ a, a ≠ 0 → ∃ v : Γ(X, ⊤), v * (p * b a) = b a := by
    intro a ha
    apply exists_mul_mul_eq γ hbres (p : Γ(X, ⊤)) a
    apply isUnit_res_natCast
    intro x hx hxfib
    exact ha (((mem_piece γ).mp hx).symm.trans (hγ x hxfib))
  obtain ⟨φ, hφ⟩ := hex Γ(X, ⊤) b hb hv
  refine ⟨φ, ContinuousMap.ext fun x => ?_⟩
  rw [index_apply, idx_eq_iff]
  change x ∈ X.basicOpen (φ (e (γ x)))
  rw [hφ]
  exact piece_le_basicOpen γ hbres (γ x) ((mem_piece γ).mpr rfl)

theorem exists_point_index_eq'
    (hex : ∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
      ∃ φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a)
    {X : Scheme.{0}} (γ : C(X, ZMod q)) :
    ∃ φ : K →ₐ[ℤ] Γ(X, ⊤), index he (toConv φ) = γ := by
  obtain ⟨b, hb, hbres⟩ := exists_indicator γ
  obtain ⟨φ, hφ⟩ := hex Γ(X, ⊤) b hb
  refine ⟨φ, ContinuousMap.ext fun x => ?_⟩
  rw [index_apply, idx_eq_iff]
  change x ∈ X.basicOpen (φ (e (γ x)))
  rw [hφ]
  exact piece_le_basicOpen γ hbres (γ x) ((mem_piece γ).mpr rfl)

theorem specInt_eq_of_mem_fib (t t' : specInt) (ht : t ∈ fib p specInt) (ht' : t' ∈ fib p specInt) :
    t = t' := by
  have key : ∀ s : specInt, s ∈ fib p specInt → (s : PrimeSpectrum ℤ).asIdeal = Ideal.span {(p : ℤ)} := by
    intro s hs
    simp only [fib, Set.mem_setOf_eq] at hs
    rw [basicOpen_eq_of_affine', map_natCast] at hs
    erw [PrimeSpectrum.mem_basicOpen] at hs
    rw [not_not] at hs
    have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    refine (hmax.eq_of_le s.2.ne_top ?_).symm
    rw [Ideal.span_singleton_le_iff_mem]
    exact hs
  exact PrimeSpectrum.ext ((key t ht).trans (key t' ht').symm)

end Fibre

section Products

abbrev homS (U : specInt.Fppf) : U.left ⟶ specInt := U.hom

scoped instance (U : specInt.Fppf) : Flat (homS U) := (inferInstance : Flat U.hom)
scoped instance (U : specInt.Fppf) : LocallyOfFinitePresentation (homS U) :=
  (inferInstance : LocallyOfFinitePresentation U.hom)

def prodObj (U V : specInt.Fppf) : specInt.Fppf :=
  Scheme.Fppf.mk (pullback.snd (homS U) (homS V) ≫ homS V)

def prodFst (U V : specInt.Fppf) : prodObj U V ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst (homS U) (homS V)) pullback.condition

def prodSnd (U V : specInt.Fppf) : prodObj U V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.snd (homS U) (homS V)) rfl

theorem prodFst_left (U V : specInt.Fppf) : (prodFst U V).left = pullback.fst (homS U) (homS V) := rfl
theorem prodSnd_left (U V : specInt.Fppf) : (prodSnd U V).left = pullback.snd (homS U) (homS V) := rfl

theorem exists_prod_point {U V : specInt.Fppf} (u : U.left) (v : V.left) (h : homS U u = homS V v) :
    ∃ w : (prodObj U V).left, (prodFst U V).left w = u ∧ (prodSnd U V).left w = v :=
  Scheme.Pullback.exists_preimage_pullback u v h

end Products

section Surj

variable {p : ℕ} [Fact p.Prime] {q : ℕ} [Fact q.Prime]
variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] {e : ZMod q → K} (he : IsModel e)
variable (L : Sheaf (smallFppfTopology specInt) Ab.{1})
  (eL : ∀ U : specInt.Fppf, L.1.obj (op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
  (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (op V)) (k : K),
    (Additive.toMul (eL U (L.1.map f.op s))) k = (Scheme.Γ.map f.left.op) ((Additive.toMul (eL V s)) k))
  (C : Sheaf (smallFppfTopology specInt) Ab.{1}) (iC : C.obj ≅ Rq q)
  (huniq : ∀ (T : Type) [CommRing T] (φ ψ : K →ₐ[ℤ] T), (∀ a, φ (e a) = ψ (e a)) → φ = ψ)

local notation "SS" => SES he L eL hnat C iC

theorem exists_preimage_of_map_eq_zero {S : ShortComplex (Sheaf (smallFppfTopology specInt) Ab.{1})}
    (hS : S.ShortExact) (Y : specInt.Fppf) (x : S.X₂.obj.obj (op Y)) (hx : S.g.hom.app (op Y) x = 0) :
    ∃ w, S.f.hom.app (op Y) w = x := by
  let evY : Sheaf (smallFppfTopology specInt) Ab.{1} ⥤ Ab.{1} :=
    sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op Y)
  have h := isLimitForkMapOfIsLimit' evY S.zero hS.fIsKernel
  have hex := ShortComplex.exact_of_f_is_kernel (S.map evY) h
  rw [ShortComplex.ab_exact_iff] at hex
  exact hex x hx

theorem app_map {F G : Sheaf (smallFppfTopology specInt) Ab.{1}} (φ : F ⟶ G) {Y Y' : specInt.Fppf}
    (f : Y' ⟶ Y) (t : F.obj.obj (op Y)) :
    φ.hom.app (op Y') (F.obj.map f.op t) = G.obj.map f.op (φ.hom.app (op Y) t) := by
  rw [← ConcreteCategory.comp_apply, φ.hom.naturality]; rfl

theorem map_map (F : Sheaf (smallFppfTopology specInt) Ab.{1}) {Y Y' Y'' : specInt.Fppf}
    (f : Y' ⟶ Y) (k : Y'' ⟶ Y') (t : F.obj.obj (op Y)) :
    F.obj.map k.op (F.obj.map f.op t) = F.obj.map (k ≫ f).op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

theorem g_app_sub {W : specInt.Fppf} (x y : C.obj.obj (op W)) :
    (SES he L eL hnat C iC).g.hom.app (op W) (x - y) =
      (SES he L eL hnat C iC).g.hom.app (op W) x - (SES he L eL hnat C iC).g.hom.app (op W) y :=
  ((SES he L eL hnat C iC).g.hom.app (op W)).hom.map_sub x y

theorem g_app_map {W W' : specInt.Fppf} (k : W' ⟶ W) (x : C.obj.obj (op W)) :
    (SES he L eL hnat C iC).g.hom.app (op W') (C.obj.map k.op x) =
      (SES he L eL hnat C iC).X₃.obj.map k.op ((SES he L eL hnat C iC).g.hom.app (op W) x) :=
  app_map _ k x

theorem g_f_app {W : specInt.Fppf} (s : L.1.obj (op W)) :
    (SES he L eL hnat C iC).g.hom.app (op W) ((SES he L eL hnat C iC).f.hom.app (op W) s) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
  have hfg : (SES he L eL hnat C iC).f.hom ≫ (SES he L eL hnat C iC).g.hom =
      ((SES he L eL hnat C iC).f ≫ (SES he L eL hnat C iC).g).hom := rfl
  rw [hfg, (SES he L eL hnat C iC).zero]
  rfl

theorem exists_section_of_index {U : specInt.Fppf} (φ : K →ₐ[ℤ] Γ(U.left, ⊤)) :
    ∃ s : L.1.obj (op U), point L eL U s = toConv φ :=
  ⟨(eL U).symm (Additive.ofMul (toConv φ)), by simp [point]⟩

theorem exists_family_of_mem {U : specInt.Fppf} {R : Sieve U} (hR : R ∈ smallFppfTopology specInt U) :
    ∃ (ι : Type) (Y : ι → specInt.Fppf) (f : ∀ i, Y i ⟶ U),
      (∀ i, R (f i)) ∧ (∀ u : U.left, ∃ (i : ι) (y : (Y i).left), (f i).left y = u) ∧
      Sieve.generate (Presieve.ofArrows Y f) ∈ smallFppfTopology specInt U := by
  have hR' := (Scheme.mem_overGrothendieckTopology fppfProperty _ _).mp
    ((Functor.mem_restrictedTopology_iff (G := Scheme.Fppf.forget specInt)
      (K := fppfTopology.over specInt)).mp hR)
  obtain ⟨𝒰, h𝒰, hle⟩ := hR'
  have hj : ∀ j : 𝒰.I₀, fppfProperty (𝒰.X j ↘ specInt) := fun j => by
    rw [← comp_over (𝒰.f j) specInt]
    exact fppfProperty.comp_mem _ _ (𝒰.map_prop j) U.prop
  let Yc : 𝒰.I₀ → specInt.Fppf := fun i => (𝒰.X i).asOverProp specInt (hj i)
  let fc : ∀ i, Yc i ⟶ U := fun i => (𝒰.f i).asOverProp specInt
  have hf : ∀ i, R (fc i) := fun i => by
    have : R.functorPushforward _ ((Scheme.Fppf.forget specInt).map (fc i)) :=
      hle _ _ (Presieve.ofArrows.mk i)
    rwa [Sieve.functorPushforward_apply, Sieve.mem_functorPushforward_iff_of_full_of_faithful] at this
  refine ⟨𝒰.I₀, Yc, fc, hf, fun u => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := 𝒰.covers u
    exact ⟨𝒰.idx u, y, hy⟩
  · refine (Functor.mem_restrictedTopology_iff (G := Scheme.Fppf.forget specInt)
      (K := fppfTopology.over specInt)).mpr
      ((Scheme.mem_overGrothendieckTopology fppfProperty _ _).mpr ⟨𝒰, h𝒰, ?_⟩)
    rintro Z g ⟨i⟩
    exact ⟨Yc i, fc i, 𝟙 _, Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i), (Category.id_comp _).symm⟩

include huniq in

theorem surjective_g_app_terminal
    (hfib : ∀ a : ZMod q, a ≠ 0 → ∃ u : K, u * (p * e a) = e a)
    (hex : ∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
      (∀ a, a ≠ 0 → ∃ v : T, v * (p * b a) = b a) → ∃ φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a) :
    Function.Surjective ((SES he L eL hnat C iC).g.hom.app (op (fppfTerminal specInt))) := by
  classical
  intro q₀
  have hSE : (SS).ShortExact := SES_shortExact he L eL hnat C iC huniq
  have hepi : Epi (SS).g := hSE.epi_g
  have hls : Sheaf.IsLocallySurjective (SS).g :=
    (Sheaf.isLocallySurjective_iff_epi' (J := smallFppfTopology specInt) (A := Ab.{1}) (SS).g).2 hepi

  have hSimg : Presheaf.imageSieve (SS).g.hom q₀ ∈ smallFppfTopology specInt (fppfTerminal specInt) :=
    Presheaf.imageSieve_mem _ (SS).g.hom q₀
  obtain ⟨ι, Y, f, hf, hsurj, hgen⟩ := exists_family_of_mem hSimg
  have hlift : ∀ i, ∃ c : C.obj.obj (op (Y i)), (SS).g.hom.app _ c = (SS).X₃.obj.map (f i).op q₀ :=
    fun i => hf i
  choose c hc using hlift

  set γ : ∀ i, C((Y i).left, ZMod q) := fun i => secC C iC (Y i) (c i) with hγ

  have hA : ∀ i j (y : (Y i).left) (y' : (Y j).left), y ∈ fib p (Y i).left → y' ∈ fib p (Y j).left →
      γ i y = γ j y' := by
    intro i j y y' hy hy'
    let W := prodObj (Y i) (Y j)
    let πi := prodFst (Y i) (Y j)
    let πj := prodSnd (Y i) (Y j)
    have hcomm : πi ≫ f i = πj ≫ f j := (fppfTerminalIsTerminal specInt).hom_ext _ _

    have hdiff : (SS).g.hom.app _ (C.obj.map πi.op (c i) - C.obj.map πj.op (c j)) = 0 := by
      rw [g_app_sub, g_app_map, g_app_map, hc, hc, map_map, map_map, hcomm, sub_self]
    obtain ⟨w, hw⟩ := exists_preimage_of_map_eq_zero hSE W _ hdiff

    have hsec : (γ i).comp πi.left.base.hom - (γ j).comp πj.left.base.hom = index he (point L eL W w) := by
      rw [← secC_fval he L eL hnat C iC W w]
      change _ = secC C iC W ((SS).f.hom.app (op W) w)
      rw [hw, secC_sub, secC_map, secC_map]

    have hyy' : homS (Y i) y = homS (Y j) y' :=
      specInt_eq_of_mem_fib _ _ ((mem_fib_iff_map p (homS (Y i)) y).mp hy)
        ((mem_fib_iff_map p (homS (Y j)) y').mp hy')
    obtain ⟨z, hz1, hz2⟩ := exists_prod_point y y' hyy'
    have hz : z ∈ fib p W.left := (mem_fib_iff_map p πi.left z).mpr (by rw [prodFst_left]; exact hz1.symm ▸ hy)
    have h0 := index_eq_zero_of_mem_fib he hfib (point L eL W w) z hz
    have := congrArg (fun F : C(W.left, ZMod q) => F z) hsec
    simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, index_apply] at this
    rw [← index_apply, h0, sub_eq_zero] at this
    convert this using 2
    · exact hz1.symm
    · exact hz2.symm

  let γ₀ : ZMod q := if h : ∃ (i : ι) (y : (Y i).left), y ∈ fib p (Y i).left then γ h.choose h.choose_spec.choose else 0
  have hγ₀ : ∀ i (y : (Y i).left), y ∈ fib p (Y i).left → γ i y = γ₀ := by
    intro i y hy
    have h : ∃ (i : ι) (y : (Y i).left), y ∈ fib p (Y i).left := ⟨i, y, hy⟩
    simp only [γ₀, dif_pos h]
    exact hA i _ y _ hy h.choose_spec.choose_spec
  set c₀ : C.obj.obj (op (fppfTerminal specInt)) := toC C iC (fppfTerminal specInt) (ContinuousMap.const _ γ₀) with hc₀
  refine ⟨c₀, ?_⟩

  have hneg : ∀ (V : specInt.Fppf) (x : C(V.left, ZMod q)), toC C iC V (-x) = - toC C iC V x :=
    fun V x => (iC.inv.app (op V)).hom.map_neg (ULift.up x)
  have hloc : ∀ i, (SS).X₃.obj.map (f i).op (q₀ - (SS).g.hom.app _ c₀) = 0 := by
    intro i

    have hvan : ∀ y ∈ fib p (Y i).left, ((γ i - ContinuousMap.const (Y i).left γ₀ : C((Y i).left, ZMod q))) y = 0 :=
      fun y hy => by simp [hγ₀ i y hy]
    obtain ⟨φ, hφ⟩ := exists_point_index_eq he hex (γ i - ContinuousMap.const _ γ₀) hvan
    obtain ⟨s, hs⟩ := exists_section_of_index L eL φ
    have hfs : (SS).f.hom.app (op (Y i)) s = c i - C.obj.map (f i).op c₀ := by
      change (fval he L eL hnat C iC).hom.app (op (Y i)) s = _
      rw [fval_app_apply, hs, hφ, hc₀, map_toC, ← toC_secC C iC (Y i) (c i)]
      change toC C iC (Y i) (γ i - ContinuousMap.const (Y i).left γ₀) =
        toC C iC (Y i) (γ i) - toC C iC (Y i) (ContinuousMap.const (Y i).left γ₀)
      rw [sub_eq_add_neg, toC_add, hneg, ← sub_eq_add_neg]
    rw [map_sub, ← g_app_map, ← hc, ← g_app_sub, ← hfs, g_f_app]

  have hP : Presieve.IsSheaf (smallFppfTopology specInt) ((SS).X₃.obj ⋙ forget Ab.{1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology specInt) (SS).X₃.obj (forget Ab.{1})).1
        (SS).X₃.property)
  symm
  rw [← sub_eq_zero]
  refine (hP _ hgen).isSeparatedFor.ext ?_
  rintro W h ⟨W', k, f', ⟨i⟩, rfl⟩
  change (SS).X₃.obj.map (k ≫ f i).op (q₀ - (SS).g.hom.app _ c₀) = (SS).X₃.obj.map (k ≫ f i).op 0
  rw [map_zero, ← map_map, hloc, map_zero]

include huniq in

theorem surjective_fppfCohomologyMap_g_zero
    (hfib : ∀ a : ZMod q, a ≠ 0 → ∃ u : K, u * (p * e a) = e a)
    (hex : ∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
      (∀ a, a ≠ 0 → ∃ v : T, v * (p * b a) = b a) → ∃ φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a) :
    Function.Surjective (fppfCohomologyMap specInt (SES he L eL hnat C iC).g 0) := by
  intro y
  obtain ⟨c, hc⟩ := surjective_g_app_terminal he L eL hnat C iC huniq hfib hex
    (fppfCohomologyZeroAddEquiv specInt (SS).X₃ y)
  refine ⟨(fppfCohomologyZeroAddEquiv specInt (SS).X₂).symm c, ?_⟩
  rw [← fppfCohomologyZeroAddEquiv_symm_naturality, hc, AddEquiv.symm_apply_apply]

theorem isIso_fval
    (hex : ∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
      ∃! φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a) :
    IsIso (fval he L eL hnat C iC) := by
  have huniq' : ∀ (T : Type) [CommRing T] (φ ψ : K →ₐ[ℤ] T), (∀ a, φ (e a) = ψ (e a)) → φ = ψ := by
    intro T _ φ ψ h
    obtain ⟨χ, -, hχ⟩ := hex T (fun a => ψ (e a)) (he.coi.map (ψ : K →+* T))
    exact (hχ φ h).trans (hχ ψ fun _ => rfl).symm
  haveI : Mono (fval he L eL hnat C iC) := mono_fval he L eL hnat C iC huniq'

  have hsurj : ∀ U : (specInt.Fppf)ᵒᵖ, Function.Surjective ((fval he L eL hnat C iC).hom.app U) := by
    intro U cU
    obtain ⟨φ, hφ⟩ := exists_point_index_eq' he (fun T _ b hb => (hex T b hb).exists) (secC C iC (unop U) cU)
    obtain ⟨s, hs⟩ := exists_section_of_index L eL φ
    refine ⟨s, ?_⟩
    change (fval he L eL hnat C iC).hom.app (op (unop U)) s = cU
    rw [fval_app_apply, hs, hφ, toC_secC]
  haveI : Sheaf.IsLocallySurjective (fval he L eL hnat C iC) :=
    Presheaf.isLocallySurjective_of_surjective _ (fval he L eL hnat C iC).hom hsurj
  haveI : Epi (fval he L eL hnat C iC) :=
    (Sheaf.isLocallySurjective_iff_epi' (J := smallFppfTopology specInt) (A := Ab.{1}) _).1 inferInstance
  exact isIso_of_mono_of_epi _

end Surj

end

end P2mConstLayerSheaf
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two.P2mConstLayerSheaf"

open P2mConstLayerSheaf in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.sheafULift.{0}.obj
        (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} q)).obj) :
    Nonempty (L ≅ C) ∨
    ∃ (Q : Sheaf (smallFppfTopology specInt) Ab.{1}) (f : L ⟶ C) (g : C ⟶ Q)
      (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧
        Function.Surjective (fppfCohomologyMap specInt g 0) := by
  obtain ⟨ee, hcoi, hconv, hone, hdich⟩ :=
    HopfAlgebra.exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two
      p q hq2 K ‹_› ‹_› ‹_› ‹_› hff hgenq hgal
  have hmodel : IsModel ee := ⟨hcoi, hconv, hone⟩
  rcases hdich with hconst | ⟨hfib, hex⟩
  ·
    haveI := isIso_fval hmodel L e hnat C iC hconst
    exact Or.inl ⟨asIso (fval hmodel L e hnat C iC)⟩
  ·
    have huniq : ∀ (T : Type) [CommRing T] (φ ψ : K →ₐ[ℤ] T), (∀ a, φ (ee a) = ψ (ee a)) → φ = ψ := by
      intro T _ φ ψ h
      have hv : ∀ a, a ≠ 0 → ∃ v : T, v * (p * ψ (ee a)) = ψ (ee a) := fun a ha => by
        obtain ⟨u, hu⟩ := hfib a ha
        exact ⟨ψ u, by simpa using congrArg ψ hu⟩
      obtain ⟨χ, -, hχ⟩ := hex T (fun a => ψ (ee a)) (hcoi.map (ψ : K →+* T)) hv
      exact (hχ φ h).trans (hχ ψ fun _ => rfl).symm
    refine Or.inr ⟨(SES hmodel L e hnat C iC).X₃, (SES hmodel L e hnat C iC).f,
      (SES hmodel L e hnat C iC).g, (SES hmodel L e hnat C iC).zero,
      SES_shortExact hmodel L e hnat C iC huniq, ?_⟩
    exact surjective_fppfCohomologyMap_g_zero hmodel L e hnat C iC huniq hfib
      (fun T _ b hb hbp => (hex T b hb hbp).exists)

end S_AlgebraicGeometry_nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two
end P2MW
export P2MW.S_AlgebraicGeometry_nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two (solution)
