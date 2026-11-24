-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:53:12.499141+00:00
-- url     : https://prove2.me/theorems/98d87c14-3b9f-4167-b0e1-698963653d76
-- title:
--   Mk Mem Admissible At Iff Cocycle
-- statement:
--   Definitions and structural lemmas for Mk Mem Admissible At Iff Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_ReciprocityTheory_Gal_LocalEulerCharAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalEulerChar_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalFinitenessAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalFiniteness_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDualityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_LocalTateDuality_restrict
import Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonalityAt_restrict
import Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonality_restrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
inductive LType
  | G
  | Bd
  deriving DecidableEq
def block (w : ℤ) (t : ℕ) : Multiset ℤ := (Finset.Ico w (w + t)).val
structure TopData (n r : ℕ) where
  h : ZMod n → ℕ
  η : ZMod n → ℕ
  ty : ZMod n → LType
  w : ZMod n → ℤ
  t : ℕ
  lows : ZMod n → Multiset ℤ
  cloud : ZMod n → Multiset ℤ
  two_le_h : ∀ i, 2 ≤ h i
  one_le_η : ∀ i, 1 ≤ η i
  one_le_letterBlockLength : 1 ≤ t
  card_eq : ∀ i, Multiset.card (lows i + cloud i) = r
  range : ∀ i, ∀ u ∈ lows i + cloud i + block (w i) t, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1
  lowG : ∀ i, ty i = LType.G → ∀ u ∈ lows i + block (w i) t, 1 ≤ u ∧ u ≤ (η i : ℤ)
  cloudG : ∀ i, ty i = LType.G → ∀ u ∈ cloud i, (η i : ℤ) < u
  lowBd : ∀ i, ty i = LType.Bd → ∀ u ∈ lows i + block (w i) t, (h i : ℤ) - η i ≤ u ∧ u ≤ (h i : ℤ) - 1
  cloudBd : ∀ i, ty i = LType.Bd → ∀ u ∈ cloud i, u < (h i : ℤ) - η i
theorem mem_block {w u : ℤ} {t : ℕ} : u ∈ block w t ↔ w ≤ u ∧ u < w + t := by
  simp [block]
namespace TopData
variable {n r : ℕ} (D : TopData n r)
def U (i : ZMod n) : Multiset ℤ := D.lows i + D.cloud i
def B (i : ZMod n) : Multiset ℤ := block (D.w i) D.t
def Ut (i : ZMod n) : Multiset ℤ := D.U i + D.B i
def sg (l : ℕ) (i : ZMod n) : ℕ := GlobalTheory.PhiGam.sg l D.h i
def wst (i : ZMod n) : ℤ := (D.h i : ℤ) - D.w i
def d (i : ZMod n) : ℕ := Multiset.card ((D.U i).filter (· < D.w i))
def dsum [NeZero n] : ℕ := ∑ i, D.d i
def T1 (l : ℕ) : Prop := ∀ i, D.η i + 4 * D.sg l i + 6 < l
def T2 (l : ℕ) : Prop := ∀ i, ∀ u ∈ D.lows i, ∀ β ∈ D.B i, (D.sg l i : ℤ) + 2 < |u - β|
def cloudRes (i : ZMod n) (u : ℤ) : ℤ :=
  match D.ty i with
  | LType.G => u
  | LType.Bd => (D.h i : ℤ) - u
def T3 (l : ℕ) : Prop :=
  ∀ i, ∀ u ∈ D.cloud i, ∀ y : ℤ, -2 * (D.sg l i : ℤ) - 2 ≤ y → y ≤ (D.η i : ℤ) + 2 * D.sg l i + 3 →
    ¬ D.cloudRes i u ≡ y [ZMOD l]
end TopData
def exData : TopData 2 2 where
  h := fun _ => 60
  η := fun _ => 10
  ty := fun i => if i = 0 then LType.G else LType.Bd
  w := fun i => if i = 0 then 1 else 58
  t := 2
  lows := fun i => if i = 0 then {7} else {52}
  cloud := fun i => if i = 0 then {20} else {40}
  two_le_h := fun _ => by norm_num
  one_le_η := fun _ => by norm_num
  one_le_letterBlockLength := by norm_num
  card_eq := fun i => by split_ifs <;> simp
  range := fun i u hu => by
    split_ifs at hu <;> simp [mem_block] at hu <;> push_cast <;> omega
  lowG := fun i hi u hu => by
    split_ifs at hu hi
    simp [mem_block] at hu; push_cast; omega
  cloudG := fun i hi u hu => by
    split_ifs at hu hi
    simp at hu; push_cast; omega
  lowBd := fun i hi u hu => by
    split_ifs at hu hi
    simp [mem_block] at hu; push_cast; omega
  cloudBd := fun i hi u hu => by
    split_ifs at hu hi
    simp at hu; push_cast; omega
example : exData.d 0 = 0 ∧ exData.d 1 = 2 := by decide
section Ss
variable {R : Type} [Ring R]
abbrev factor {M : Type} [AddCommGroup M] [Module R M] (s : CompositionSeries (Submodule R M))
    (i : Fin s.length) : Type :=
  ↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype
def SameFactors (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] : Prop :=
  ∃ (s : CompositionSeries (Submodule R M)) (t : CompositionSeries (Submodule R N)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
      ∃ e : Fin s.length ≃ Fin t.length, ∀ i, Nonempty (factor s i ≃ₗ[R] factor t (e i))
variable {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
theorem SameFactors.refl (h : IsFiniteLength R M) : SameFactors R M M := by
  obtain ⟨s, h1, h2⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
  exact ⟨s, s, h1, h2, h1, h2, Equiv.refl _, fun _ => ⟨LinearEquiv.refl _ _⟩⟩
theorem SameFactors.symm (h : SameFactors R M N) : SameFactors R N M := by
  obtain ⟨s, t, h1, h2, h3, h4, e, he⟩ := h
  refine ⟨t, s, h3, h4, h1, h2, e.symm, fun i => ?_⟩
  obtain ⟨j, rfl⟩ := e.surjective i
  obtain ⟨f⟩ := he j
  rw [Equiv.symm_apply_apply]
  exact ⟨f.symm⟩
theorem SameFactors.trans (h : SameFactors R M N) (h' : SameFactors R N P) : SameFactors R M P := by
  obtain ⟨s, t, h1, h2, h3, h4, e, he⟩ := h
  obtain ⟨t', u, h5, h6, h7, h8, e', he'⟩ := h'
  obtain ⟨c, hc⟩ := CompositionSeries.jordan_holder t t' (h3.trans h5.symm) (h4.trans h6.symm)
  refine ⟨s, u, h1, h2, h7, h8, (e.trans c).trans e', fun i => ?_⟩
  obtain ⟨f⟩ := he i
  obtain ⟨g⟩ := he' (c (e i))
  exact ⟨(f.trans (JordanHolderLattice.Iso.linearEquiv (hc (e i)))).trans g⟩
theorem SameFactors.of_equiv (h : IsFiniteLength R M) (e : M ≃ₗ[R] N) : SameFactors R M N := by
  obtain ⟨s, h1, h2⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
  let o : Submodule R M ≃o Submodule R N := Submodule.orderIsoMapComap e
  let t : CompositionSeries (Submodule R N) :=
    { length := s.length
      toFun := fun i => o (s i)
      step := fun i => (apply_covBy_apply_iff o).mpr (s.step i) }
  refine ⟨s, t, h1, h2, ?_, ?_, Equiv.refl _, fun i => ⟨?_⟩⟩
  · change o s.head = ⊥
    rw [h1, map_bot]
  · change o s.last = ⊤
    rw [h2, map_top]
  · refine Submodule.Quotient.equiv _ _ (e.submoduleMap (s i.succ)) ?_
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨x', hx', hxx⟩ := hy
      obtain rfl : x' = x := e.injective hxx
      exact ⟨⟨x', hx'⟩, hx, rfl⟩
example [IsSimpleModule R M] [Subsingleton N] : ¬ SameFactors R M N := by
  rintro ⟨s, t, h1, h2, h3, h4, e, -⟩
  have a := Module.length_compositionSeries s h1 h2
  have b := Module.length_compositionSeries t h3 h4
  rw [Module.length_eq_one, Fin.equiv_iff_eq.mp ⟨e⟩] at a
  rw [Module.length_eq_zero] at b
  exact one_ne_zero (a.symm.trans b)
end Ss
section Rep
variable {O G : Type} [CommRing O] [Group G]
variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
def SameSS (π : Representation O G M) (π' : Representation O G M') : Prop :=
  SameFactors (MonoidAlgebra O G) π.asModule π'.asModule
def modRep (π : Representation O G M) (c : O) : Representation O G (QuotSMulTop c M) :=
  π.quotient (c • (⊤ : Submodule O M)) (fun g x hx => by
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x c ⊤).mp hx
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
@[simp] theorem modRep_mk (π : Representation O G M) (c : O) (g : G) (x : M) :
    modRep π c g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (π g x) := rfl
def piRep {ι : Type} {N : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    (π : ∀ j, Representation O G (N j)) : Representation O G (∀ j, N j) where
  toFun g := LinearMap.pi fun j => (π j g).comp (LinearMap.proj j)
  map_one' := by ext x j; simp
  map_mul' g h := by ext x j; simp
@[simp] theorem piRep_apply {ι : Type} {N : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    (π : ∀ j, Representation O G (N j)) (g : G) (x : ∀ j, N j) (j : ι) : piRep π g x j = π j g (x j) := rfl
theorem coefRep_tmul (π : Representation O G M) (X : Type) [AddCommGroup X] [Module O X] (g : G) (m : M)
    (x : X) : coefRep π X g (m ⊗ₜ[O] x) = π g m ⊗ₜ[O] x := rfl
abbrev twCoef (W : Representation O G M) (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] :
    Representation O G (M ⊗[O] X) :=
  coefRep (twistRep W χ⁻¹) X
theorem smul_tensor_eq_zero {X : Type} [AddCommGroup X] [Module O X] {c : O} (hc : ∀ x : X, c • x = 0)
    (y : M ⊗[O] X) : c • y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => rw [← tmul_smul, hc, tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]
def cycMap {c : O} (hc : ∀ m : M, c • m = 0) : M →ₗ[O] (O ⧸ Ideal.span {c}) →ₗ[O] M where
  toFun m := Submodule.liftQ (Ideal.span {c}) (LinearMap.toSpanSingleton O M m) (by
    rw [Ideal.span, Submodule.span_le]
    rintro _ rfl
    exact hc m)
  map_add' a b := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact smul_add y a b
  map_smul' a b := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact smul_comm y a b
@[simp] theorem cycMap_mk {c : O} (hc : ∀ m : M, c • m = 0) (m : M) (y : O) :
    cycMap hc m (Ideal.Quotient.mk _ y) = y • m := rfl
variable [TopologicalSpace G]
theorem cocycle_mul {π : Representation O G M} (z : ↥(Z1 π ⊤)) (g h : G) :
    (z : G → M) (g * h) = (z : G → M) g + π g ((z : G → M) h) := by
  have h1 : π g ((z : G → M) h) - (z : G → M) (g * h) + (z : G → M) g = 0 := congrFun z.2.2 (g, h)
  rw [← sub_eq_zero, ← neg_eq_zero, ← h1]; abel
theorem cocycle_one {π : Representation O G M} (z : ↥(Z1 π ⊤)) : (z : G → M) 1 = 0 := by
  have h := cocycle_mul z 1 1
  simpa using h
def extRep (π : Representation O G M) {c : O} (hc : ∀ m : M, c • m = 0) (z : ↥(Z1 π ⊤)) :
    Representation O G (M × (O ⧸ Ideal.span {c})) where
  toFun g := ((π g).coprod (cycMap hc ((z : G → M) g))).prod (LinearMap.snd O M _)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp [cocycle_one]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, y⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [cocycle_mul z g h]
    abel
def Ea (W : Representation O G M) (χ : G →* Oˣ) {X : Type} [AddCommGroup X] [Module O X] {c : O}
    (hc : ∀ x : X, c • x = 0) (z : ↥(Z1 (twCoef W χ X) ⊤)) :
    Representation O G ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) :=
  twistRep (extRep (twCoef W χ X) (smul_tensor_eq_zero hc) z) χ
section Ea
variable (W : Representation O G M) (χ : G →* Oˣ) {X : Type} [AddCommGroup X] [Module O X] {c : O}
    (hc : ∀ x : X, c • x = 0)
end Ea
def mapH1 {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M')
    (hf : ∀ g m, f (π g m) = π' g (f m)) : H1 π ⊤ →ₗ[O] H1 π' ⊤ :=
  Submodule.mapQ _ _
    ((f.compLeft G).restrict (p := Z1 π ⊤) (q := Z1 π' ⊤) (fun z hz =>
      ⟨⟨hz.1.1.comp f, fun _ => Submodule.mem_top⟩, by
        funext x
        have h1 : π x.1 (z x.2) - z (x.1 * x.2) + z x.1 = 0 := congrFun hz.2 x
        change π' x.1 (f (z x.2)) - f (z (x.1 * x.2)) + f (z x.1) = 0
        rw [← hf, ← map_sub, ← map_add, h1, map_zero]⟩))
    (by
      rintro z ⟨b, -, hb⟩
      refine ⟨f b, Submodule.mem_top, ?_⟩
      funext g
      have h1 : π g b - b = (z : G → M) g := congrFun hb g
      change π' g (f b) - f b = f ((z : G → M) g)
      rw [← h1, map_sub, hf])
def coefH1 (W : Representation O G M) (χ : G →* Oˣ) {X X' : Type} [AddCommGroup X] [Module O X]
    [AddCommGroup X'] [Module O X'] (f : X →ₗ[O] X') : H1 (twCoef W χ X) ⊤ →ₗ[O] H1 (twCoef W χ X') ⊤ :=
  mapH1 (f.lTensor M) (fun g m => by
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [coefRep_tmul]
    | add a b ha hb => simp only [map_add, ha, hb])
def unr (π : Representation O G M) (I : Subgroup G) : Submodule O (H1 π ⊤) :=
  Submodule.map (Submodule.mkQ _)
    { carrier := {z : ↥(Z1 π ⊤) | ∃ b : M, ∀ g ∈ I, (z : G → M) g = π g b - b}
      zero_mem' := ⟨0, fun g _ => by simp⟩
      add_mem' := by
        rintro a a' ⟨x, hx⟩ ⟨y, hy⟩
        refine ⟨x + y, fun g hg => ?_⟩
        simp only [Submodule.coe_add, Pi.add_apply, hx g hg, hy g hg, map_add]
        abel
      smul_mem' := by
        rintro c a ⟨x, hx⟩
        refine ⟨c • x, fun g hg => ?_⟩
        simp only [Submodule.coe_smul, Pi.smul_apply, hx g hg, map_smul, smul_sub] }
abbrev Amb (π : Representation O G M) : Type := (G → M) ⧸ B1 π ⊤
def toAmb (π : Representation O G M) : H1 π ⊤ →ₗ[O] Amb π :=
  Submodule.mapQ _ _ (Z1 π ⊤).subtype (fun _ h => h)
end Rep
section Lat
variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
def chiLL (LL : Type) [Field LL] [Algebra O LL] (χ : G →* Oˣ) : G →* LLˣ :=
  (Units.map (algebraMap O LL : O →* LL)).comp χ
@[simp] theorem chiLL_apply (χ : G →* Oˣ) (g : G) : (chiLL LL χ g : LL) = algebraMap O LL (χ g) := rfl
variable {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
def latRep (L : Lattice (O := O) ρ) : Representation O G ↥L.T where
  toFun g := actT L g
  map_one' := by ext x; simp [actT]
  map_mul' g h := by
    ext x
    change ρ (g * h) x = ρ g (ρ h x)
    simp
@[simp] theorem latRep_apply (L : Lattice (O := O) ρ) (g : G) (x : ↥L.T) : (latRep L g x : V) = ρ g x := rfl
abbrev twLattice (L : Lattice (O := O) ρ) (χ : G →* Oˣ) : Lattice (O := O) (twistRep ρ (chiLL LL χ)) where
  T := L.T
  stable := fun g x hx => by
    change algebraMap O LL (χ g) • ρ g x ∈ L.T
    rw [algebraMap_smul]
    exact L.T.smul_mem _ (L.stable g x hx)
  fg := L.fg
  free := L.free
  span := L.span
theorem latRep_twLattice (L : Lattice (O := O) ρ) (χ : G →* Oˣ) :
    latRep (twLattice L χ) = twistRep (latRep L) χ := by
  ext g x
  exact algebraMap_smul LL (χ g : O) (ρ g x)
def charLattice (hinj : Function.Injective (algebraMap O LL)) (χ : G →* Oˣ) :
    Lattice (O := O) (charRep (chiLL LL χ)) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g _ ⟨a, rfl⟩
    refine ⟨χ g * a, ?_⟩
    change algebraMap O LL (χ g * a) = algebraMap O LL (χ g) • algebraMap O LL a
    simp
  fg := by
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have h : (1 : LL) ∈ Submodule.span LL (LinearMap.range (Algebra.linearMap O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h
variable [TopologicalSpace G] [TopologicalSpace LL] {Qp : Type} [Field Qp] [Algebra Qp LL]
def charLat (Qp : Type) [Field Qp] [Algebra Qp LL] [IsTopologicalRing LL]
    (hinj : Function.Injective (algebraMap O LL)) (χ : G →* Oˣ)
    (hχ : Continuous fun g => algebraMap O LL (χ g)) : LocLat G Qp LL O where
  V := LL
  ρ := charRep (chiLL LL χ)
  cont := fun _ => hχ.mul continuous_const
  L := charLattice hinj χ
def twLat (T : LocLat G Qp LL O) (χ : G →* Oˣ) (hχ : Continuous fun g => algebraMap O LL (χ g)) :
    LocLat G Qp LL O where
  V := T.V
  ρ := twistRep T.ρ (chiLL LL χ)
  cont := fun x => by
    have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
    exact hχ.smul (T.cont x)
  L := twLattice T.L χ
def zeroLat (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp] [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL] : LocLat G Qp LL O where
  V := Fin 0 → LL
  ρ := 1
  cont := fun _ => continuous_const
  L :=
    { T := ⊥
      stable := fun _ _ hx => hx
      fg := Submodule.fg_bot
      free := inferInstance
      span := Subsingleton.elim _ _ }
def withLat (T : LocLat G Qp LL O) (L : Lattice (O := O) T.ρ) : LocLat G Qp LL O := { T with L := L }
end Lat
structure GalData (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] where
  lam : O
  T₀ : LocLat G Qp LL O
  χ₁ : G →* Oˣ
  ε : G →* Oˣ
def exGal (l : ℕ) [Fact l.Prime] : GalData ℤ_[l]ˣ ℚ_[l] ℚ_[l] ℤ_[l] where
  lam := l
  T₀ := charLat ℚ_[l] (IsFractionRing.injective ℤ_[l] ℚ_[l]) ((MonoidHom.id ℤ_[l]ˣ)⁻¹ ^ 7) (by
    change Continuous fun g : ℤ_[l]ˣ => (((g⁻¹ ^ 7 : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])
    have h1 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
    have h2 : Continuous fun g : ℤ_[l]ˣ => ((g⁻¹ ^ 7 : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (continuous_inv.pow 7)
    exact h1.comp h2)
  χ₁ := (MonoidHom.id _)⁻¹
  ε := MonoidHom.id _
namespace GalData
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)
def chi (c : ℕ) : G →* Oˣ := Γ.χ₁ * Γ.ε ^ (-((c : ℤ) - 1))
@[simp] theorem chi_one : Γ.chi 1 = Γ.χ₁ := by simp [chi]
theorem chi_succ (c : ℕ) : Γ.chi (c + 1) = Γ.chi c * Γ.ε⁻¹ := by
  rw [chi, chi, mul_assoc, ← zpow_sub_one]
  congr 2
  push_cast; ring
abbrev W₀ : Representation O G ↥Γ.T₀.L.T := latRep Γ.T₀.L
abbrev Wchi (c : ℕ) : Representation O G O := scalRep O (Γ.chi c)
def refRep (t : ℕ) :
    Representation O G (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) :=
  (modRep Γ.W₀ Γ.lam).prod (piRep fun c : Fin t => modRep (Γ.Wchi (c.val + 1)) Γ.lam)
def twist (θ : G →* Oˣ) (hθ : Continuous fun g => algebraMap O LL (θ g)) : GalData G Qp LL O where
  lam := Γ.lam
  T₀ := twLat Γ.T₀ θ hθ
  χ₁ := Γ.χ₁ * θ
  ε := Γ.ε
end GalData
example (l : ℕ) [Fact l.Prime] (g : ℤ_[l]ˣ) : (exGal l).chi 2 g = g⁻¹ * g⁻¹ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, GalData.chi_succ, GalData.chi_one]; rfl
section Per
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
def HasJumps {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ₀ : K₀ →ₐ[Qp] LL) (U : Multiset ℤ) : Prop :=
  ∀ τ : K →ₐ[Qp] LL, (∀ x : K₀, τ (algebraMap K₀ K x) = τ₀ x) → ∀ a : ℤ, multV PD ρ τ a = (U.count a : ℤ)
def CrysWith {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (U : ZMod n → Multiset ℤ) : Prop :=
  IsCrys PD ρ ∧ ∀ i, HasJumps PD ρ (emb i) (U i)
def IsCrysChar (χ : G →* Oˣ) (a : ZMod n → ℤ) : Prop :=
  (Continuous fun g => algebraMap O LL (χ g)) ∧ CrysWith PD emb (charRep (chiLL LL χ)) (fun i => {a i})
def IsTopGal {r : ℕ} (D : TopData n r) (Γ : GalData G Qp LL O) : Prop :=
  Module.finrank LL Γ.T₀.V = r ∧ CrysWith PD emb Γ.T₀.ρ D.U ∧ IsCrysChar PD emb Γ.χ₁ D.w ∧
    ∀ g, algebraMap O LL (Γ.ε g) = algebraMap Qp LL (PD.χ g)
variable (Γ : GalData G Qp LL O) (t : ℕ) (Ut : ZMod n → Multiset ℤ)
def Full (T : LocLat G Qp LL O) : Prop :=
  CrysWith PD emb T.ρ Ut ∧ ∀ L : Lattice (O := O) T.ρ, SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t)
def SumFull (μ : ℕ) (T : LocLat G Qp LL O) : Prop :=
  ∃ F : Fin μ → LocLat G Qp LL O, (∀ j, Full PD emb Γ t Ut (F j)) ∧
    ∃ e : T.V ≃ₗ[LL] (∀ j, (F j).V), ∀ g x j, e (T.ρ g x) j = (F j).ρ g (e x j)
def Admissible {M : Type} [AddCommGroup M] [Module O M] (π : Representation O G M) : Prop :=
  Finite M ∧ ∃ (μ : ℕ) (T : LocLat G Qp LL O), SumFull PD emb Γ t Ut μ T ∧
    ∃ (L₂ : Lattice (O := O) T.ρ) (p : ↥T.L.T →ₗ[O] M), L₂.T ≤ T.L.T ∧ Function.Surjective p ∧
      (∀ g x, p (latRep T.L g x) = π g (p x)) ∧ ∀ x, p x = 0 ↔ (x : T.V) ∈ L₂.T
variable {PD emb Γ t Ut}
theorem Full.withLat {T : LocLat G Qp LL O} (h : Full PD emb Γ t Ut T) (L : Lattice (O := O) T.ρ) :
    Full PD emb Γ t Ut (withLat T L) := h
variable (PD emb Γ t Ut)
variable {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M)
  (X : Type) [AddCommGroup X] [Module O X]
def admAt (a : ℕ) (ha : ∀ x : X, Γ.lam ^ a • x = 0) : Set (H1 (twCoef W Γ.χ₁ X) ⊤) :=
  {c | ∃ z : ↥(Z1 (twCoef W Γ.χ₁ X) ⊤), Submodule.Quotient.mk z = c ∧
    Admissible PD emb Γ t Ut (Ea W Γ.χ₁ ha z)}
def adm : Set (H1 (twCoef W Γ.χ₁ X) ⊤) :=
  {c | ∃ (a : ℕ) (ha : ∀ x : X, Γ.lam ^ a • x = 0), 1 ≤ a ∧ c ∈ admAt PD emb Γ t Ut W X a ha}
variable {PD emb Γ t Ut W X}
end Per
section Tens
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X]
abbrev H1tw : Type := LatticeCohomology (twLattice L χ⁻¹)
def tensCoc : ↥(latticeCocycles (twLattice L χ⁻¹)) →ₗ[O] X →ₗ[O] (G → ↥L.T ⊗[O] X) :=
  LinearMap.mk₂ O (fun c x g => (evT (twLattice L χ⁻¹) g c : ↥L.T) ⊗ₜ[O] x)
    (fun a b x => by funext g; simp [add_tmul])
    (fun a b x => by funext g; simp [smul_tmul'])
    (fun a x y => by funext g; simp [tmul_add])
    (fun a b x => by funext g; simp)
def tensAmb : H1tw L χ ⊗[O] X →ₗ[O] Amb (twCoef (latRep L) χ X) :=
  TensorProduct.lift (Submodule.liftQ _ ((tensCoc L χ X).compr₂ (Submodule.mkQ _)) (by
    rintro c ⟨b, hb, hc⟩
    refine LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).mpr
      ⟨(⟨b, hb⟩ : ↥L.T) ⊗ₜ[O] x, Submodule.mem_top, ?_⟩
    funext g
    change twistRep (latRep L) χ⁻¹ g ⟨b, hb⟩ ⊗ₜ[O] x - (⟨b, hb⟩ : ↥L.T) ⊗ₜ[O] x =
      (evT (twLattice L χ⁻¹) g c : ↥L.T) ⊗ₜ[O] x
    rw [← sub_tmul, ← latRep_twLattice]
    congr 1
    exact Subtype.ext (congrFun hc g)))
def TensIso : Prop :=
  Function.Injective (tensAmb L χ X) ∧
    LinearMap.range (tensAmb L χ X) = LinearMap.range (toAmb (twCoef (latRep L) χ X))
def finiteSelmer : Submodule O (H1 (twCoef (latRep L) χ X) ⊤) :=
  (LinearMap.range ((tensAmb L χ X).comp ((latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X))).comap
    (toAmb (twCoef (latRep L) χ X))
end Tens
section Shortcut
instance (priority := high) modTens {O M X : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup X]
    [Module O X] : Module O (M ⊗[O] X) :=
  TensorProduct.instModule
instance (priority := high) modProd {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N]
    [Module O N] : Module O (M × N) :=
  Prod.instModule
instance (priority := high) modFun {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] :
    Module O (ι → M) :=
  Pi.Function.module ι O M
instance (priority := high) modQuot {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S : Submodule O M) :
    Module O (M ⧸ S) :=
  Submodule.Quotient.module S
variable {G : Type} [Group G] [TopologicalSpace G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
instance (priority := high) twistedModuleH1 (L : Lattice (O := O) ρ) : Module O (LatticeCohomology L) :=
  Submodule.Quotient.module _
instance (priority := high) twistedSubmoduleH1 (L : Lattice (O := O) ρ) (S : Submodule O (LatticeCohomology L)) : Module O ↥S :=
  Submodule.module S
instance (priority := high) moduleH1Alt {M : Type} [AddCommGroup M] [Module O M] (π : Representation O G M) :
    Module O (H1 π ⊤) :=
  Submodule.Quotient.module _
end Shortcut
def Standing {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : Loc.FinExt l) {n : ℕ}
    (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (lam : ↥(Loc.OL LL)) : Prop :=
  5 ≤ l ∧ Loc.CaseA K LL ∧ n = Module.finrank ℚ_[l] ↥K.1 ∧ Function.Bijective emb ∧
    (∀ i, (emb (i + 1)).comp (P.PD K).σ = emb i) ∧ Irreducible lam
end GlobalTheory.AdmLoc


