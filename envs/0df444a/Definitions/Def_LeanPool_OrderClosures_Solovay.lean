-- Prove2me | Definitions.Def_LeanPool_OrderClosures_Solovay
-- name    : LeanPool_OrderClosures_Solovay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:55:36.652366+00:00
-- url     : https://prove2.me/theorems/329a6af4-4959-45e3-a65d-66c4a10bbd56
-- title:
--   Solovay
-- statement:
--   Definitions and structural lemmas for Solovay, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_OrderConvergesTo_inf
public import Theorems.Thm_Positive_continuous
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
noncomputable section
namespace OrderClosures
universe u
abbrev RegularOpen (X : Type u) [TopologicalSpace X] :=
  Heyting.Regular (TopologicalSpace.Opens X)
noncomputable instance regularOpenCompleteLattice
    (X : Type u) [TopologicalSpace X] : CompleteLattice (RegularOpen X) :=
  Heyting.Regular.gi.liftCompleteLattice
noncomputable instance regularOpenCompleteBooleanAlgebra
    (X : Type u) [TopologicalSpace X] : CompleteBooleanAlgebra (RegularOpen X) where
  __ := Heyting.Regular.instBooleanAlgebra
  __ := regularOpenCompleteLattice X
def regularOpenOfClopen {X : Type u} [TopologicalSpace X]
    (s : Set X) (hs : IsClopen s) : RegularOpen X := by
  let U : TopologicalSpace.Opens X := ⟨s, hs.2⟩
  let V : TopologicalSpace.Opens X := ⟨sᶜ, hs.1.isOpen_compl⟩
  have hUV : IsCompl U V := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff]
      apply TopologicalSpace.Opens.ext
      simp [U, V]
    · rw [codisjoint_iff]
      apply TopologicalSpace.Opens.ext
      simp [U, V]
  exact ⟨U, (congrArg (fun W ↦ Wᶜ) hUV.compl_eq).trans hUV.symm.compl_eq⟩
@[simp] theorem coe_regularOpenOfClopen {X : Type u} [TopologicalSpace X]
    (s : Set X) (hs : IsClopen s) :
    (((regularOpenOfClopen s hs : RegularOpen X) :
      TopologicalSpace.Opens X) : Set X) = s := rfl
section Solovay
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]
abbrev SolovayProduct := ℕ → Gamma
def solovayA (n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f n = eta}
    ((isClopen_discrete {eta}).preimage (continuous_apply n))
def solovayCylinderSet (F : Finset ℕ) (g : SolovayProduct Gamma) :
    Set (SolovayProduct Gamma) :=
  ⋂ i ∈ F, {f | f i = g i}
omit [LinearOrder Gamma] in
/-- Shows that every finite-coordinate Solovay cylinder is clopen; this allows
it to define an element of the regular-open Boolean algebra. -/
theorem isClopen_solovayCylinderSet (F : Finset ℕ)
    (g : SolovayProduct Gamma) : IsClopen (solovayCylinderSet Gamma F g) := by
  apply isClopen_biInter_finset
  intro i hi
  exact (isClopen_discrete {g i}).preimage (continuous_apply i)
def solovayCylinder (F : Finset ℕ) (g : SolovayProduct Gamma) :
    RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen (solovayCylinderSet Gamma F g)
    (isClopen_solovayCylinderSet Gamma F g)
omit [LinearOrder Gamma] [TopologicalSpace Gamma] [DiscreteTopology Gamma] in
@[simp] theorem mem_solovayCylinderSet (F : Finset ℕ)
    (g f : SolovayProduct Gamma) :
    f ∈ solovayCylinderSet Gamma F g ↔ ∀ i ∈ F, f i = g i := by
  simp [solovayCylinderSet]
def solovayB (m n : ℕ) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f m ≤ f n}
    (by
      change IsClopen
        ((fun f : SolovayProduct Gamma ↦ (f m, f n)) ⁻¹'
          {p : Gamma × Gamma | p.1 ≤ p.2})
      exact (isClopen_discrete _).preimage
        ((continuous_apply m).prodMk (continuous_apply n)))
def solovayLT (n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f n < eta}
    ((isClopen_discrete {xi : Gamma | xi < eta}).preimage (continuous_apply n))
def solovayLE (n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f n ≤ eta}
    ((isClopen_discrete {xi : Gamma | xi ≤ eta}).preimage (continuous_apply n))
def solovayC (m n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f m < f n → f m < eta}
    (by
      change IsClopen
        ((fun f : SolovayProduct Gamma ↦ (f m, f n)) ⁻¹'
          {p : Gamma × Gamma | p.1 < p.2 → p.1 < eta})
      exact (isClopen_discrete _).preimage
        ((continuous_apply m).prodMk (continuous_apply n)))
def solovayStrict (m n : ℕ) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f m < f n}
    (by
      change IsClopen
        ((fun f : SolovayProduct Gamma ↦ (f m, f n)) ⁻¹'
          {p : Gamma × Gamma | p.1 < p.2})
      exact (isClopen_discrete _).preimage
        ((continuous_apply m).prodMk (continuous_apply n)))
def solovayNotLT (m : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | ¬ f m < eta}
    ((isClopen_discrete {xi : Gamma | ¬ xi < eta}).preimage (continuous_apply m))
def solovayBad (m n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f m < f n ∧ ¬ f m < eta}
    (by
      change IsClopen
        ((fun f : SolovayProduct Gamma ↦ (f m, f n)) ⁻¹'
          {p : Gamma × Gamma | p.1 < p.2 ∧ ¬ p.1 < eta})
      exact (isClopen_discrete _).preimage
        ((continuous_apply m).prodMk (continuous_apply n)))
def IsCompleteBooleanSubalgebra {B : Type u} [CompleteBooleanAlgebra B]
    (L : BooleanSubalgebra B) : Prop :=
  ∀ S : Set B, S ⊆ L → sSup S ∈ L
def solovayCylindersBelow (U : RegularOpen (SolovayProduct Gamma)) :
    Set (RegularOpen (SolovayProduct Gamma)) :=
  {V | ∃ F g, V = solovayCylinder Gamma F g ∧
    ((((V : RegularOpen (SolovayProduct Gamma)) :
      TopologicalSpace.Opens (SolovayProduct Gamma)) :
        Set (SolovayProduct Gamma))) ⊆
      (((U : TopologicalSpace.Opens (SolovayProduct Gamma)) :
        Set (SolovayProduct Gamma)))}
end Solovay
section BooleanStone
variable (B : Type u) [BooleanAlgebra B]
def IsBooleanStonePoint (f : B → Bool) : Prop :=
  f ⊥ = ⊥ ∧ f ⊤ = ⊤ ∧
    (∀ a b, f (a ⊓ b) = f a ⊓ f b) ∧
    (∀ a b, f (a ⊔ b) = f a ⊔ f b)
abbrev BooleanStone := {f : B → Bool // IsBooleanStonePoint B f}
theorem isClosed_isBooleanStonePoint :
    IsClosed {f : B → Bool | IsBooleanStonePoint B f} := by
  unfold IsBooleanStonePoint
  repeat' apply IsClosed.inter
  · exact isClosed_eq (continuous_apply ⊥) continuous_const
  · exact isClosed_eq (continuous_apply ⊤) continuous_const
  · change IsClosed ({f : B → Bool | ∀ a b, f (a ⊓ b) = f a ⊓ f b} :
      Set (B → Bool))
    rw [show {f : B → Bool | ∀ a b, f (a ⊓ b) = f a ⊓ f b} =
        ⋂ a, ⋂ b, {f : B → Bool | f (a ⊓ b) = f a ⊓ f b} by
      ext f
      simp]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (continuous_apply (a ⊓ b))
        (show Continuous (fun f : B → Bool ↦ f a ⊓ f b) by fun_prop)
  · change IsClosed ({f : B → Bool | ∀ a b, f (a ⊔ b) = f a ⊔ f b} :
      Set (B → Bool))
    rw [show {f : B → Bool | ∀ a b, f (a ⊔ b) = f a ⊔ f b} =
        ⋂ a, ⋂ b, {f : B → Bool | f (a ⊔ b) = f a ⊔ f b} by
      ext f
      simp]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (continuous_apply (a ⊔ b))
        (show Continuous (fun f : B → Bool ↦ f a ⊔ f b) by fun_prop)
noncomputable instance booleanStoneCompactSpace : CompactSpace (BooleanStone B) :=
  isCompact_iff_compactSpace.mp (isClosed_isBooleanStonePoint B).isCompact
instance booleanStoneT2Space : T2Space (BooleanStone B) := inferInstance
def booleanStoneClopen (b : B) : Set (BooleanStone B) :=
  {x | x.1 b = true}
theorem isClopen_booleanStoneClopen (b : B) :
    IsClopen (booleanStoneClopen B b) :=
  (isClopen_discrete {true}).preimage
    ((continuous_apply b).comp continuous_subtype_val)
def booleanStoneHom (x : BooleanStone B) : BoundedLatticeHom B Bool where
  toFun := x.1
  map_inf' := x.2.2.2.1
  map_sup' := x.2.2.2.2
  map_top' := x.2.2.1
  map_bot' := x.2.1
@[simp] theorem booleanStone_apply_bot (x : BooleanStone B) : x.1 ⊥ = false :=
  x.2.1
@[simp] theorem booleanStone_apply_top (x : BooleanStone B) : x.1 ⊤ = true :=
  x.2.2.1
@[simp] theorem booleanStone_apply_inf (x : BooleanStone B) (a b : B) :
    x.1 (a ⊓ b) = x.1 a ⊓ x.1 b := x.2.2.2.1 a b
@[simp] theorem booleanStone_apply_sup (x : BooleanStone B) (a b : B) :
    x.1 (a ⊔ b) = x.1 a ⊔ x.1 b := x.2.2.2.2 a b
@[simp] theorem booleanStone_apply_compl (x : BooleanStone B) (a : B) :
    x.1 aᶜ = (x.1 a)ᶜ := by
  exact map_compl' (booleanStoneHom B x) a
noncomputable def booleanStonePointOfPrime (J : Order.Ideal B)
    (hJ : Order.Ideal.IsPrime J) : BooleanStone B := by
  classical
  exact ⟨fun b ↦ decide (b ∉ J), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [J.bot_mem]
    · simp [hJ.toIsProper.top_notMem]
    · intro a b
      by_cases ha : a ∈ J
      · have hab : a ⊓ b ∈ J := J.lower inf_le_left ha
        simp [ha, hab]
      · by_cases hb : b ∈ J
        · have hab : a ⊓ b ∈ J := J.lower inf_le_right hb
          simp [ha, hb, hab]
        · have hab : a ⊓ b ∉ J := fun h ↦ (hJ.mem_or_mem h).elim ha hb
          simp [ha, hb, hab]
    · intro a b
      by_cases ha : a ∈ J
      · by_cases hb : b ∈ J
        · have hab : a ⊔ b ∈ J := J.sup_mem ha hb
          simp [ha, hb, hab]
        · have hab : a ⊔ b ∉ J := by
            simp [Order.Ideal.sup_mem_iff, ha, hb]
          simp [ha, hb, hab]
      · have hab : a ⊔ b ∉ J := by
          simp [Order.Ideal.sup_mem_iff, ha]
        simp [ha, hab]⟩
theorem exists_booleanStonePoint_of_not_le {a b : B} (hab : ¬ a ≤ b) :
    ∃ x : BooleanStone B, x.1 a = true ∧ x.1 b = false := by
  let F : Order.PFilter B := Order.PFilter.principal a
  let I : Order.Ideal B := Order.Ideal.principal b
  have hFI : Disjoint (F : Set B) (I : Set B) := by
    rw [Set.disjoint_left]
    intro c hcF hcI
    exact hab ((Order.PFilter.mem_principal.mp hcF).trans
      (Order.Ideal.mem_principal.mp hcI))
  rcases DistribLattice.prime_ideal_of_disjoint_filter_ideal hFI with
    ⟨J, hJ, hIJ, hFJ⟩
  have hbJ : b ∈ J := hIJ Order.Ideal.mem_principal_self
  have haJ : a ∉ J := by
    intro haJ
    exact Set.disjoint_left.mp hFJ (Order.PFilter.mem_principal.mpr le_rfl) haJ
  refine ⟨booleanStonePointOfPrime B J hJ, ?_, ?_⟩
  · simp [booleanStonePointOfPrime, haJ]
  · simp [booleanStonePointOfPrime, hbJ]
theorem booleanStoneClopen_subset_iff {a b : B} :
    booleanStoneClopen B a ⊆ booleanStoneClopen B b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    rcases exists_booleanStonePoint_of_not_le B hab with ⟨x, hxa, hxb⟩
    exact Bool.false_ne_true (hxb.symm.trans (h hxa))
  · intro hab x hxa
    change x.1 b = true
    have hmap : x.1 a ≤ x.1 b :=
      OrderHomClass.monotone (booleanStoneHom B x) hab
    rw [hxa] at hmap
    exact top_unique hmap
@[simp] theorem booleanStoneClopen_top :
    booleanStoneClopen B ⊤ = Set.univ := by
  ext x
  simp [booleanStoneClopen]
@[simp] theorem booleanStoneClopen_inf (a b : B) :
    booleanStoneClopen B (a ⊓ b) =
      booleanStoneClopen B a ∩ booleanStoneClopen B b := by
  ext x
  simp [booleanStoneClopen]
@[simp] theorem booleanStoneClopen_compl (a : B) :
    booleanStoneClopen B aᶜ = (booleanStoneClopen B a)ᶜ := by
  ext x
  simp [booleanStoneClopen]
def booleanStoneSignedCoordinate (x : BooleanStone B) (b : B) : B :=
  if x.1 b = true then b else bᶜ
theorem booleanStoneClopen_signedCoordinate (x : BooleanStone B) (b : B) :
    booleanStoneClopen B (booleanStoneSignedCoordinate B x b) =
      {y | y.1 b = x.1 b} := by
  ext y
  by_cases hx : x.1 b = true
  · simp [booleanStoneSignedCoordinate, hx, booleanStoneClopen]
  · simp [booleanStoneSignedCoordinate, hx, booleanStoneClopen]
def booleanStoneCylinderElement (F : Finset B) (x : BooleanStone B) : B :=
  F.inf (booleanStoneSignedCoordinate B x)
theorem booleanStoneClopen_cylinderElement (F : Finset B)
    (x : BooleanStone B) :
    booleanStoneClopen B (booleanStoneCylinderElement B F x) =
      {y | ∀ b ∈ F, y.1 b = x.1 b} := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [booleanStoneCylinderElement]
  | @insert b F hb ih =>
      unfold booleanStoneCylinderElement
      change booleanStoneClopen B (F.inf (booleanStoneSignedCoordinate B x)) =
        {y | ∀ b ∈ F, y.1 b = x.1 b} at ih
      rw [Finset.inf_insert, booleanStoneClopen_inf,
        booleanStoneClopen_signedCoordinate, ih]
      ext y
      simp
theorem booleanStone_clopen_basis {U : Set (BooleanStone B)}
    (hU : IsOpen U) {x : BooleanStone B} (hxU : x ∈ U) :
    ∃ b : B, x ∈ booleanStoneClopen B b ∧ booleanStoneClopen B b ⊆ U := by
  rcases isOpen_induced_iff.mp hU with ⟨V, hV, hVU⟩
  have hxV : x.1 ∈ V := by
    have : x ∈ Subtype.val ⁻¹' V := by simpa [hVU] using hxU
    exact this
  rcases isOpen_pi_iff.mp hV x.1 hxV with ⟨F, v, hv, hvV⟩
  refine ⟨booleanStoneCylinderElement B F x, ?_, ?_⟩
  · rw [booleanStoneClopen_cylinderElement]
    exact fun _ _ ↦ rfl
  · intro y hy
    have hycoord : ∀ b ∈ F, y.1 b = x.1 b := by
      rwa [booleanStoneClopen_cylinderElement] at hy
    have hyV : y.1 ∈ V := by
      apply hvV
      intro b hb
      rw [hycoord b (Finset.mem_coe.mp hb)]
      exact (hv b (Finset.mem_coe.mp hb)).2
    have : y ∈ Subtype.val ⁻¹' V := hyV
    rwa [hVU] at this
end BooleanStone
section CompleteBooleanStone
variable (B : Type u) [CompleteBooleanAlgebra B]
noncomputable instance booleanStoneExtremallyDisconnected :
    ExtremallyDisconnected (BooleanStone B) where
  open_closure U hU := by
    let S : Set B := {b | booleanStoneClopen B b ⊆ U}
    let c : B := sSup S
    have hUc : U ⊆ booleanStoneClopen B c := by
      intro x hxU
      rcases booleanStone_clopen_basis B hU hxU with ⟨b, hxb, hbU⟩
      have hbS : b ∈ S := hbU
      exact (booleanStoneClopen_subset_iff B).mpr (le_sSup hbS) hxb
    have hclosure_le : closure U ⊆ booleanStoneClopen B c :=
      closure_minimal hUc (isClopen_booleanStoneClopen B c).1
    have hc_le : booleanStoneClopen B c ⊆ closure U := by
      intro x hxc
      by_contra hxclosure
      have hxopen : x ∈ (closure U)ᶜ := hxclosure
      rcases booleanStone_clopen_basis B (isOpen_compl_iff.mpr isClosed_closure)
          hxopen with ⟨d, hxd, hd⟩
      have hcd : c ≤ dᶜ := by
        apply sSup_le
        intro b hbS
        apply (booleanStoneClopen_subset_iff B).mp
        intro y hyb
        rw [booleanStoneClopen_compl]
        intro hyd
        have hyU : y ∈ U := hbS hyb
        have hyclosure : y ∈ closure U := subset_closure hyU
        exact (hd hyd) hyclosure
      have hxccompl : x ∈ booleanStoneClopen B dᶜ :=
        (booleanStoneClopen_subset_iff B).mpr hcd hxc
      rw [booleanStoneClopen_compl] at hxccompl
      exact hxccompl hxd
    rw [Set.Subset.antisymm hclosure_le hc_le]
    exact (isClopen_booleanStoneClopen B c).2
end CompleteBooleanStone
section OrderCompleteCofK
variable (K : Type u) [TopologicalSpace K] [ExtremallyDisconnected K]
def continuousFamilyLevelOpen (A : Set C(K, ℝ)) (q : ℚ) : Set K :=
  ⋃ f ∈ A, f ⁻¹' Set.Ioi (q : ℝ)
omit [ExtremallyDisconnected K] in
/-- Shows that a rational strict upper-level set of a continuous family is
open; used to regularize level sets in the supremum construction. -/
theorem isOpen_continuousFamilyLevelOpen (A : Set C(K, ℝ)) (q : ℚ) :
    IsOpen (continuousFamilyLevelOpen K A q) := by
  apply isOpen_iUnion
  intro f
  apply isOpen_iUnion
  intro hf
  exact isOpen_Ioi.preimage f.continuous
def continuousFamilyRegularizedLevel (A : Set C(K, ℝ)) (q : ℚ) : Set K :=
  closure (continuousFamilyLevelOpen K A q)
theorem isClopen_continuousFamilyRegularizedLevel
    (A : Set C(K, ℝ)) (q : ℚ) :
    IsClopen (continuousFamilyRegularizedLevel K A q) :=
  ⟨isClosed_closure, ExtremallyDisconnected.open_closure _
    (isOpen_continuousFamilyLevelOpen K A q)⟩
def continuousFamilyCutValues (A : Set C(K, ℝ)) (x : K) : Set ℝ :=
  ((fun q : ℚ ↦ (q : ℝ)) ''
    {q | x ∈ continuousFamilyRegularizedLevel K A q})
noncomputable def continuousFamilySupValue (A : Set C(K, ℝ)) (x : K) : ℝ :=
  sSup (continuousFamilyCutValues K A x)
omit [ExtremallyDisconnected K] in
/-- Shows that regularized upper-level sets decrease with the threshold; used
to prove consistency of the cut-value construction. -/
theorem continuousFamilyRegularizedLevel_antitone (A : Set C(K, ℝ)) :
    Antitone (continuousFamilyRegularizedLevel K A) := by
  intro q r hqr
  apply closure_mono
  intro x hx
  simp only [continuousFamilyLevelOpen, Set.mem_iUnion, Set.mem_preimage,
    Set.mem_Ioi] at hx ⊢
  rcases hx with ⟨f, hfA, hrfx⟩
  exact ⟨f, hfA, (Rat.cast_le.mpr hqr).trans_lt hrfx⟩
omit [ExtremallyDisconnected K] in
/-- Supplies rational cut values at each point for a nonempty family; needed
to define the pointwise cut supremum. -/
theorem continuousFamilyCutValues_nonempty {A : Set C(K, ℝ)}
    (hA : A.Nonempty) (x : K) : (continuousFamilyCutValues K A x).Nonempty := by
  rcases hA with ⟨f, hfA⟩
  rcases exists_rat_lt (f x) with ⟨q, hq⟩
  refine ⟨(q : ℝ), ⟨q, ?_, rfl⟩⟩
  apply subset_closure
  simp only [continuousFamilyLevelOpen, Set.mem_iUnion, Set.mem_preimage,
    Set.mem_Ioi]
  exact ⟨f, hfA, hq⟩
omit [ExtremallyDisconnected K] in
/-- Bounds the rational cut values using a common upper bound of the family;
used to make their real supremum well-defined. -/
theorem continuousFamilyCutValues_bddAbove {A : Set C(K, ℝ)}
    {h : C(K, ℝ)} (hh : h ∈ upperBounds A) (x : K) :
    BddAbove (continuousFamilyCutValues K A x) := by
  refine ⟨h x, ?_⟩
  rintro r ⟨q, hxq, rfl⟩
  have hopen_le : continuousFamilyLevelOpen K A q ⊆
      h ⁻¹' Set.Ici (q : ℝ) := by
    intro y hy
    simp only [continuousFamilyLevelOpen, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_Ioi] at hy
    rcases hy with ⟨f, hfA, hqf⟩
    exact le_of_lt (hqf.trans_le (hh hfA y))
  have hclosed : IsClosed (h ⁻¹' Set.Ici (q : ℝ)) :=
    isClosed_Ici.preimage h.continuous
  exact (closure_minimal hopen_le hclosed hxq)
theorem continuous_continuousFamilySupValue {A : Set C(K, ℝ)}
    (hA : A.Nonempty) (hAbdd : BddAbove A) :
    Continuous (continuousFamilySupValue K A) := by
  rcases hAbdd with ⟨h, hh⟩
  apply continuous_iff_lower_upperSemicontinuous.mpr
  constructor
  · rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro a
    rw [show continuousFamilySupValue K A ⁻¹' Set.Ioi a =
        ⋃ q : ℚ, ⋃ (_ : a < (q : ℝ)),
          continuousFamilyRegularizedLevel K A q by
      ext x
      constructor
      · intro hx
        have hbdd := continuousFamilyCutValues_bddAbove K hh x
        have hne := continuousFamilyCutValues_nonempty K hA x
        rcases (lt_csSup_iff hbdd hne).mp hx with ⟨r, hr, har⟩
        rcases hr with ⟨q, hxq, rfl⟩
        simp only [Set.mem_iUnion]
        exact ⟨q, har, hxq⟩
      · simp only [Set.mem_iUnion]
        rintro ⟨q, haq, hxq⟩
        exact haq.trans_le (le_csSup
          (continuousFamilyCutValues_bddAbove K hh x) ⟨q, hxq, rfl⟩)]
    apply isOpen_iUnion
    intro q
    apply isOpen_iUnion
    intro haq
    exact (isClopen_continuousFamilyRegularizedLevel K A q).2
  · rw [upperSemicontinuous_iff_isOpen_preimage]
    intro a
    rw [show continuousFamilySupValue K A ⁻¹' Set.Iio a =
        ⋃ q : ℚ, ⋃ (_ : (q : ℝ) < a),
          (continuousFamilyRegularizedLevel K A q)ᶜ by
      ext x
      constructor
      · intro hx
        change continuousFamilySupValue K A x < a at hx
        rcases exists_rat_btwn hx with ⟨q, hgq, hqa⟩
        simp only [Set.mem_iUnion, Set.mem_compl_iff]
        refine ⟨q, hqa, ?_⟩
        intro hxq
        have hqg : (q : ℝ) ≤ continuousFamilySupValue K A x :=
          le_csSup (continuousFamilyCutValues_bddAbove K hh x)
            ⟨q, hxq, rfl⟩
        exact (not_le_of_gt hgq) hqg
      · simp only [Set.mem_iUnion, Set.mem_compl_iff]
        rintro ⟨q, hqa, hxq⟩
        have hgq : continuousFamilySupValue K A x ≤ (q : ℝ) := by
          apply csSup_le (continuousFamilyCutValues_nonempty K hA x)
          rintro r ⟨q', hxq', rfl⟩
          by_contra hq'q
          have hqq' : q < q' := Rat.cast_lt.mp (lt_of_not_ge hq'q)
          exact hxq (continuousFamilyRegularizedLevel_antitone K A
            (le_of_lt hqq') hxq')
        exact hgq.trans_lt hqa]
    apply isOpen_iUnion
    intro q
    apply isOpen_iUnion
    intro hqa
    exact (isClopen_continuousFamilyRegularizedLevel K A q).1.isOpen_compl
noncomputable def continuousFamilySup (A : Set C(K, ℝ))
    (hA : A.Nonempty) (hAbdd : BddAbove A) : C(K, ℝ) :=
  ⟨continuousFamilySupValue K A,
    continuous_continuousFamilySupValue K hA hAbdd⟩
end OrderCompleteCofK
section ClopenIndicators
variable (K : Type u) [TopologicalSpace K]
noncomputable def clopenIndicator (s : Set K) (hs : IsClopen s) : C(K, ℝ) where
  toFun := s.indicator 1
  continuous_toFun :=
    continuous_indicator (by simp [hs]) continuous_const.continuousOn
@[simp] theorem clopenIndicator_apply_mem (s : Set K) (hs : IsClopen s)
    {x : K} (hx : x ∈ s) : clopenIndicator K s hs x = 1 := by
  simp [clopenIndicator, hx]
@[simp] theorem clopenIndicator_apply_notMem (s : Set K) (hs : IsClopen s)
    {x : K} (hx : x ∉ s) : clopenIndicator K s hs x = 0 := by
  simp [clopenIndicator, hx]
@[simp] theorem clopenIndicator_empty :
    clopenIndicator K ∅ isClopen_empty = 0 := by
  ext x
  simp [clopenIndicator]
end ClopenIndicators
section BooleanStoneIndicators
variable (B : Type u) [CompleteBooleanAlgebra B]
noncomputable def booleanStoneIndicator (b : B) : C(BooleanStone B, ℝ) :=
  clopenIndicator (BooleanStone B) (booleanStoneClopen B b)
    (isClopen_booleanStoneClopen B b)
@[simp] theorem booleanStoneIndicator_apply (b : B) (x : BooleanStone B) :
    booleanStoneIndicator B b x = if x.1 b = true then 1 else 0 := by
  by_cases hxb : x.1 b = true
  · simp [booleanStoneIndicator, booleanStoneClopen, hxb]
  · simp [booleanStoneIndicator, booleanStoneClopen, hxb]
@[simp] theorem booleanStoneIndicator_bot : booleanStoneIndicator B ⊥ = 0 := by
  ext x
  simp [booleanStoneIndicator_apply]
@[simp] theorem booleanStoneIndicator_inf (a b : B) :
    booleanStoneIndicator B (a ⊓ b) =
      booleanStoneIndicator B a ⊓ booleanStoneIndicator B b := by
  ext x
  by_cases ha : x.1 a = true <;> by_cases hb : x.1 b = true <;>
    simp [booleanStoneIndicator_apply, ha, hb]
@[simp] theorem booleanStoneIndicator_sup (a b : B) :
    booleanStoneIndicator B (a ⊔ b) =
      booleanStoneIndicator B a ⊔ booleanStoneIndicator B b := by
  ext x
  by_cases ha : x.1 a = true <;> by_cases hb : x.1 b = true <;>
    simp [booleanStoneIndicator_apply, ha, hb]
@[simp] theorem booleanStoneIndicator_compl (a : B) :
    booleanStoneIndicator B aᶜ = 1 - booleanStoneIndicator B a := by
  ext x
  by_cases ha : x.1 a = true <;> simp [booleanStoneIndicator_apply, ha]
noncomputable def booleanSubalgebraInVectorSublattice
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z) : BooleanSubalgebra B where
  carrier := {b | booleanStoneIndicator B b ∈ Z}
  supClosed' := by
    intro a ha b hb
    change booleanStoneIndicator B a ∈ Z at ha
    change booleanStoneIndicator B b ∈ Z at hb
    change booleanStoneIndicator B (a ⊔ b) ∈ Z
    rw [booleanStoneIndicator_sup]
    exact Z.sup_mem ha hb
  infClosed' := by
    intro a ha b hb
    change booleanStoneIndicator B a ∈ Z at ha
    change booleanStoneIndicator B b ∈ Z at hb
    change booleanStoneIndicator B (a ⊓ b) ∈ Z
    rw [booleanStoneIndicator_inf]
    exact Z.inf_mem ha hb
  compl_mem' := by
    intro a ha
    change booleanStoneIndicator B a ∈ Z at ha
    change booleanStoneIndicator B aᶜ ∈ Z
    rw [booleanStoneIndicator_compl]
    exact Z.sub_mem hOne ha
  bot_mem' := by
    change booleanStoneIndicator B ⊥ ∈ Z
    rw [booleanStoneIndicator_bot]
    exact Z.zero_mem
end BooleanStoneIndicators
end OrderClosures
namespace OrderClosures
universe u v
section ClosedOrderSublattices
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
end ClosedOrderSublattices
section BooleanIndicatorsGenerate
variable (B : Type u) [CompleteBooleanAlgebra B]
end BooleanIndicatorsGenerate
section DensityCharacter
end DensityCharacter
section SolovayVectorSublattice
variable (Gamma : Type u) [LinearOrder Gamma] [WellFoundedLT Gamma]
  [TopologicalSpace Gamma] [DiscreteTopology Gamma]
noncomputable def solovayVectorGenerators :
    Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ) :=
  Set.range (fun p : ℕ × ℕ ↦
    booleanStoneIndicator (RegularOpen (SolovayProduct Gamma))
      (solovayB Gamma p.1 p.2)) ∪ {1}
noncomputable def solovayVectorSublattice :
    VectorSublattice C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ) :=
  VectorSublattice.topologicalClosure
    (VectorSublattice.generated (solovayVectorGenerators Gamma))
end SolovayVectorSublattice
end OrderClosures


