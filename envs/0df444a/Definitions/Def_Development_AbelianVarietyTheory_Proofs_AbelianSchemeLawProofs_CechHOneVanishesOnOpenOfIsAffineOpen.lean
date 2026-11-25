-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:23:41.872835+00:00
-- url     : https://prove2.me/theorems/df2ab358-eb4d-4d11-8567-92ff5ca0a401
-- title:
--   Cech HOne Vanishes On Open Of Is Affine Open
-- statement:
--   Definitions and structural lemmas for Cech HOne Vanishes On Open Of Is Affine Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_existsUnique_glue
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_ext_of_cover
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_existsUnique_glue
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_ext_of_cover
import Theorems.Thm_GlobalTheory_AbLaw_cechLB_d
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
def IsCocycle (M : LB X) {I : Type} (O : I → X.Opens) (φ : ∀ a b, SecOn M (O a ⊓ O b)) : Prop :=
  ∀ a b d (W : X.Opens) (ha : W ≤ O a) (hb : W ≤ O b) (hd : W ≤ O d),
    restrict M (le_inf ha hb) (φ a b) + restrict M (le_inf hb hd) (φ b d) =
      restrict M (le_inf ha hd) (φ a d)
def IsCoboundary (M : LB X) {I : Type} (O : I → X.Opens) (φ : ∀ a b, SecOn M (O a ⊓ O b)) : Prop :=
  ∃ ψ : ∀ a, SecOn M (O a), ∀ a b,
    φ a b = restrict M inf_le_left (ψ a) - restrict M inf_le_right (ψ b)
def CechHOneVanishesOnOpen (M : LB X) (V : X.Opens) : Prop :=
  ∀ (I : Type) (O : I → X.Opens), (∀ a, O a ≤ V) → V ≤ ⨆ a, O a →
    ∀ φ : ∀ a b, SecOn M (O a ⊓ O b), IsCocycle M O φ → IsCoboundary M O φ
variable {M : LB X}
theorem exists_pair {κ : Type} [LinearOrder κ] {t : Finset κ} (ht : t.card = 2) :
    ∃ i j, i < j ∧ t = {i, j} := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 ht
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, rfl⟩
  · exact ⟨j, i, h, Finset.pair_comm _ _⟩
section Cube
variable {κ : Type} (D : κ → X.Opens)
theorem le_single {W : X.Opens} {i : κ} (hi : W ≤ D i) : W ≤ ⨅ l ∈ ({i} : Finset κ), D l := by
  simpa using hi
theorem le_of_mem {s : Finset κ} {i : κ} (hi : i ∈ s) : ⨅ l ∈ s, D l ≤ D i := biInf_le _ hi
variable [LinearOrder κ]
theorem le_pair {W : X.Opens} {i j : κ} (hi : W ≤ D i) (hj : W ≤ D j) :
    W ≤ ⨅ l ∈ ({i, j} : Finset κ), D l := by
  simp [hi, hj]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M)
def comp {p : ℕ} (x : GlobalTheory.Cube.Term (secCube f M D) p) (s : Finset κ) (hs : s.card = p) :
    SecOn M (⨅ l ∈ s, D l) := x ⟨s, hs⟩
variable {D f M}
theorem restrict_d_one (x : GlobalTheory.Cube.Term (secCube f M D) 1) {i j : κ} (h : i < j) {W : X.Opens}
    (hi : W ≤ D i) (hj : W ≤ D j) :
    restrict M (le_pair D hi hj) (comp M D f (GlobalTheory.Cube.d _ 1 x) {i, j} (Finset.card_pair h.ne)) =
      restrict M (le_single D hj) (comp M D f x {j} (Finset.card_singleton j)) -
        restrict M (le_single D hi) (comp M D f x {i} (Finset.card_singleton i)) := by
  have e : comp M D f (GlobalTheory.Cube.d _ 1 x) {i, j} (Finset.card_pair h.ne) =
      restrict M (iInf_le_iInf_of_subset D (by simp)) (comp M D f x {j} (Finset.card_singleton j)) -
      restrict M (iInf_le_iInf_of_subset D (by simp)) (comp M D f x {i} (Finset.card_singleton i)) :=
    GlobalTheory.Cube.d_one_apply_pair _ x h
  rw [e, map_sub, restrict_restrict, restrict_restrict]
end Cube
section Main
variable {κ : Type} [LinearOrder κ] (f : X ⟶ Spec (CommRingCat.of R)) (M) (D : κ → X.Opens)
def toCech {V : X.Opens} (hD : ∀ i, D i ≤ V) : SecOnR f M V →ₗ[R] (cechLB f M D).X 0 :=
  LinearMap.pi fun s : {s : Finset κ // s.card = 0 + 1} => SecOnR.restrict f M (by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (s.2.symm ▸ Nat.succ_pos 0 : 0 < s.1.card)
    exact (le_of_mem D hi).trans (hD i))
variable {D}
theorem toCech_injective {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i) :
    Function.Injective (toCech M f D hD) := by
  intro x y h
  refine SecOnR.ext_of_cover f D hD hc fun i => ?_
  have e := congrArg (SecOnR.restrict f M (le_single D (le_rfl : D i ≤ D i)))
    (congrFun h ⟨{i}, Finset.card_singleton i⟩)
  have hi := (le_of_mem D (Finset.mem_singleton_self i)).trans (hD i)
  exact (SecOnR.restrict_restrict f hi _ x).symm.trans (e.trans (SecOnR.restrict_restrict f hi _ y))
theorem exact_toCech {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i) :
    Function.Exact (toCech M f D hD) ((cechLB f M D).d 0 1).hom := by
  have hd : ∀ x, ((cechLB f M D).d 0 1).hom x = GlobalTheory.Cube.d (secCube f M D) 1 x := fun x =>
    congrArg (fun q => q.hom x) (cechLB_d f M D 0)
  intro x
  rw [hd]
  constructor
  · intro hx
    have hlt : ∀ i j, i < j → ∀ (W : X.Opens) (hi : W ≤ D i) (hj : W ≤ D j),
        restrict M (le_single D hj) (comp M D f x {j} (Finset.card_singleton j)) =
          restrict M (le_single D hi) (comp M D f x {i} (Finset.card_singleton i)) := by
      intro i j hij W hi hj
      have e := restrict_d_one x hij hi hj
      rw [hx] at e
      exact sub_eq_zero.1 ((map_zero (restrict M _)).symm.trans e).symm
    obtain ⟨t, ht, -⟩ := existsUnique_glue D hD hc
      (fun i => restrict M (le_single D le_rfl) (comp M D f x {i} (Finset.card_singleton i)))
      fun i j => by
        rw [restrict_restrict, restrict_restrict]
        rcases lt_trichotomy i j with hij | rfl | hij
        · exact (hlt i j hij _ inf_le_left inf_le_right).symm
        · rfl
        · exact hlt j i hij _ inf_le_right inf_le_left
    refine ⟨SecOnR.of f M V t, ?_⟩
    funext ⟨s, hs⟩
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    have e := congrArg (restrict M (le_of_mem D (Finset.mem_singleton_self i))) (ht i)
    rw [restrict_restrict, restrict_restrict, restrict_self] at e
    exact e
  · rintro ⟨t, rfl⟩
    funext ⟨s, hs⟩
    obtain ⟨i, j, hij, rfl⟩ := exists_pair hs
    have e := restrict_d_one (toCech M f D hD t) hij (W := ⨅ l ∈ ({i, j} : Finset κ), D l)
      (le_of_mem D (by simp)) (le_of_mem D (by simp))
    rw [restrict_self] at e
    exact e.trans (sub_eq_zero.2
      ((restrict_restrict ((le_of_mem D (Finset.mem_singleton_self j)).trans (hD j)) _ _).trans
        (restrict_restrict ((le_of_mem D (Finset.mem_singleton_self i)).trans (hD i)) _ _).symm))
def kerEquiv {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i) :
    SecOnR f M V ≃ₗ[R] LinearMap.ker ((cechLB f M D).d 0 1).hom :=
  LinearEquiv.ofInjective _ (toCech_injective M f hD hc) ≪≫ₗ
    LinearEquiv.ofEq _ _ (exact_toCech M f hD hc).linearMap_ker_eq.symm
def secKerEquiv (hc : ⨆ i, D i = ⊤) :
    LB.Sec M ≃+ LinearMap.ker ((cechLB f M D).d 0 1).hom :=
  (SecOnR.topEquiv f M).symm.toAddEquiv.trans (kerEquiv M f (fun _ => le_top) hc.ge).toAddEquiv
variable {M}
end Main
end GlobalTheory.AbLaw.CechOne


