-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:18.963801+00:00
-- url     : https://prove2.me/theorems/095aea74-f64f-48c6-9209-c1c260964bf2
-- title:
--   Section Arithmetic
-- statement:
--   Definitions and structural lemmas for Section Arithmetic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionArithmetic.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
def secAdd {M : LB Y} (s t : LB.Sec M) : LB.Sec M where
  f i := s.f i + t.f i
  compat i j := by rw [map_add, map_add, s.compat, t.compat, mul_add]
def secZero (M : LB Y) : LB.Sec M where
  f _ := 0
  compat _ _ := by rw [map_zero, map_zero, mul_zero]
def secCMul {M : LB Y} {V : Y.Opens} (hV : ∀ i, M.U i ≤ V) (c : Γ(Y, V)) (s : LB.Sec M) : LB.Sec M where
  f i := (Y.presheaf.map (homOfLE (hV i)).op).hom c * s.f i
  compat i j := fn_ext fun y hy => by
    have e := congrArg (gs (𝟙 Y) y (M.U i ⊓ M.U j)) (s.compat i j)
    rw [gs_res (𝟙 Y) y inf_le_left hy, gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y inf_le_right hy] at e
    rw [gs_res (𝟙 Y) y inf_le_left hy, gs_mul (𝟙 Y) y _ hy.1, gs_res (𝟙 Y) y (hV i) hy.1, e,
      gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y inf_le_right hy, gs_mul (𝟙 Y) y _ hy.2, gs_res (𝟙 Y) y (hV j) hy.2]
    ring
variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
def pullSec {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε) :=
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (Y'.presheaf.map (homOfLE (l j)).op).hom ((h.app _).hom (s.f j))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j →
          gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (l j)).op).hom ((h.app _).hom (s.f j))) =
            gs (𝟙 Y' ≫ h) y (LB.wchart L φ j) (s.f j) := fun j hj =>
        (gs_res _ y _ hj _).trans (gs_pull _ h y _ (l j hj) _)
      refine ((gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y' ≫ h) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.assoc] }
def mulSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (t : LB.Sec (LB.LinComb L φ' ε')) :
    LB.Sec (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) :=
  have l₁ : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have l₂ : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  { f := fun j => (Y.presheaf.map (homOfLE (l₁ j)).op).hom (s.f (j ∘ Sum.inl)) *
      (Y.presheaf.map (homOfLE (l₂ j)).op).hom (t.f (j ∘ Sum.inr))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : K ⊕ K' → L.ι, y ∈ LB.wchart L (Sum.elim φ φ') j →
          gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (l₁ j)).op).hom (s.f (j ∘ Sum.inl)) *
            (Y.presheaf.map (homOfLE (l₂ j)).op).hom (t.f (j ∘ Sum.inr))) =
          gs (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) *
            gs (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (t.f (j ∘ Sum.inr)) := fun j hj =>
        (gs_mul _ y _ hj _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hj _) (gs_res _ y _ hj _))
      refine ((gs_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2))) ((gs_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y) y (l₁ j hy.1) (l₁ j' hy.2), sec_trans t (𝟙 Y) y (l₂ j hy.1) (l₂ j' hy.2),
        Fintype.prod_sum_type, Units.val_mul, mul_mul_mul_comm]
      simp only [trF, Sum.elim_inl, Sum.elim_inr]
      rfl }
def powSec {I : Type} [Fintype I] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : I → LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb L (fun p : I × K => φ p.2) (fun p => ε p.2)) :=
  have l : ∀ (j : I × K → L.ι) (i : I), LB.wchart L (fun p : I × K => φ p.2) j ≤ LB.wchart L φ (fun k => j (i, k)) :=
    fun _ i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  { f := fun j => ∏ i, (Y.presheaf.map (homOfLE (l j i)).op).hom ((s i).f (fun k => j (i, k)))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.2) j →
          gs (𝟙 Y) y _ (∏ i, (Y.presheaf.map (homOfLE (l j i)).op).hom ((s i).f (fun k => j (i, k)))) =
          ∏ i, gs (𝟙 Y) y (LB.wchart L φ (fun k => j (i, k))) ((s i).f (fun k => j (i, k))) := fun j hj => by
        rw [gs_eq (𝟙 Y) y _ hj, map_prod, map_prod]
        exact Finset.prod_congr rfl fun i _ => (gs_eq (𝟙 Y) y _ hj _).symm.trans (gs_res _ y _ hj _)
      refine ((gs_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2))) ((gs_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
      have e : ∀ i, gs (𝟙 Y) y (LB.wchart L φ (fun k => j (i, k))) ((s i).f (fun k => j (i, k))) =
          (trF φ ε (𝟙 Y) y (fun k => j (i, k)) (fun k => j' (i, k))).val *
            gs (𝟙 Y) y (LB.wchart L φ (fun k => j' (i, k))) ((s i).f (fun k => j' (i, k))) :=
        fun i => sec_trans (s i) (𝟙 Y) y (l j i hy.1) (l j' i hy.2)
      rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, ← Units.coe_prod]
      congr 2
      simp only [trF]
      rw [Fintype.prod_prod_type] }
end ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic


