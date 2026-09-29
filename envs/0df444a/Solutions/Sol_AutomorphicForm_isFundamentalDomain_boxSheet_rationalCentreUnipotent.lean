-- Prove2me | solution 1 for AutomorphicForm.isFundamentalDomain_boxSheet_rationalCentreUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5857e9c9-1723-5140-ad89-3d2926d1b583

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent.AutomorphicForm"
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalCentre rationalCentreUnipotent rationalCentreUnipotentHaar adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add unipotentGL2Hom AdelicGL2 globalPoints globalPoints_apply"
p2m_open "AutomorphicForm"

namespace BoxSheetZN

variable (K : Type) [Field K] [NumberField K]

theorem countable_numberField : Countable K := by
  have e := (Module.finBasis ℚ K).equivFun.toEquiv
  exact e.symm.countable_iff.mp inferInstance

def ratCentralHom : Kˣ →* AdelicGL2 (𝓞 K) K :=
  (globalPoints (𝓞 K) K).comp (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)

theorem ratCentralHom_apply_entry (a : Kˣ) (i j : Fin 2) :
    ((ratCentralHom K a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then algebraMap K (AdeleRing (𝓞 K) K) a else 0 := by
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem ratCentralHom_comm (a : Kˣ) (g : AdelicGL2 (𝓞 K) K) : ratCentralHom K a * g = g * ratCentralHom K a := by
  refine Units.ext ?_
  change (Matrix.scalar (Fin 2) ((a : Kˣ) : K)).map (algebraMap K (AdeleRing (𝓞 K) K)) *
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * (Matrix.scalar (Fin 2) ((a : Kˣ) : K)).map (algebraMap K (AdeleRing (𝓞 K) K))
  have : (Matrix.scalar (Fin 2) ((a : Kˣ) : K)).map (algebraMap K (AdeleRing (𝓞 K) K)) =
      Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) a) := by
    ext i j
    rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [this]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem unipotentGL2_inv (y : AdeleRing (𝓞 K) K) : (unipotentGL2 y : AdelicGL2 (𝓞 K) K)⁻¹ = unipotentGL2 (-y) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem exists_eq (h : AdelicGL2 (𝓞 K) K) (hh : h ∈ rationalCentreUnipotent K) :
    ∃ (a : Kˣ) (y : AdeleRing (𝓞 K) K), h = ratCentralHom K a * unipotentGL2 y := by
  rw [rationalCentreUnipotent, Subgroup.sup_eq_closure] at hh
  refine Subgroup.closure_induction (p := fun g _ => ∃ (a : Kˣ) (y : AdeleRing (𝓞 K) K), g = ratCentralHom K a * unipotentGL2 y)
    ?_ ?_ ?_ ?_ hh
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨a, 0, by rw [unipotentGL2_zero, mul_one]; rfl⟩
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨1, Multiplicative.toAdd y, by rw [map_one, one_mul]; rfl⟩
  · exact ⟨1, 0, by rw [map_one, unipotentGL2_zero, mul_one]⟩
  · rintro g g' _ _ ⟨a, y, rfl⟩ ⟨a', y', rfl⟩
    refine ⟨a * a', y + y', ?_⟩
    rw [map_mul, unipotentGL2_add, mul_assoc, ← mul_assoc (unipotentGL2 y), ← ratCentralHom_comm, mul_assoc, mul_assoc]
  · rintro g _ ⟨a, y, rfl⟩
    refine ⟨a⁻¹, -y, ?_⟩
    rw [mul_inv_rev, unipotentGL2_inv, ← map_inv, (ratCentralHom_comm K a⁻¹ (unipotentGL2 (-y))).symm]

theorem exists_eq_rational (h : AdelicGL2 (𝓞 K) K)
    (hh : h ∈ rationalCentre K ⊔ ((globalPoints (𝓞 K) K).comp (unipotentGL2Hom (R := K))).range) :
    ∃ (a : Kˣ) (β : K), h = ratCentralHom K a * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  rw [Subgroup.sup_eq_closure] at hh
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ (a : Kˣ) (β : K), g = ratCentralHom K a * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β))
    ?_ ?_ ?_ ?_ hh
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨a, 0, by rw [map_zero, unipotentGL2_zero, mul_one]; rfl⟩
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
      refine ⟨1, Multiplicative.toAdd y, ?_⟩
      rw [map_one, one_mul, MonoidHom.comp_apply, ← globalPoints_unipotentGL2]
      rfl
  · exact ⟨1, 0, by rw [map_one, map_zero, unipotentGL2_zero, mul_one]⟩
  · rintro g g' _ _ ⟨a, y, rfl⟩ ⟨a', y', rfl⟩
    refine ⟨a * a', y + y', ?_⟩
    rw [map_mul, map_add, unipotentGL2_add, mul_assoc, ← mul_assoc (unipotentGL2 _), ← ratCentralHom_comm, mul_assoc,
      mul_assoc]
  · rintro g _ ⟨a, y, rfl⟩
    refine ⟨a⁻¹, -y, ?_⟩
    rw [mul_inv_rev, unipotentGL2_inv, ← map_inv, map_neg, (ratCentralHom_comm K a⁻¹ (unipotentGL2 _)).symm]

theorem sheet_entries (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    (((ratCentralHom K a * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
        algebraMap K (AdeleRing (𝓞 K) K) a ∧
      (((ratCentralHom K a * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 =
        algebraMap K (AdeleRing (𝓞 K) K) a * y := by
  constructor <;>
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ratCentralHom_apply_entry,
      ratCentralHom_apply_entry, unipotentGL2_coe]
    simp

theorem ratCentral_mul_unipotent_mul (a a' : Kˣ) (y y' : AdeleRing (𝓞 K) K) :
    ratCentralHom K a' * unipotentGL2 y' * (ratCentralHom K a * unipotentGL2 y) =
      ratCentralHom K (a' * a) * unipotentGL2 (y' + y) := by
  rw [map_mul, unipotentGL2_add, mul_assoc, ← mul_assoc (unipotentGL2 y'), ← ratCentralHom_comm, mul_assoc, mul_assoc]

theorem continuous_unipotentGL2 :
    Continuous (fun y : AdeleRing (𝓞 K) K => (unipotentGL2 y : AdelicGL2 (𝓞 K) K)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ y : AdeleRing (𝓞 K) K, (↑((unipotentGL2 y : AdelicGL2 (𝓞 K) K)⁻¹) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = !![1, -y; 0, 1] := fun y => rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_toAdelicUnipotent : Continuous (toAdelicUnipotent K) :=
  (continuous_unipotentGL2 K).subtype_mk _

def sheet (a : Kˣ) (n : adelicUnipotent K) : rationalCentreUnipotent K :=
  ⟨globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) *
    (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩

theorem sheet_coe (a : Kˣ) (n : adelicUnipotent K) :
    ((sheet K a n : rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K) = ratCentralHom K a * (n : AdelicGL2 (𝓞 K) K) := rfl

theorem continuous_sheet (a : Kˣ) : Continuous (sheet K a) :=
  (continuous_const.mul continuous_subtype_val).subtype_mk _

theorem measurable_sheet (a : Kˣ) : Measurable (sheet K a) := (continuous_sheet K a).measurable

theorem rationalCentreUnipotentHaar_eq :
    rationalCentreUnipotentHaar K = Measure.sum (fun a : Kˣ => (unipotentHaar K).map (sheet K a)) := rfl

theorem coe_toAdelicUnipotent (y : AdeleRing (𝓞 K) K) :
    ((toAdelicUnipotent K y : adelicUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 y := rfl

theorem exists_eq_toAdelicUnipotent (n : adelicUnipotent K) : ∃ y : AdeleRing (𝓞 K) K, n = toAdelicUnipotent K y := by
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp n.2
  exact ⟨Multiplicative.toAdd y, Subtype.ext hy.symm⟩

theorem coe_inclusion_toAdelicUnipotent (u : AdeleRing (𝓞 K) K) :
    ((Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K) (toAdelicUnipotent K u) :
      rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 u := rfl

theorem sheet_one_eq_inclusion (n : adelicUnipotent K) :
    sheet K 1 n = Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K) n := by
  refine Subtype.ext ?_
  rw [sheet_coe, map_one, one_mul]
  rfl

theorem continuous_entry (i j : Fin 2) : Continuous fun h : rationalCentreUnipotent K =>
    (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) :=
  ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp continuous_subtype_val

theorem boxSheet_eq :
    (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K)
      (toAdelicUnipotent K u)) '' adelicBox K =
    {h : rationalCentreUnipotent K |
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) ∈ adelicBox K} := by
  ext h
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = 1
      simp [unipotentGL2_coe]
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 ∈ adelicBox K
      simpa [unipotentGL2_coe] using hu
  · rintro ⟨h00, h01⟩
    obtain ⟨a, y, hay⟩ := exists_eq K h h.2
    have ha : algebraMap K (AdeleRing (𝓞 K) K) a = 1 := by rw [← (sheet_entries K a y).1, ← hay]; exact h00
    have ha1 : a = 1 := by
      apply Units.ext
      exact (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)) (by rw [ha, Units.val_one, map_one])
    have hy : (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) = y := by
      rw [hay, (sheet_entries K a y).2, ha, one_mul]
    refine ⟨y, hy ▸ h01, Subtype.ext ?_⟩
    rw [coe_inclusion_toAdelicUnipotent, hay, ha1, map_one, one_mul]

theorem measurableSet_boxSheet :
    MeasurableSet ((fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion
      (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K) (toAdelicUnipotent K u)) '' adelicBox K) := by
  rw [boxSheet_eq]
  exact ((continuous_entry K 0 0).measurable (measurableSet_singleton 1)).inter
    ((continuous_entry K 0 1).measurable (measurableSet_adelicBox K))

theorem main :
    let P : Subgroup (AdelicGL2 (𝓞 K) K) :=
      rationalCentre K ⊔ ((globalPoints (𝓞 K) K).comp (unipotentGL2Hom (R := K))).range
    let T : Set (rationalCentreUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    P ≤ rationalCentreUnipotent K ∧ Countable P ∧ MeasurableSet T ∧
    IsFundamentalDomain (P.subgroupOf (rationalCentreUnipotent K)) T (rationalCentreUnipotentHaar K) ∧
    ∀ F : rationalCentreUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalCentreUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by
  intro P T
  haveI : Countable K := countable_numberField K
  have hT : MeasurableSet T := measurableSet_boxSheet K
  have hTeq : T = {h : rationalCentreUnipotent K |
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) ∈ adelicBox K} := boxSheet_eq K

  have hle : P ≤ rationalCentreUnipotent K := by
    refine sup_le le_sup_left ?_
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_sup_right ⟨Multiplicative.ofAdd (algebraMap K (AdeleRing (𝓞 K) K) x.toAdd), ?_⟩
    rw [MonoidHom.comp_apply]
    change unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) x.toAdd) = globalPoints (𝓞 K) K (unipotentGL2 x.toAdd)
    rw [globalPoints_unipotentGL2]

  have hcount : Countable P := by
    haveI : Countable Kˣ := Function.Injective.countable (f := (Units.val : Kˣ → K)) Units.val_injective
    let f : Kˣ × K → P := fun p => ⟨ratCentralHom K p.1 * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) p.2),
      Subgroup.mul_mem_sup ⟨p.1, rfl⟩ ⟨Multiplicative.ofAdd p.2, by
        rw [MonoidHom.comp_apply]
        change globalPoints (𝓞 K) K (unipotentGL2 p.2) = _
        rw [globalPoints_unipotentGL2]⟩⟩
    refine Function.Surjective.countable (f := f) fun g => ?_
    obtain ⟨a, β, h⟩ := exists_eq_rational K g g.2
    exact ⟨(a, β), Subtype.ext h.symm⟩
  refine ⟨hle, hcount, hT, ?_, ?_⟩
  ·
    refine IsFundamentalDomain.mk' hT.nullMeasurableSet fun x => ?_
    obtain ⟨a, y, hay⟩ := exists_eq K x x.2
    obtain ⟨β, hβ, hβu⟩ := existsUnique_algebraMap_add_mem_adelicBox K y

    have hmemP : ∀ (a' : Kˣ) (β' : K),
        ratCentralHom K a' * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β') ∈ P := fun a' β' =>
      Subgroup.mul_mem_sup ⟨a', rfl⟩ ⟨Multiplicative.ofAdd β', by
        rw [MonoidHom.comp_apply]
        change globalPoints (𝓞 K) K (unipotentGL2 β') = _
        rw [globalPoints_unipotentGL2]⟩
    let g₀ : P.subgroupOf (rationalCentreUnipotent K) :=
      ⟨⟨ratCentralHom K a⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β), hle (hmemP a⁻¹ β)⟩,
        Subgroup.mem_subgroupOf.mpr (hmemP a⁻¹ β)⟩
    have hval : ∀ g : P.subgroupOf (rationalCentreUnipotent K),
        (((g • x : rationalCentreUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          ((g : rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K) * (x : AdelicGL2 (𝓞 K) K) := fun g => rfl
    refine ⟨g₀, ?_, ?_⟩
    · show g₀ • x ∈ T
      rw [hTeq]
      have hv : (((g₀ • x : rationalCentreUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          ratCentralHom K (a⁻¹ * a) * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + y) := by
        rw [hval, hay]
        exact ratCentral_mul_unipotent_mul K a a⁻¹ y _
      rw [inv_mul_cancel] at hv
      refine ⟨?_, ?_⟩
      · rw [hv, (sheet_entries K 1 _).1, Units.val_one, map_one]
      · rw [hv, (sheet_entries K 1 _).2, Units.val_one, map_one, one_mul]; exact hβ
    · intro g hg
      rw [hTeq] at hg
      obtain ⟨h00, h01⟩ := hg
      obtain ⟨a', β', ha'⟩ := exists_eq_rational K ((g : rationalCentreUnipotent K) : AdelicGL2 (𝓞 K) K)
        (Subgroup.mem_subgroupOf.mp g.2)
      have hv : (((g • x : rationalCentreUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          ratCentralHom K (a' * a) * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β' + y) := by
        rw [hval, hay, ha']
        exact ratCentral_mul_unipotent_mul K a a' y _
      rw [hv, (sheet_entries K _ _).1] at h00
      rw [hv, (sheet_entries K _ _).2, h00, one_mul] at h01
      have ha'a : a' * a = 1 := by
        apply Units.ext
        exact (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)) (by rw [h00, Units.val_one, map_one])
      have ha'' : a' = a⁻¹ := eq_inv_of_mul_eq_one_left ha'a
      have hβ' : β' = β := hβu β' h01
      apply Subtype.ext
      apply Subtype.ext
      rw [ha', ha'', hβ']
  ·
    intro F hF
    have hind : Measurable (T.indicator F) := hF.indicator hT
    rw [← lintegral_indicator hT, rationalCentreUnipotentHaar_eq, lintegral_sum_measure]
    have hterm : ∀ a : Kˣ, ∫⁻ x, T.indicator F x ∂((unipotentHaar K).map (sheet K a)) =
        ∫⁻ n, T.indicator F (sheet K a n) ∂(unipotentHaar K) := fun a =>
      lintegral_map hind (measurable_sheet K a)
    simp_rw [hterm]
    have hzero : ∀ a : Kˣ, a ≠ 1 → ∫⁻ n, T.indicator F (sheet K a n) ∂(unipotentHaar K) = 0 := by
      intro a ha
      have : ∀ n, T.indicator F (sheet K a n) = 0 := by
        intro n
        apply Set.indicator_of_notMem
        rw [hTeq]
        rintro ⟨h00, -⟩
        obtain ⟨y, rfl⟩ := exists_eq_toAdelicUnipotent K n
        rw [sheet_coe, coe_toAdelicUnipotent, (sheet_entries K a y).1] at h00
        apply ha
        apply Units.ext
        exact (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)) (by rw [h00, Units.val_one, map_one])
      simp [this]
    rw [tsum_eq_single 1 hzero]
    have hm1 : Measurable (fun n : adelicUnipotent K => T.indicator F (sheet K 1 n)) := hind.comp (measurable_sheet K 1)
    rw [unipotentHaar, lintegral_map hm1 (continuous_toAdelicUnipotent K).measurable,
      ← lintegral_indicator (measurableSet_adelicBox K)]
    refine lintegral_congr (fun y => ?_)
    rw [sheet_one_eq_inclusion]
    have hmem : Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalCentreUnipotent K) (toAdelicUnipotent K y) ∈ T ↔
        y ∈ adelicBox K := by
      rw [hTeq, Set.mem_setOf_eq, coe_inclusion_toAdelicUnipotent, unipotentGL2_coe]
      simp
    by_cases hy : y ∈ adelicBox K
    · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun h => hy (hmem.mp h)), Set.indicator_of_notMem hy]

end BoxSheetZN

end AutomorphicForm

end

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let P : Subgroup (AdelicGL2 (𝓞 K) K) :=
      rationalCentre K ⊔ ((globalPoints (𝓞 K) K).comp (unipotentGL2Hom (R := K))).range
    let T : Set (rationalCentreUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    P ≤ rationalCentreUnipotent K ∧ Countable P ∧ MeasurableSet T ∧
    IsFundamentalDomain (P.subgroupOf (rationalCentreUnipotent K)) T (rationalCentreUnipotentHaar K) ∧
    ∀ F : rationalCentreUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalCentreUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) :=
  AutomorphicForm.BoxSheetZN.main K

end S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent
end P2MW
export P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent (solution)
