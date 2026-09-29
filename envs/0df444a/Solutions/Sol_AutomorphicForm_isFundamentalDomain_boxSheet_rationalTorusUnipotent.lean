-- Prove2me | solution 1 for AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/44460e51-0662-5e4a-9648-efc47385c41c

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent.AutomorphicForm"
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorus rationalTorusUnipotent rationalTorusUnipotentHaar adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add AdelicGL2 globalPoints borelSubgroup borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup globalPoints_apply"
p2m_open "AutomorphicForm"

namespace BoxSheetTN

variable (K : Type) [Field K] [NumberField K]

theorem countable_numberField : Countable K := by
  have e := (Module.finBasis ℚ K).equivFun.toEquiv
  exact e.symm.countable_iff.mp inferInstance

def ratCentralHom : Kˣ →* AdelicGL2 (𝓞 K) K :=
  (globalPoints (𝓞 K) K).comp (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)

def diagHom : Kˣ →* AdelicGL2 (𝓞 K) K :=
  (globalPoints (𝓞 K) K).comp (diagOne (A := K))

theorem ratCentralHom_apply_entry (a : Kˣ) (i j : Fin 2) :
    ((ratCentralHom K a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then algebraMap K (AdeleRing (𝓞 K) K) a else 0 := by
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem diagHom_apply_entry (a : Kˣ) (i j : Fin 2) :
    ((diagHom K a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then (if i = 0 then algebraMap K (AdeleRing (𝓞 K) K) a else 1) else 0 := by
  change algebraMap K (AdeleRing (𝓞 K) K) ((diagOne a : Matrix (Fin 2) (Fin 2) K) i j) = _
  rw [diagOne_coe_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp

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

theorem unipotentGL2_mul_diagHom (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    unipotentGL2 y * diagHom K a = diagHom K a * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((a⁻¹ : Kˣ) : K) * y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two, diagHom_apply_entry, diagHom_apply_entry, diagHom_apply_entry,
    diagHom_apply_entry, unipotentGL2_coe]
  have hinv : algebraMap K (AdeleRing (𝓞 K) K) (a : K) * algebraMap K (AdeleRing (𝓞 K) K) ((a : K)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ a.ne_zero, map_one]
  fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hinv]

def torus (za : Kˣ × Kˣ) : AdelicGL2 (𝓞 K) K := ratCentralHom K za.1 * diagHom K za.2

theorem torus_mul (za zb : Kˣ × Kˣ) : torus K za * torus K zb = torus K (za * zb) := by
  simp only [torus, Prod.fst_mul, Prod.snd_mul, map_mul]
  rw [mul_assoc, ← mul_assoc (diagHom K za.2), ← ratCentralHom_comm, mul_assoc, mul_assoc]

theorem torus_one : torus K 1 = 1 := by
  simp [torus]

theorem torus_inv (za : Kˣ × Kˣ) : (torus K za)⁻¹ = torus K za⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [torus_mul, mul_inv_cancel, torus_one])

theorem unipotentGL2_mul_torus (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K) :
    unipotentGL2 y * torus K za = torus K za * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((za.2⁻¹ : Kˣ) : K) * y) := by
  rw [torus, ← mul_assoc, ← ratCentralHom_comm, mul_assoc, unipotentGL2_mul_diagHom, mul_assoc]

theorem mem_torus (za : Kˣ × Kˣ) : torus K za ∈ rationalTorusUnipotent K :=
  Subgroup.mem_sup_left (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩)

theorem mem_unipotent (y : AdeleRing (𝓞 K) K) : (unipotentGL2 y : AdelicGL2 (𝓞 K) K) ∈ rationalTorusUnipotent K :=
  Subgroup.mem_sup_right ⟨Multiplicative.ofAdd y, rfl⟩

theorem unipotentGL2_inv (y : AdeleRing (𝓞 K) K) : (unipotentGL2 y : AdelicGL2 (𝓞 K) K)⁻¹ = unipotentGL2 (-y) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem exists_eq_torus (g : AdelicGL2 (𝓞 K) K) (hg : g ∈ rationalTorus K) : ∃ za : Kˣ × Kˣ, g = torus K za := by
  rw [rationalTorus, Subgroup.sup_eq_closure] at hg
  refine Subgroup.closure_induction (p := fun g _ => ∃ za : Kˣ × Kˣ, g = torus K za) ?_ ?_ ?_ ?_ hg
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨(a, 1), by show _ = ratCentralHom K a * diagHom K 1; rw [map_one, mul_one]; rfl⟩
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨(1, a), by show _ = ratCentralHom K 1 * diagHom K a; rw [map_one, one_mul]; rfl⟩
  · exact ⟨1, (torus_one K).symm⟩
  · rintro g g' _ _ ⟨za, rfl⟩ ⟨zb, rfl⟩
    exact ⟨za * zb, torus_mul K za zb⟩
  · rintro g _ ⟨za, rfl⟩
    exact ⟨za⁻¹, torus_inv K za⟩

theorem exists_eq (h : AdelicGL2 (𝓞 K) K) (hh : h ∈ rationalTorusUnipotent K) :
    ∃ (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K), h = torus K za * unipotentGL2 y := by
  rw [rationalTorusUnipotent, Subgroup.sup_eq_closure] at hh
  refine Subgroup.closure_induction (p := fun g _ => ∃ (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K), g = torus K za * unipotentGL2 y)
    ?_ ?_ ?_ ?_ hh
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨za, rfl⟩ := exists_eq_torus K g hg
      exact ⟨za, 0, by rw [unipotentGL2_zero, mul_one]⟩
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
      exact ⟨1, Multiplicative.toAdd y, by rw [torus_one, one_mul]; rfl⟩
  · exact ⟨1, 0, by rw [torus_one, unipotentGL2_zero, mul_one]⟩
  · rintro g g' _ _ ⟨za, y, rfl⟩ ⟨zb, y', rfl⟩
    refine ⟨za * zb, algebraMap K (AdeleRing (𝓞 K) K) ((zb.2⁻¹ : Kˣ) : K) * y + y', ?_⟩
    rw [mul_assoc, ← mul_assoc (unipotentGL2 y), unipotentGL2_mul_torus, mul_assoc, ← unipotentGL2_add, ← mul_assoc,
      torus_mul]
  · rintro g _ ⟨za, y, rfl⟩
    refine ⟨za⁻¹, algebraMap K (AdeleRing (𝓞 K) K) (((za⁻¹).2⁻¹ : Kˣ) : K) * (-y), ?_⟩
    rw [mul_inv_rev, unipotentGL2_inv, torus_inv, unipotentGL2_mul_torus]

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

def sheet (za : Kˣ × Kˣ) (n : adelicUnipotent K) : rationalTorusUnipotent K :=
  ⟨torus K za * (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩) n.2⟩

theorem sheet_coe (za : Kˣ × Kˣ) (n : adelicUnipotent K) :
    ((sheet K za n : rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K) = torus K za * (n : AdelicGL2 (𝓞 K) K) := rfl

theorem continuous_sheet (za : Kˣ × Kˣ) : Continuous (sheet K za) :=
  (continuous_const.mul continuous_subtype_val).subtype_mk _

theorem measurable_sheet (za : Kˣ × Kˣ) : Measurable (sheet K za) := (continuous_sheet K za).measurable

theorem rationalTorusUnipotentHaar_eq :
    rationalTorusUnipotentHaar K = Measure.sum (fun za : Kˣ × Kˣ => (unipotentHaar K).map (sheet K za)) := rfl

theorem coe_toAdelicUnipotent (y : AdeleRing (𝓞 K) K) :
    ((toAdelicUnipotent K y : adelicUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 y := rfl

theorem exists_eq_toAdelicUnipotent (n : adelicUnipotent K) : ∃ y : AdeleRing (𝓞 K) K, n = toAdelicUnipotent K y := by
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp n.2
  exact ⟨Multiplicative.toAdd y, Subtype.ext hy.symm⟩

theorem torus_apply_entry (za : Kˣ × Kˣ) (i j : Fin 2) :
    ((torus K za : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then (if i = 0 then algebraMap K (AdeleRing (𝓞 K) K) ((za.1 * za.2 : Kˣ) : K)
        else algebraMap K (AdeleRing (𝓞 K) K) (za.1 : K)) else 0 := by
  rw [torus, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ratCentralHom_apply_entry,
    ratCentralHom_apply_entry, diagHom_apply_entry, diagHom_apply_entry]
  fin_cases i <;> fin_cases j <;> simp [map_mul]

theorem sheet_entries (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K) :
    (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
        algebraMap K (AdeleRing (𝓞 K) K) ((za.1 * za.2 : Kˣ) : K) ∧
      (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 =
        algebraMap K (AdeleRing (𝓞 K) K) ((za.1 * za.2 : Kˣ) : K) * y ∧
      (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 =
        algebraMap K (AdeleRing (𝓞 K) K) (za.1 : K) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, torus_apply_entry, torus_apply_entry,
      unipotentGL2_coe]
    simp

theorem globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem torus_mul_unipotent_mul (za zb : Kˣ × Kˣ) (y y' : AdeleRing (𝓞 K) K) :
    torus K zb * unipotentGL2 y' * (torus K za * unipotentGL2 y) =
      torus K (zb * za) * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((za.2⁻¹ : Kˣ) : K) * y' + y) := by
  rw [mul_assoc, ← mul_assoc (unipotentGL2 y'), unipotentGL2_mul_torus, mul_assoc, ← unipotentGL2_add, ← mul_assoc,
    torus_mul]

omit [NumberField K] in

theorem borel_eq (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    b = Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom (borelDiagSnd ⟨b, hb⟩) *
      diagOne (borelDiagFst ⟨b, hb⟩ * (borelDiagSnd ⟨b, hb⟩)⁻¹) *
      unipotentGL2 ((b : Matrix (Fin 2) (Fin 2) K) 0 1 / (b : Matrix (Fin 2) (Fin 2) K) 0 0) := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
  have hd₁v : ((borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup K)) : Kˣ) : K) = (b : Matrix (Fin 2) (Fin 2) K) 0 0 := rfl
  have hd₂v : ((borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup K)) : Kˣ) : K) = (b : Matrix (Fin 2) (Fin 2) K) 1 1 := rfl
  have h00 : (b : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := hd₁v ▸ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup K))).ne_zero
  have h11 : (b : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := hd₂v ▸ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup K))).ne_zero
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, Units.coe_map, unipotentGL2_coe]
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
    diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hb10, hd₁v, hd₂v, Units.val_mul]
  all_goals field_simp

theorem globalPoints_borel_eq (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    globalPoints (𝓞 K) K b =
      torus K (borelDiagSnd ⟨b, hb⟩, borelDiagFst ⟨b, hb⟩ * (borelDiagSnd ⟨b, hb⟩)⁻¹) *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K)
          ((b : Matrix (Fin 2) (Fin 2) K) 0 1 / (b : Matrix (Fin 2) (Fin 2) K) 0 0)) := by
  conv_lhs => rw [borel_eq K b hb]
  rw [map_mul, map_mul, globalPoints_unipotentGL2]
  rfl

theorem torus_mul_unipotent_mem_map (za : Kˣ × Kˣ) (β : K) :
    torus K za * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) ∈ (borelSubgroup K).map (globalPoints (𝓞 K) K) := by
  refine ⟨Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1 * diagOne za.2 * unipotentGL2 β,
    ?_, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (unipotentGL2_mem_borelSubgroup β)
    · show (Matrix.scalar (Fin 2) ((za.1 : Kˣ) : K)) 1 0 = 0
      simp
    · show (diagOne za.2 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
      rw [diagOne_coe_apply]; simp
  · rw [map_mul, map_mul, globalPoints_unipotentGL2]
    rfl

theorem exists_eq_of_mem_map (g : AdelicGL2 (𝓞 K) K) (hg : g ∈ (borelSubgroup K).map (globalPoints (𝓞 K) K)) :
    ∃ (za : Kˣ × Kˣ) (β : K), g = torus K za * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  obtain ⟨b, hb, rfl⟩ := hg
  exact ⟨_, _, globalPoints_borel_eq K b hb⟩

theorem coe_inclusion_toAdelicUnipotent (u : AdeleRing (𝓞 K) K) :
    ((Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K) (toAdelicUnipotent K u) :
      rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 u := rfl

theorem sheet_one_eq_inclusion (n : adelicUnipotent K) :
    sheet K 1 n = Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K) n := by
  refine Subtype.ext ?_
  rw [sheet_coe, torus_one, one_mul]
  rfl

theorem continuous_entry (i j : Fin 2) : Continuous fun h : rationalTorusUnipotent K =>
    (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) :=
  ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp continuous_subtype_val

theorem torus_eq_one_of_entries (za : Kˣ × Kˣ) (y : AdeleRing (𝓞 K) K)
    (h00 : (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = 1)
    (h11 : (((torus K za * unipotentGL2 y : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = 1) :
    za = 1 := by
  rw [(sheet_entries K za y).1] at h00
  rw [(sheet_entries K za y).2.2] at h11
  have hz : za.1 = 1 := by
    apply Units.ext
    exact (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)) (by rw [h11, Units.val_one, map_one])
  have hza : za.1 * za.2 = 1 := by
    apply Units.ext
    exact (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)) (by rw [h00, Units.val_one, map_one])
  rw [hz, one_mul] at hza
  exact Prod.ext hz hza

theorem boxSheet_eq :
    (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K)
      (toAdelicUnipotent K u)) '' adelicBox K =
    {h : rationalTorusUnipotent K |
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) ∈ adelicBox K} := by
  ext h
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = 1
      simp [unipotentGL2_coe]
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = 1
      simp [unipotentGL2_coe]
    · show ((unipotentGL2 u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 ∈ adelicBox K
      simpa [unipotentGL2_coe] using hu
  · rintro ⟨h00, h11, h01⟩
    obtain ⟨za, y, hay⟩ := exists_eq K h h.2
    have hza : za = 1 := torus_eq_one_of_entries K za y (hay ▸ h00) (hay ▸ h11)
    have hy : (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) = y := by
      rw [hay, (sheet_entries K za y).2.1, hza]
      simp
    refine ⟨y, hy ▸ h01, Subtype.ext ?_⟩
    rw [coe_inclusion_toAdelicUnipotent, hay, hza, torus_one, one_mul]

theorem measurableSet_boxSheet :
    MeasurableSet ((fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion
      (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K) (toAdelicUnipotent K u)) '' adelicBox K) := by
  rw [boxSheet_eq]
  exact ((continuous_entry K 0 0).measurable (measurableSet_singleton 1)).inter
    (((continuous_entry K 1 1).measurable (measurableSet_singleton 1)).inter
      ((continuous_entry K 0 1).measurable (measurableSet_adelicBox K)))

theorem main :
    let B : Subgroup (AdelicGL2 (𝓞 K) K) := (borelSubgroup K).map (globalPoints (𝓞 K) K)
    let T : Set (rationalTorusUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    B ≤ rationalTorusUnipotent K ∧ Countable B ∧ MeasurableSet T ∧
    IsFundamentalDomain (B.subgroupOf (rationalTorusUnipotent K)) T (rationalTorusUnipotentHaar K) ∧
    ∀ F : rationalTorusUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalTorusUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by
  intro B T
  haveI : Countable K := countable_numberField K
  have hT : MeasurableSet T := measurableSet_boxSheet K
  have hTeq : T = {h : rationalTorusUnipotent K |
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1) = 1 ∧
      (((h : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) ∈ adelicBox K} := boxSheet_eq K
  have hmemB : ∀ (za : Kˣ × Kˣ) (β : K), torus K za * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) ∈ B :=
    torus_mul_unipotent_mem_map K

  have hle : B ≤ rationalTorusUnipotent K := by
    intro g hg
    obtain ⟨za, β, rfl⟩ := exists_eq_of_mem_map K g hg
    exact Subgroup.mul_mem _ (mem_torus K za) (mem_unipotent K _)

  have hcount : Countable B := by
    haveI : Countable Kˣ := Function.Injective.countable (f := (Units.val : Kˣ → K)) Units.val_injective
    let f : (Kˣ × Kˣ) × K → B := fun p => ⟨torus K p.1 * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) p.2), hmemB p.1 p.2⟩
    refine Function.Surjective.countable (f := f) fun g => ?_
    obtain ⟨za, β, h⟩ := exists_eq_of_mem_map K g g.2
    exact ⟨(za, β), Subtype.ext h.symm⟩
  refine ⟨hle, hcount, hT, ?_, ?_⟩
  ·
    refine IsFundamentalDomain.mk' hT.nullMeasurableSet fun x => ?_
    obtain ⟨za, y, hay⟩ := exists_eq K x x.2
    obtain ⟨β₀, hβ₀, hβ₀u⟩ := existsUnique_algebraMap_add_mem_adelicBox K y
    let g₀ : B.subgroupOf (rationalTorusUnipotent K) :=
      ⟨⟨torus K za⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ((za.2 : K) * β₀)), hle (hmemB za⁻¹ _)⟩,
        Subgroup.mem_subgroupOf.mpr (hmemB za⁻¹ _)⟩
    have hval : ∀ g : B.subgroupOf (rationalTorusUnipotent K),
        (((g • x : rationalTorusUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          ((g : rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K) * (x : AdelicGL2 (𝓞 K) K) := fun g => rfl
    have hscale : ∀ β : K, algebraMap K (AdeleRing (𝓞 K) K) ((za.2⁻¹ : Kˣ) : K) * algebraMap K (AdeleRing (𝓞 K) K) β =
        algebraMap K (AdeleRing (𝓞 K) K) (((za.2⁻¹ : Kˣ) : K) * β) := fun β => by rw [map_mul]
    refine ⟨g₀, ?_, ?_⟩
    · show g₀ • x ∈ T
      rw [hTeq]
      have hv : (((g₀ • x : rationalTorusUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          torus K (za⁻¹ * za) * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β₀ + y) := by
        rw [hval, hay]
        have hk : ((za.2⁻¹ : Kˣ) : K) * ((za.2 : K) * β₀) = β₀ := by
          rw [Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ za.2.ne_zero, one_mul]
        have := torus_mul_unipotent_mul K za za⁻¹ y (algebraMap K (AdeleRing (𝓞 K) K) ((za.2 : K) * β₀))
        rw [hscale, hk] at this
        exact this
      rw [inv_mul_cancel] at hv
      refine ⟨?_, ?_, ?_⟩
      · rw [hv, (sheet_entries K 1 _).1]; simp
      · rw [hv, (sheet_entries K 1 _).2.2]; simp
      · rw [hv, (sheet_entries K 1 _).2.1]; simpa using hβ₀
    · intro g hg
      rw [hTeq] at hg
      obtain ⟨h00, h11, h01⟩ := hg
      obtain ⟨zb, β', hb'⟩ := exists_eq_of_mem_map K ((g : rationalTorusUnipotent K) : AdelicGL2 (𝓞 K) K)
        (Subgroup.mem_subgroupOf.mp g.2)
      have hv : (((g • x : rationalTorusUnipotent K)) : AdelicGL2 (𝓞 K) K) =
          torus K (zb * za) * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) (((za.2⁻¹ : Kˣ) : K) * β') + y) := by
        rw [hval, hay, hb', torus_mul_unipotent_mul, hscale]
      rw [hv] at h00 h11 h01
      have hw : zb * za = 1 := torus_eq_one_of_entries K _ _ h00 h11
      rw [hw, (sheet_entries K 1 _).2.1] at h01
      simp only [Prod.fst_one, Prod.snd_one, mul_one, Units.val_one, map_one, one_mul] at h01
      have hzb : zb = za⁻¹ := eq_inv_of_mul_eq_one_left hw
      have hβ' : ((za.2⁻¹ : Kˣ) : K) * β' = β₀ := hβ₀u _ h01
      have hβ'' : β' = (za.2 : K) * β₀ := by
        rw [← hβ', ← mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ za.2.ne_zero, one_mul]
      apply Subtype.ext
      apply Subtype.ext
      rw [hb', hzb, hβ'']
  ·
    intro F hF
    have hind : Measurable (T.indicator F) := hF.indicator hT
    rw [← lintegral_indicator hT, rationalTorusUnipotentHaar_eq, lintegral_sum_measure]
    have hterm : ∀ za : Kˣ × Kˣ, ∫⁻ x, T.indicator F x ∂((unipotentHaar K).map (sheet K za)) =
        ∫⁻ n, T.indicator F (sheet K za n) ∂(unipotentHaar K) := fun za =>
      lintegral_map hind (measurable_sheet K za)
    simp_rw [hterm]
    have hzero : ∀ za : Kˣ × Kˣ, za ≠ 1 → ∫⁻ n, T.indicator F (sheet K za n) ∂(unipotentHaar K) = 0 := by
      intro za hza
      have : ∀ n, T.indicator F (sheet K za n) = 0 := by
        intro n
        apply Set.indicator_of_notMem
        rw [hTeq]
        rintro ⟨h00, h11, -⟩
        obtain ⟨y, rfl⟩ := exists_eq_toAdelicUnipotent K n
        rw [sheet_coe, coe_toAdelicUnipotent] at h00 h11
        exact hza (torus_eq_one_of_entries K za y h00 h11)
      simp [this]
    rw [tsum_eq_single 1 hzero]
    have hm1 : Measurable (fun n : adelicUnipotent K => T.indicator F (sheet K 1 n)) := hind.comp (measurable_sheet K 1)
    rw [unipotentHaar, lintegral_map hm1 (continuous_toAdelicUnipotent K).measurable,
      ← lintegral_indicator (measurableSet_adelicBox K)]
    refine lintegral_congr (fun y => ?_)
    rw [sheet_one_eq_inclusion]
    have hmem : Subgroup.inclusion (le_sup_right : adelicUnipotent K ≤ rationalTorusUnipotent K) (toAdelicUnipotent K y) ∈ T ↔
        y ∈ adelicBox K := by
      rw [hTeq, Set.mem_setOf_eq, coe_inclusion_toAdelicUnipotent, unipotentGL2_coe]
      simp
    by_cases hy : y ∈ adelicBox K
    · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun h => hy (hmem.mp h)), Set.indicator_of_notMem hy]

end BoxSheetTN

end AutomorphicForm

end

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let B : Subgroup (AdelicGL2 (𝓞 K) K) := (borelSubgroup K).map (globalPoints (𝓞 K) K)
    let T : Set (rationalTorusUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    B ≤ rationalTorusUnipotent K ∧ Countable B ∧ MeasurableSet T ∧
    IsFundamentalDomain (B.subgroupOf (rationalTorusUnipotent K)) T (rationalTorusUnipotentHaar K) ∧
    ∀ F : rationalTorusUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalTorusUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) :=
  AutomorphicForm.BoxSheetTN.main K

end S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
end P2MW
export P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent (solution)
