-- Prove2me | Definitions.Def_LeanPool_Copula_Classical_Approximation
-- name    : LeanPool_Copula_Classical_Approximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:54:15.133837+00:00
-- url     : https://prove2.me/theorems/a3bcf30b-6495-4f12-937d-6aa8c3069def
-- title:
--   Approximation
-- statement:
--   Definitions and structural lemmas for Approximation, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_rectangleIncrement_zero_lower
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_independence
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_empty
public import Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_split
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_independence
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_comonotonic
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_independence
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.corner_empty
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.partialIncrement_empty
attribute [local simp] ProbabilityTheory.Copula.toMeasure_comonotonic
attribute [local simp] ProbabilityTheory.Copula.toMeasure_independence
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap


set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped unitInterval ENNReal BigOperators
namespace ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ClassicalConstruction
inductive Division : (Fin d → I) → (Fin d → I) → Type
  | leaf {a b} (hab : a ≤ b) : Division a b
  | cut {a b} (i : Fin d) (t : I) (hat : a i ≤ t) (htb : t ≤ b i)
      (left : Division a (Function.update b i t))
      (right : Division (Function.update a i t) b) : Division a b
namespace Division
variable {a b : Fin d → I}
theorem ordered (D : Division a b) : a ≤ b := by
  induction D with
  | leaf hab => exact hab
  | @cut a b i t hat htb left right ihl ihr =>
    intro j
    by_cases hj : j = i
    · subst j; exact hat.trans htb
    · simpa only [Function.update_of_ne hj] using ihl j
@[expose]
def All (P : (Fin d → I) → (Fin d → I) → Prop) :
    ∀ {a b : Fin d → I}, Division a b → Prop
  | a, b, .leaf _ => P a b
  | _, _, .cut _ _ _ _ left right => left.All P ∧ right.All P
@[expose]
noncomputable def measure (F : (Fin d → I) → ℝ) :
    ∀ {a b : Fin d → I}, Division a b → Measure (Fin d → I)
  | a, b, .leaf _ => ENNReal.ofReal (rectangleIncrement F a b) • Measure.dirac b
  | _, _, .cut _ _ _ _ left right => left.measure F + right.measure F
theorem measure_univ (hF : IsClassical F) (D : Division a b) :
    D.measure F univ = ENNReal.ofReal (rectangleIncrement F a b) := by
  induction D with
  | leaf hab => simp only [measure, Measure.smul_apply, MeasureTheory.measure_univ,
    smul_eq_mul, mul_one]
  | @cut a b i t hat htb left right ihl ihr =>
    rw [measure, Measure.add_apply, ihl, ihr,
      ← ENNReal.ofReal_add (hF.increasing _ _ left.ordered) (hF.increasing _ _ right.ordered),
      ← rectangleIncrement_split]
@[expose]
noncomputable def grid (l : List (Fin d)) (a b : Fin d → I) (hab : a ≤ b) : Division a b :=
  match l with
  | [] => .leaf hab
  | i :: l =>
    let t : I := ⟨((a i : ℝ) + (b i : ℝ)) / 2, by
      constructor
      · linarith [(a i).property.1, (b i).property.1]
      · linarith [(a i).property.2, (b i).property.2]⟩
    have hat : a i ≤ t := by
      change (a i : ℝ) ≤ _
      dsimp [t]
      have := hab i
      change (a i : ℝ) ≤ (b i : ℝ) at this
      linarith
    have htb : t ≤ b i := by
      change _ ≤ (b i : ℝ)
      dsimp [t]
      have := hab i
      change (a i : ℝ) ≤ (b i : ℝ) at this
      linarith
    .cut i t hat htb
      (grid l a (Function.update b i t) (by
        intro j; by_cases hj : j = i
        · subst j; simpa only [Function.update_self] using hat
        · simpa only [Function.update_of_ne hj] using hab j))
      (grid l (Function.update a i t) b (by
        intro j; by_cases hj : j = i
        · subst j; simpa only [Function.update_self] using htb
        · simpa only [Function.update_of_ne hj] using hab j))
end Division
@[expose]
noncomputable def probability (hF : IsClassical F)
    (D : Division (fun _ : Fin d => 0) (fun _ => 1)) : ProbabilityMeasure (Fin d → I) :=
  ⟨D.measure F, ⟨by rw [D.measure_univ hF, hF.rectangleIncrement_zero_lower,
    hF.normalized, ENNReal.ofReal_one]⟩⟩
@[expose]
noncomputable def approximation (hF : IsClassical F) (n : ℕ) : ProbabilityMeasure (Fin d → I) :=
  probability hF (Division.grid ((List.replicate n (List.finRange d)).flatten)
    (fun _ => 0) (fun _ => 1) (by intro i; exact zero_le_one))
end ClassicalConstruction
end ProbabilityTheory.Copula


