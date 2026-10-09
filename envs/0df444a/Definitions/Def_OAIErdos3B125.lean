-- Prove2me | Definitions.Def_OAIErdos3B125
-- name    : OAIErdos3B125
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T07:07:48.612289+00:00
-- url     : https://prove2.me/theorems/db1baadb-beb0-4394-8854-5843ec9de892
-- title:
--   OpenAI Erdős-3 split, definitions bundle 126 of 132
-- statement:
--   Definitions bundle 126 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B124`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 126 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.bracket_array_matching_remainder`, `OAI.Erdos3.NilpotentLieFiltration.bracket_arrays_match_lifts`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_bracket_polynomial_step`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_formal_bracket_step`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_induction_iteration`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_induction_stage`, `OAI.Erdos3.NilpotentLieFiltration.exists_uniform_controlled_bracket_stage`, `OAI.Erdos3.NilpotentLieFiltration.exists_uniform_formal_bracket_step`, `OAI.Erdos3.NilpotentLieFiltration.exists_uniform_formal_induction_iteration`, `OAI.Erdos3.NilpotentLieFiltration.formal_bracket_induction_step`, `OAI.Erdos3.NilpotentLieFiltration.formal_bracket_induction_step_mod`, `OAI.Erdos3.NilpotentLieFiltration.formal_current_bracket_equation`, `OAI.Erdos3.NilpotentLieFiltration.formal_current_bracket_equation_mod`, `OAI.Erdos3.exists_formal_iteration_uniform_budget`, `OAI.Erdos3.formalIterationBudget`, `OAI.Erdos3.formalIterationBudget_ge`, `OAI.Erdos3.formalIterationBudget_monotone`, `OAI.Erdos3.formalIterationBudget_nonneg`, `OAI.Erdos3.formalIterationBudget_succ`, `OAI.Erdos3.formalIterationBudget_zero`, `OAI.Erdos3.formalIterationPolynomial`, `OAI.Erdos3.formalIterationPolynomial_eval`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B045

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UniformControlledBracketStage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct Matrix

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_bracket_polynomial_step
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (hgraded : BasisHomogeneousBrackets (b.baseChange ℝ) w)
    {d H J l : ℕ} (hd : 0 < d)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w d x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P Pd : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPU : ∀ α, coefficients P α ∈ U)
    (hPgraded : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPd : Pd = map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P)
    (hPdE : ∀ α, coefficients Pd α ∈ E.baseChange ℝ)
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hsmallhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients small α = 0)
    (hrationalhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients rational α = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (coefficients Pd α) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B P' : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realBracketSystem f k).restrictScalars ℚ) A = small ∧
      map ((realBracketSystem f k).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      P' = bchRemove s A P B ∧ lieBCH s (lieBCH s A P') B = P ∧
      coefficients P' 0 = coefficients P 0 ∧
      P' ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
      (∀ α, coefficients P' α ∈ U) ∧
      (∀ α t, ⁅coefficients (map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P') α,
        (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ) ∧
      ∀ r < d, map ((basisGradeProjection (b.baseChange ℝ) w r).restrictScalars ℚ) P' =
        map ((basisGradeProjection (b.baseChange ℝ) w r).restrictScalars ℚ) P := by
  obtain ⟨Q, hQ, hQzero⟩ := exists_subspace_coordinate_polynomial e Pd hPdE
  have hPd0 : coefficients Pd 0 = 0 := by
    rw [hPd]
    exact gradedPolynomialSubmodule_projection_homogeneous (b.baseChange ℝ) w (fun _ => 1)
      P hPgraded d 0 (by simpa using Nat.ne_of_lt hd)
  have hcoeff (α : σ →₀ ℕ) : bracketSystemLift e (coefficients Q α) = coefficients Pd α := by
    have h := congrArg (fun p => coefficients p α) hQ
    simpa only [coefficients_map, LinearMap.restrictScalars_apply] using h
  have hsmall0 : coefficients small 0 = 0 := hsmallhom 0 (by simpa using Nat.ne_of_lt hd)
  have hrational0 : coefficients rational 0 = 0 := hrationalhom 0 (by simpa using Nat.ne_of_lt hd)
  have h := exists_ambient_bracket_correction_polynomials b e f k hH hl hA he hp hrows hcols hHp hlp
    T hT Q small rational (hQzero 0 hPd0) hsmall0 hrational0 hsmall hrational
    (fun α => by rw [hcoeff]; exact heq α)
  obtain ⟨m, A, B, hm, hmp, hAQ, hBQ, hAB, hAzero, hBzero, hAnorm, hBgrid, hres⟩ := h
  have hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0 :=
    fun α hα => hAzero α (hsmallhom α hα)
  have hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0 :=
    fun α hα => hBzero α (hrationalhom α hα)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers (E.baseChange ℝ) d hE A P B
    (fun α => (hAB α).1) (fun α => (hAB α).2)
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    d A hAhom (fun α => hE _ (hAB α).1)
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    d B hBhom (fun α => hE _ (hAB α).2)
  refine ⟨m, A, B, bchRemove s A P B, hm, hmp, hAQ, hBQ, hAB, hAhom, hBhom, hAnorm, hBgrid,
    rfl, bchRemove_factorization F.realification.lowerCentralSeries_eq_bot A P B,
    bchRemove_constant F.realification.lowerCentralSeries_eq_bot A P B
      (hAzero 0 hsmall0) (hBzero 0 hrational0),
    bchRemove_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w hgraded (fun _ => 1) s A P B
      hAgraded hPgraded hBgraded,
    bchRemove_coefficients_mem U s A P B (fun α => hEU _ (hAB α).1) hPU
      (fun α => hEU _ (hAB α).2), ?_, hgrades.2⟩
  intro α t
  rw [hgrades.1, ← hPd]
  simpa only [hQ] using hres α t

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_bracket_induction_step (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) =
      coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) =
      coefficients B.coord α)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hSR : PolynomialLiftSystem P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V)
    (hleft : ∀ t α, coefficients (S t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hright : ∀ t α, coefficients (R t - monomial 0 (k t) + ⁅B.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := fun t => dualAdjoint A⁻¹ (S t)
    let R' := fun t => dualAdjoint B (R t)
    A * P' * B = P ∧ (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ d < j - 1,
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
      (∀ d < j, ∀ t α,
        ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V) ∧
      PolynomialLiftSystem P' S' R' ∧
      ∀ t α,
        coefficients (S' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        coefficients (R' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        ⁅coefficients P'.coord α, k t⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' S' R'
  let Vq := V.restrictScalars ℚ
  let p := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ Vq ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hp : p ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [coefficients_map]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have ha : A.coord ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hb : B.coord ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [← hB α]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hkl (t : κ) : k t ∈ F.realification.layer 1 := by
    rw [F.realification.one_eq_top]
    trivial
  have hstep : j - 1 + 2 = j + 1 := by omega
  have hrem (t : κ) (α : σ →₀ ℕ) :
      coefficients (⁅P.coord - p, monomial (R := ℚ) 0 (k t)⁆ :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P.coord α) (k t) (hkl t) (fun d hd => hlower d hd t α)
    rw [hstep] at h
    simpa only [p, coefficients_lie_constant, map_sub, Finsupp.sub_apply, coefficients_map,
      LinearMap.restrictScalars_apply] using h
  have hnorm := F.realification.polynomialFiltration.current_layer_normalization hs
    (coefficientLieSubalgebra U) (coefficientSubmodule Vq)
    (fun X hX Y hY => coefficientSubmodule_invariant U Vq hUV X Y hX hY)
    hj P A B hPU hAU hBU ha hb S R (fun t => monomial 0 (k t)) p hp hSR
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq j _).mpr
      (fun α => (hW j _).mpr (hR t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hrem t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hleft t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hright t α)))
  obtain ⟨hprod, hP'U, _, _, hS'R', hcurrent⟩ := hnorm
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w (j - 1) - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x := by
    intro x hx
    exact sub_eq_zero.mp hx
  have haE : ∀ α, coefficients A.coord α ∈ E := fun α => sub_eq_zero.mpr (hA α)
  have hbE : ∀ α, coefficients B.coord α ∈ E := fun α => sub_eq_zero.mpr (hB α)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers E (j - 1) hE A.coord P.coord B.coord haE hbE
  have hgrade : VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P'.coord =
      p - A.coord - B.coord := hgrades.1
  have hcur (t : κ) (α : σ →₀ ℕ) :
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P'.coord α), k t⁆ ∈ V := by
    apply F.real_mem_of_homogeneous_mem_sup_next b w hlayers V hV j
    · have h := (hgraded.baseChange b w).projection_lie (b.baseChange ℝ) w
        (basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1}
          (coefficients P'.coord α)) (hk t)
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
      exact h
    · have h := (hW (j + 1) _).mp
        ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp
          (hcurrent t).2.2 α)
      rw [← hgrade, coefficients_lie_constant, coefficients_map] at h
      exact h
  have hall (d : ℕ) (hd : d < j) (t : κ) (α : σ →₀ ℕ) :
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V := by
    rcases lt_or_eq_of_le (show d ≤ j - 1 by omega) with hlt | rfl
    · have h := congrArg (fun Q => coefficients Q α) (hgrades.2 d hlt)
      simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
      have he : basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) =
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := h
      rw [he]
      exact hlower d hlt t α
    · exact hcur t α
  refine ⟨hprod, hP'U, hgrades.2, hall, hS'R', fun t α => ⟨?_, ?_, ?_⟩⟩
  · exact (hW (j + 1) _).mp
      ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp (hcurrent t).1 α)
  · exact (hW (j + 1) _).mp
      ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp (hcurrent t).2.1 α)
  · have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P'.coord α) (k t) (hkl t) (fun d hd => hall d (by omega) t α)
    rw [hstep] at h
    have ht := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem h
      (Submodule.mem_sup_left (hcur t α))
    simpa only [sub_lie, sub_add_cancel] using ht

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {μ ι κ σ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {V : Submodule ℚ L}

include hlayers in
theorem bracket_array_matching_remainder
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (j : ℕ)
    (X : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (A : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hX : ∀ t α, coefficients (X t) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hA : map ((realBracketSystem f k).restrictScalars ℚ) A =
      liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (X t))) :
    ∀ t α, coefficients (X t - ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈
      V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hmatch := bracket_system_matches_lift_array f k A _ hA
  intro t
  exact F.polynomial_lift_matching_remainder b w hlayers (V.baseChange ℝ) hV j
    (X t) _ (hX t) (hmatch t)

include hlayers in
theorem bracket_arrays_match_lifts
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (j : ℕ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hR : ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hA : map ((realBracketSystem f k).restrictScalars ℚ) A =
      liftQuotientArray f (fun t => map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))
    (hB : map ((realBracketSystem f k).restrictScalars ℚ) B =
      liftQuotientArray f (fun t => map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) :
    (∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) -
      ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
    ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) +
      ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  refine ⟨F.bracket_array_matching_remainder b w hlayers hV f k j _ A hS hA, ?_⟩
  have hneg : ∀ t α, coefficients (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule := by
    intro t α
    rw [map_neg, Finsupp.neg_apply]
    exact Submodule.neg_mem _ (hR t α)
  have hmatch := F.bracket_array_matching_remainder b w hlayers hV f k j _ B hneg hB
  intro t α
  have he : R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) + ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆ =
      -(-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) - ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) := by abel
  rw [he, map_neg, Finsupp.neg_apply]
  exact Submodule.neg_mem _ (hmatch t α)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_bracket_equation (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j) (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hSR : PolynomialLiftSystem P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V) :
    ∀ t α, ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α) -
        basisGradeProjection (b.baseChange ℝ) w j (coefficients (R t) α)) ∈ V := by
  let Vq := V.restrictScalars ℚ
  let p := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ Vq ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hp : p ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [coefficients_map]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hk1 (t : κ) : k t ∈ F.realification.layer 1 := by
    rw [F.realification.one_eq_top]
    trivial
  have hstep : j - 1 + 2 = j + 1 := by omega
  intro t α
  have hrem : (⁅P.coord - p, monomial (R := ℚ) 0 (k t)⁆ : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
      coefficientSubmodule Vq ⊔ F.realification.polynomialFiltration.layer (j + 1) := by
    apply (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
    intro β
    apply (hW (j + 1) _).mpr
    have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P.coord β) (k t) (hk1 t) (fun d hd => hlower d hd t β)
    rw [hstep] at h
    simpa only [p, coefficients_lie_constant, map_sub, Finsupp.sub_apply,
      coefficients_map, LinearMap.restrictScalars_apply] using h
  have hconst : monomial (R := ℚ) (0 : σ →₀ ℕ) (k t) ∈ F.realification.polynomialFiltration.layer 1 :=
    F.realification.monomial_mem_polynomialLayer 1 0 (hk1 t)
  have h := F.realification.polynomialFiltration.adjoint_current_layer_relation
    (coefficientLieSubalgebra U) (coefficientSubmodule Vq)
    (fun X hX Y hY => coefficientSubmodule_invariant U Vq hUV X Y hX hY)
    hs (by omega) P hPU (R t) (monomial 0 (k t)) p hp hconst
    ((mem_coefficient_sup_polynomialLayer F.realification Vq j _).mpr
      (fun β => (hW j _).mpr (hR t β))) hrem
  rw [← hSR t] at h
  have hc := (hW (j + 1) _).mp
    ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp h α)
  have hscalar : ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (coefficients (S t) α - coefficients (R t) α) ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    simpa only [p, map_sub, Finsupp.sub_apply, coefficients_lie_constant,
      coefficients_map, LinearMap.restrictScalars_apply] using hc
  have hhom : basisGradeProjection (b.baseChange ℝ) w j
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ =
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ := by
    have hh := (hgraded.baseChange b w).projection_lie (b.baseChange ℝ) w
      (basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1}
        (coefficients P.coord α)) (hk t)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hh
    exact hh
  have hproj := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j _ hscalar
  simpa only [map_sub, hhom] using hproj

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_bracket_equation_mod (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j) (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V) :
    ∀ t α, ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α) -
        basisGradeProjection (b.baseChange ℝ) w j (coefficients (R t) α)) ∈ V := by
  obtain ⟨S₀, hS₀, herror⟩ := PolynomialLiftSystemMod.exact_left (V.restrictScalars ℚ) P S R hSR
  have hcurrent := F.formal_current_bracket_equation b w hlayers hgraded hs U V hUV hV
    k hk hj P hPU S₀ R hS₀ hR hlower
  intro t α
  have he := hV j (coefficients (S t - S₀ t) α) (herror t α)
  simp only [map_sub, Finsupp.sub_apply] at he
  have h := V.sub_mem (hcurrent t α) he
  convert h using 1
  abel

include hlayers in
theorem formal_bracket_induction_step_mod (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V)
    (hleft : ∀ t α, coefficients (S t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hright : ∀ t α, coefficients (R t - monomial 0 (k t) + ⁅B.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := fun t => dualAdjoint A⁻¹ (S t)
    let R' := fun t => dualAdjoint B (R t)
    A * P' * B = P ∧ (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ d < j - 1,
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
      (∀ d < j, ∀ t α,
        ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V) ∧
      PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      ∀ t α,
        coefficients (S' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        coefficients (R' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        ⁅coefficients P'.coord α, k t⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' S' R'
  obtain ⟨S₀, hS₀, herror⟩ := PolynomialLiftSystemMod.exact_left (V.restrictScalars ℚ) P S R hSR
  have hleft₀ (t : κ) (α : σ →₀ ℕ) :
      coefficients (S₀ t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem
      (hleft t α) (Submodule.mem_sup_left (herror t α))
    simp only [map_sub, Finsupp.sub_apply] at h ⊢
    convert h using 1
    abel
  have hstep := F.formal_bracket_induction_step b w hlayers hgraded hs U V hUV hV k hk hj
    P A B hPU hAU hBU hA hB S₀ R hS₀ hR hlower hleft₀ hright
  obtain ⟨hprod, hU, hbelow, hbracket, _, hnext⟩ := hstep
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hAU
  refine ⟨hprod, hU, hbelow, hbracket,
    PolynomialLiftSystemMod.remove U (V.restrictScalars ℚ) hUV P A B hAU S R hSR,
    fun t α => ⟨?_, (hnext t α).2.1, (hnext t α).2.2⟩⟩
  have he := dualAdjoint_mem_coefficientSubmodule U (V.restrictScalars ℚ) hUV A⁻¹
    (S t - S₀ t) hAi (herror t)
  have heq : dualAdjoint A⁻¹ (S t) - monomial 0 (k t) =
      dualAdjoint A⁻¹ (S t - S₀ t) + (dualAdjoint A⁻¹ (S₀ t) - monomial 0 (k t)) := by
    rw [dualAdjoint_sub]
    abel
  change coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈ _
  rw [heq, map_add, Finsupp.add_apply]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (he α)) (hnext t α).1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_formal_bracket_step
    (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    {j H J Q l : ℕ} (hj : 2 ≤ j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p) (hcols : (Fintype.card ν : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) ≤ Real.exp p)
    (hMp : (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * M ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (hSgraded : ∀ t, S t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRgraded : ∀ t, R t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hS : ∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hR : ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ)
    (hsmall : ∀ t α, ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ ≤ M / monomialScale T α)
    (hrational : ∀ t α, (b.baseChange ℝ).equivFun (coefficients (R t) α) ∈ realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun t => dualAdjoint A⁻¹ (S t)
      let R' := fun t => dualAdjoint B (R t)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ t α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        ∀ t α,
          coefficients (S' t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let π := (basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ
  let Pd := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  let small := liftQuotientArray f (fun t => VectorPolynomial.map π (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))
  let rational := liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hcurrent := F.formal_current_bracket_equation_mod b w hlayers hgraded hs U (V.baseChange ℝ)
    hUV hV (fun t => (1 : ℝ) ⊗ₜ[ℚ] k t) hk hj P hPU S R hSR hR hlower
  have harr := bracket_array_equation_of_current_relation f k
    (basisGradeProjection (b.baseChange ℝ) w j) Pd S R (fun t α => by
      rw [coefficients_map]
      exact hcurrent t α)
  have hsmallhom := projected_lift_array_homogeneous b w f k hj hk S hSgraded
  have hrhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients rational α = 0 := by
    intro α hα
    change coefficients (liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α = 0
    rw [liftQuotientArray_map_neg, map_neg, Finsupp.neg_apply]
    rw [projected_lift_array_homogeneous b w f k hj hk R hRgraded α hα, neg_zero]
  have hsbound (α : σ →₀ ℕ) : ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α :=
    (projected_lift_array_bound b w f k hj hk hf T hTpos hM S hsmall α).trans
      (div_le_div_of_nonneg_right hMp (monomialScale_pos T hTpos α).le)
  have hrgrid (α : σ →₀ ℕ) : coefficients rational α ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
    change coefficients (liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α ∈ _
    rw [liftQuotientArray_map_neg, map_neg, Finsupp.neg_apply]
    exact realDenominatorGrid_neg _ (projected_lift_array_grid b w f k hj hk l R hrational α)
  have h := F.exists_controlled_bracket_polynomial_step b w hlayers U e f k (hgraded.baseChange b w)
    (by omega : 0 < j - 1) hE hEU hH (Nat.mul_pos (matrixDenominator_pos _) hl)
    hA he hp hrows hcols hHp hlp T hT P.coord Pd hPU hPgraded rfl
    (fun α => by rw [coefficients_map]; exact hPE α) small rational hsmallhom hrhom hsbound hrgrid harr
  obtain ⟨m, a, c, Pnew, hm, hmp, haQ, hcQ, hac, hahom, hchom, hanorm, hcgrid,
    hremove, _, hconstant, hnewgraded, _, _, _⟩ := h
  have hmatching := F.bracket_arrays_match_lifts b w hlayers hV f k j S R a c hS hR haQ hcQ
  have hstep := F.formal_bracket_induction_step_mod b w hlayers hgraded hs U (V.baseChange ℝ) hUV hV
    (fun t => (1 : ℝ) ⊗ₜ[ℚ] k t) hk hj P ⟨a⟩ ⟨c⟩ hPU
    (fun α => hEU _ (hac α).1) (fun α => hEU _ (hac α).2)
    (fun α => hE _ (hac α).1) (fun α => hE _ (hac α).2) S R hSR hR hlower hmatching.1 hmatching.2
  obtain ⟨hprod, hnewU, hbelow, hbrackets, hlifts, hrems⟩ := hstep
  refine ⟨m, ⟨a⟩, ⟨c⟩, hm, hmp, hac, hahom, hchom, hanorm, hcgrid,
    hprod, ?_, ?_, hnewU, hbelow, hbrackets, hlifts, hrems⟩
  · change coefficients (bchRemove s a P.coord c) 0 = coefficients P.coord 0
    rw [← hremove]
    exact hconstant
  · change bchRemove s a P.coord c ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    rw [← hremove]
    exact hnewgraded

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_bracket_step :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (_hk : ∀ z, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k z) = (1 : ℝ) ⊗ₜ[ℚ] k z)
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hquotient : (Fintype.card ι : ℝ) ≤ p)
    (_hkernel : (Fintype.card κ : ℝ) ≤ p) (_hsource : (Fintype.card ν : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSgraded : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hS : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hR : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hlower : ∀ d < j - 1, ∀ z α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ)
    (_hsmall : ∀ z α, ‖(b.baseChange ℝ).equivFun (coefficients (S z) α)‖ ≤ M / monomialScale T α)
    (_hrational : ∀ z α, (b.baseChange ℝ).equivFun (coefficients (R z) α) ∈ realDenominatorGrid l),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈ realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun z => dualAdjoint A⁻¹ (S z)
      let R' := fun z => dualAdjoint B (R z)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ z α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        ∀ z α,
          coefficients (S' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨C, hC, hCbound⟩ := exists_bracket_uniform_budget
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν σ _ _ _ _ _ _ s F b w hF E V hgraded hs U hUV hV e f k hk j H J Q l
    hj hE hEU hH hl hA he hf p M hp hM hambient hquotient hkernel hsource
    hHp hJp hQp hlp hMp T hT P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
  let q := bracketConstructionBudget p
  let r := bracketCorrectionBudget p
  have hq : 0 ≤ q := bracketConstructionBudget_nonneg hp
  have hr : 0 ≤ r := bracketCorrectionBudget_nonneg hp
  obtain ⟨hpq, hrowsq, hdenq, hnormq⟩ := bracket_construction_budget_bounds hp
  have hrows : (Fintype.card (κ × ι) : ℝ) ≤ q := by
    apply le_trans _ hrowsq
    rw [Fintype.card_prod, Nat.cast_mul, pow_two]
    exact mul_le_mul (hkernel.trans (by linarith)) (hquotient.trans (by linarith))
      (Nat.cast_nonneg _) (by linarith)
  have hpplus : Real.exp p ≤ Real.exp ((p + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hquotient hambient (fun i z =>
    (show (((quotientCoordinateMatrix b f i z).den) : ℝ) ≤ Q from Nat.cast_le.mpr (hf i z).2).trans
      (hQp.trans hpplus))
  have hEden := matrixDenominator_le_exp_power (bracketLiftMatrix b e) hp 1 hambient hsource (fun i z =>
    (show (((bracketLiftMatrix b e i z).den) : ℝ) ≤ J from Nat.cast_le.mpr (he i z).2).trans
      (hJp.trans hpplus))
  have hden : ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hD hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdenq
  have hnorm : (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * M ≤ Real.exp q := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul (current_layer_coordinate_factor_bound hp (Fintype.card μ) Q hambient hQp)
          hMp hM (Real.exp_nonneg _)
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hnormq
  have htotal : separationBudget q + r ≤ (p + C) ^ C := hCbound p hp
  have hcut : separationBudget q ≤ (p + C) ^ C := by linarith
  have hout : r ≤ (p + C) ^ C := by linarith [separationBudget_nonneg hq]
  have hTq : ∀ i, Real.exp (separationBudget q) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hcut).trans (hT i)
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  obtain ⟨m, A, B, hm, hmbound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders⟩ :=
    F.exists_controlled_formal_bracket_step b w hF hgraded hs Uq hUV hV e f k hk hj hE hEU
      hH hl hA he hf hq hM hrows (hsource.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
      hden hnorm T hTq P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
  have houtputs := bracket_correction_budget_bounds hp (Fintype.card ν) J
    (matrixDenominator (bracketLiftMatrix b e)) hsource hJp hEden
  let n := matrixDenominator (bracketLiftMatrix b e) * m
  have hnbound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (matrixDenominator (bracketLiftMatrix b e) : ℝ) * (m : ℝ) := Nat.cast_mul _ _
      _ ≤ (matrixDenominator (bracketLiftMatrix b e) : ℝ) * Real.exp ((q + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmbound (Nat.cast_nonneg _)
      _ ≤ Real.exp r := houtputs.2
      _ ≤ _ := Real.exp_le_exp.mpr hout
  refine ⟨n, A, B, Nat.mul_pos (matrixDenominator_pos _) hm, hnbound,
    hAB, hAhom, hBhom, ?_, hBgrid, hprod, hconstant, hnewgraded, hnewU,
    hbelow, hbrackets, hlifts, hremainders⟩
  intro α
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  exact (hAnorm α).trans (div_le_div_of_nonneg_right
    (houtputs.1.trans (Real.exp_le_exp.mpr hout)) (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_controlled_bracket_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (_hk : ∀ z, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k z) = (1 : ℝ) ⊗ₜ[ℚ] k z)
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hquotient : (Fintype.card ι : ℝ) ≤ p)
    (_hkernel : (Fintype.card κ : ℝ) ≤ p) (_hsource : (Fintype.card ν : ℝ) ≤ p)
    (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSgraded : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hS : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hR : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hlower : ∀ d < j - 1, ∀ z α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ)
    (_hsmall : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S z))
    (_hrational : ∀ z, CoefficientGrid (b.baseChange ℝ) l (R z))
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hsmallShift : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hrationalShift : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (_hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈ realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun z => dualAdjoint A⁻¹ (S z)
      let R' := fun z => dualAdjoint B (R z)
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ z α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        (∀ z α,
          coefficients (S' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (S' z) ∧
          CoefficientGrid (b.baseChange ℝ) n (R' z) ∧
          S' z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          R' z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) ∧
          small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 := by
  obtain ⟨D, _, hstage⟩ := exists_uniform_formal_bracket_step
  obtain ⟨E, _, hremove⟩ := exists_formal_derivative_removal_control s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C D) ^ D
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D + (Q + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν σ _ _ _ _ _ _ _ F b w hF Esource V hgraded hs U hUV hV e f k hk
    j H J Qheight l hj hE hEU hH hl hA he hf hstructure p hp
    hambient hquotient hkernel hsource hvariables hHp hJp hQp hlp T hT P hPU hPgraded hPE
    S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
    small rational extra hsystem hsmallShift hrationalShift hsmallBound hrationalGrid
  let d := (p + D) ^ D
  let q := p + d
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hqE : 0 ≤ (q + E) ^ E := by positivity
  have htotal : d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
    simpa [B, Q, q, d, Polynomial.eval₂_pow] using hCbound p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hremCap : (q + E) ^ E ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  obtain ⟨n₀, A, Bcorr, hn₀, hn₀bound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders⟩ :=
    hstage F b w hF hgraded hs U hUV hV e f k hk hj hE hEU hH hl hA he hf hp
      (Real.exp_nonneg p) hambient hquotient hkernel hsource hHp hJp hQp hlp le_rfl
      T hTD P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower
      (fun z => (coefficientBound_iff_norm (b.baseChange ℝ) T hTpos (Real.exp_nonneg p) (S z)).mp (hsmall z))
      hrational
  let Lden := l * n₀
  have hLden : 0 < Lden := Nat.mul_pos hl hn₀
  have hLbound : (Lden : ℝ) ≤ Real.exp q := by
    calc
      _ = (l : ℝ) * (n₀ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp p * Real.exp d := mul_le_mul hlp hn₀bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  obtain ⟨m, hm, hmbound, hLm, hcontrol⟩ := hremove F b w hF hgraded H q hH hq
    (hambient.trans hpq) (hvariables.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    hstructure Lden hLden hLbound
  have hlL : l ∣ Lden := dvd_mul_right l n₀
  have hnL : n₀ ∣ Lden := dvd_mul_left n₀ l
  have hAg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    (j - 1) A.coord hAhom (fun α => hE _ (hAB α).1)
  have hBg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    (j - 1) Bcorr.coord hBhom (fun α => hE _ (hAB α).2)
  have hAraw : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) A.coord).mpr hAnorm
  have hAinput : CoefficientBound (b.baseChange ℝ) T (Real.exp ((q + 2) ^ 1)) A.coord := by
    apply CoefficientBound.mono _ T hTpos hAraw
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    dsimp [q]
    linarith
  have hBinput : CoefficientGrid (b.baseChange ℝ) Lden Bcorr.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hn₀ hnL (hBgrid α)
  have hinputCap : Real.exp p ≤ Real.exp ((q + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  obtain ⟨hboundLifts, hboundDerivative, hshiftLifts, hshiftDerivative⟩ :=
    hcontrol T hTpos A Bcorr hAg hBg hAinput hBinput S R small rational
      hSgraded hRgraded hsmallShift hrationalShift
      (fun z => CoefficientBound.mono _ T hTpos (hsmall z) hinputCap)
      (fun z α => realDenominatorGrid_subset_of_dvd hl hlL (hrational z α))
      (fun i => CoefficientBound.mono _ T hTpos (hsmallBound i)
        (div_le_div_of_nonneg_right hinputCap (hTpos i).le))
      (fun i α => realDenominatorGrid_subset_of_dvd hl hlL (hrationalGrid i α))
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hsystem' := PolynomialDerivativeSystemMod.remove Uq ((V.baseChange ℝ).restrictScalars ℚ)
    hUV P A Bcorr (fun α => hEU _ (hAB α).1) small rational extra hsystem
  have hfinalCap : Real.exp ((q + E) ^ E) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hremCap
  refine ⟨m, A, Bcorr, hm, hmbound.trans hfinalCap, hAB, hAhom, hBhom, ?_, ?_,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders,
    hsystem', ?_, ?_⟩
  · intro α
    exact (hAnorm α).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdCap)
      (monomialScale_pos T hTpos α).le)
  · intro α
    exact realDenominatorGrid_subset_of_dvd hn₀ (dvd_trans hnL hLm) (hBgrid α)
  · intro z
    exact ⟨CoefficientBound.mono _ T hTpos (hboundLifts z).1 hfinalCap,
      (hboundLifts z).2, (hshiftLifts z).1, (hshiftLifts z).2⟩
  · intro i
    exact ⟨CoefficientBound.mono _ T hTpos (hboundDerivative i).1
      (div_le_div_of_nonneg_right hfinalCap (hTpos i).le),
      (hboundDerivative i).2, (hshiftDerivative i).1, (hshiftDerivative i).2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionStage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_induction_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν τ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype τ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K Ebr Ecur : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (eBr : Basis ν ℚ Ebr) (eCur : Basis τ ℚ Ecur)
    (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {j H : ℕ} (_hj : 2 ≤ j) (_hH : 1 ≤ H)
    (_hBrGrade : ∀ x ∈ Ebr.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hBrU : Ebr.baseChange ℝ ≤ U.toSubmodule)
    (_hBrK : j = 2 → Ebr.baseChange ℝ ≤ K.baseChange ℝ)
    (_hBrV : 2 < j → Ebr.baseChange ℝ ≤ V.baseChange ℝ)
    (_hCurGrade : ∀ x ∈ Ecur.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hCurU : Ecur.baseChange ℝ ≤ U.toSubmodule)
    (_hCurProjection : ∀ x ∈ U, basisGradeProjection (b.baseChange ℝ) w j x ∈ Ecur.baseChange ℝ)
    (_hBracketMatrix : ∀ i z, RationalHeightLE (bracketSystemMatrix eBr f (fun z => (eK z : L)) i z) H)
    (_hCurrentMatrix : ∀ i z, RationalHeightLE (subspaceQuotientMatrix eCur f i z) H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hBracketBasis : ∀ i z, RationalHeightLE (b.repr (eBr z : L) i) H)
    (_hCurrentBasis : ∀ i z, RationalHeightLE (b.repr (eCur z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hν : (Fintype.card ν : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T j p)
    (_hBracketSource : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1)
      (coefficients X.P.coord α) ∈ Ebr.baseChange ℝ),
    ∃ (Y : F.FormalInductionState b w U V K eK T (j + 1) ((p + C) ^ C))
      (A₁ A₂ B₁ B₂ : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      (A₁ * A₂) * Y.P * (B₂ * B₁) = X.P ∧
      (∀ α, coefficients A₁.coord α ∈ U ∧ coefficients A₂.coord α ∈ U ∧
        coefficients B₁.coord α ∈ U ∧ coefficients B₂.coord α ∈ U) ∧
      (A₁.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        A₂.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        B₁.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        B₂.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)) ∧
      (coefficients A₁.coord 0 = 0 ∧ coefficients A₂.coord 0 = 0 ∧
        coefficients B₁.coord 0 = 0 ∧ coefficients B₂.coord 0 = 0) ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A₁.coord ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A₂.coord ∧
      CoefficientGrid (b.baseChange ℝ) Y.denominator B₁.coord ∧
      CoefficientGrid (b.baseChange ℝ) Y.denominator B₂.coord := by
  classical
  obtain ⟨D, _, hbracketStage⟩ := exists_uniform_controlled_bracket_stage s
  obtain ⟨E, _, hcurrentStage⟩ := exists_uniform_controlled_current_stage s
  obtain ⟨C, hC, hbudget⟩ := exists_formal_stage_budget D E
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν τ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K Ebr Ecur hUV hV
    eK eBr eCur f hK j H hj hH hBrGrade hBrU hBrK hBrV hCurGrade hCurU hCurProjection
    hBracketMatrix hCurrentMatrix hKernelBasis hBracketBasis hCurrentBasis hQuotient hStructure
    p hp hμ hι hκ hν hτ hσ hjp hHp T hT X hBracketSource
  let d := (p + D) ^ D
  let t := p + d
  let u := bracketTransitionBudget t
  let v := bracketConstructionBudget u
  let q := u + v
  let z := (q + E) ^ E
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hu : 0 ≤ u := bracketTransitionBudget_nonneg ht
  have hv : 0 ≤ v := bracketConstructionBudget_nonneg hu
  have hq : 0 ≤ q := add_nonneg hu hv
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right hd
  have htu : t ≤ u := le_bracketTransitionBudget ht
  have huv : u ≤ v := (bracket_construction_budget_bounds hu).1
  have huq : u ≤ q := le_add_of_nonneg_right hv
  have hvq : v ≤ q := le_add_of_nonneg_left hu
  have hpu : p ≤ u := hpt.trans htu
  have hpq : p ≤ q := hpu.trans huq
  have hcap : d + z + 1 ≤ (p + C) ^ C := hbudget p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hzCap : z ≤ (p + C) ^ C := by linarith
  have hsumCap : d + z ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  have hk (r : κ) : basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] (eK r : L)) =
      (1 : ℝ) ⊗ₜ[ℚ] (eK r : L) := by
    have h := hK _ (bracketSystemLift_mem eK (Pi.single r 1))
    rw [bracketSystemLift_single] at h
    exact h
  obtain ⟨n₀, A₁, B₁, hn₀, hn₀bound, hAB₁, hAhom₁, hBhom₁, hAnorm₁, hBgrid₁,
    hprod₁, hconstant₁, hgraded₁, hU₁, hbelow₁, hbrackets₁, hlifts₁, hrems₁,
    hrawSystem, hliftControls₁, hderivControls₁⟩ :=
    hbracketStage F b w hF hgraded hs U hUV hV eBr f (fun r => (eK r : L)) hk hj
      hBrGrade hBrU hH X.denominator_pos hBracketMatrix hBracketBasis hQuotient hStructure hp
      hμ hι hκ hν hσ hHp hHp hHp X.denominator_bound T hTD X.P X.mem_U X.graded
      hBracketSource X.S X.R X.lift_system X.S_shift X.R_shift X.S_remainder X.R_remainder
      X.lower_bracket X.S_bound X.R_grid X.small X.rational
      (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) X.S (X.k i)) X.derivative_system
      X.small_shift X.rational_shift X.small_bound X.rational_grid
  let P₁ := A₁⁻¹ * X.P * B₁⁻¹
  let S₁ := fun r => dualAdjoint A₁⁻¹ (X.S r)
  let R₁ := fun r => dualAdjoint B₁ (X.R r)
  have hA₁bound : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A₁.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) _).mpr hAnorm₁
  have hdt : d ≤ t := le_add_of_nonneg_left hp
  have hExpdt : Real.exp d ≤ Real.exp t := Real.exp_le_exp.mpr hdt
  obtain ⟨a, c, n₁, hn₁, hn₁bound, hmidU, hmidK, hmidLower, hmidLift,
    hmidSystem, hmidRemainders, hmidExtra, hmidEquation, hmidBracket, hmidControls, hmidLiftControls⟩ :=
    F.exists_controlled_bracket_to_current_layer b w hF hs U (V.baseChange ℝ) hUV hV eK hK
      hj hH hn₀ hKernelBasis ht (hμ.trans hpt) (hκ.trans hpt)
      (hHp.trans (Real.exp_le_exp.mpr hpt)) (hn₀bound.trans hExpdt) T hTpos X.P A₁ B₁
      X.mem_U (fun α => hBrU (hAB₁ α).1) (fun α => hBrU (hAB₁ α).2)
      (fun α => hBrGrade _ (hAB₁ α).1) (fun α => hBrGrade _ (hAB₁ α).2)
      hAhom₁ hBhom₁ (fun h α => hBrK h (hAB₁ α).1) (fun h α => hBrK h (hAB₁ α).2)
      (fun h α => hBrV h (hAB₁ α).1) (fun h α => hBrV h (hAB₁ α).2)
      X.horizontal X.lower_log X.S X.R X.small X.rational X.k X.lift_system X.derivative_system
      X.small_remainder X.rational_remainder (fun r α => (hrems₁ r α).1)
      (fun r α => (hrems₁ r α).2.1) (fun r α => (hrems₁ r α).2.2)
      (hA₁bound.mono _ T hTpos hExpdt) hBgrid₁
      (fun r => (hliftControls₁ r).1.mono _ T hTpos hExpdt)
      (fun r => (hliftControls₁ r).2.1)
      (fun i => (hderivControls₁ i).1.mono _ T hTpos
        (div_le_div_of_nonneg_right hExpdt (hTpos i).le))
      (fun i => (hderivControls₁ i).2.1)
      (fun r => (hliftControls₁ r).2.2.1) (fun r => (hliftControls₁ r).2.2.2)
      (fun i => (hderivControls₁ i).2.2.1) (fun i => (hderivControls₁ i).2.2.2)
  let Smap₁ := (dualAdjointAddEquiv A₁⁻¹).toAddMonoidHom.comp
    (basisPolynomialLift (Pi.basisFun ℝ κ) X.S).toAddMonoidHom
  let Rmap₁ := (dualAdjointAddEquiv B₁).toAddMonoidHom.comp
    (basisPolynomialLift (Pi.basisFun ℝ κ) X.R).toAddMonoidHom
  let small₁ := fun i => dualAdjoint A₁⁻¹ (X.small i - formalLogDerivative i A₁) +
    if j = 2 then Smap₁ (a i) else 0
  let rational₁ := fun i => dualAdjoint B₁ (X.rational i) - formalLogDerivative i B₁ +
    if j = 2 then Rmap₁ (c i) else 0
  let k₁ := fun i => if j = 2 then X.k i - a i - c i else X.k i
  let extra₁ := fun i => Smap₁ (k₁ i)
  have hHpu : (H : ℝ) ≤ Real.exp u := hHp.trans (Real.exp_le_exp.mpr hpu)
  obtain ⟨nQ, hnQ, hnQbound, hprojectedBound, hprojectedGrid⟩ :=
    uniform_current_layer_inputs_from_ambient b w f j hn₁ hQuotient hu
      (hμ.trans hpu) (hι.trans hpu) hHpu hn₁bound T hTpos small₁ rational₁
      (fun i => (hmidControls i).1) (fun i => (hmidControls i).2.1)
  let nInput := n₁ * nQ
  have hnInput : 0 < nInput := Nat.mul_pos hn₁ hnQ
  have hn₁Input : n₁ ∣ nInput := dvd_mul_right n₁ nQ
  have hnQInput : nQ ∣ nInput := dvd_mul_left nQ n₁
  have hInputBound : (nInput : ℝ) ≤ Real.exp q := by
    calc
      _ = (n₁ : ℝ) * (nQ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp u * Real.exp v := mul_le_mul hn₁bound hnQbound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  have hTE : ∀ i, Real.exp ((q + E) ^ E) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hzCap).trans (hT i)
  have hHq : (H : ℝ) ≤ Real.exp q := hHp.trans (Real.exp_le_exp.mpr hpq)
  have hEuq : Real.exp u ≤ Real.exp q := Real.exp_le_exp.mpr huq
  have hP₁cur : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P₁.coord α) ∈ Ecur.baseChange ℝ :=
    fun α => hCurProjection _ (hmidU α)
  obtain ⟨n₂, A₂, B₂, hn₂, hn₂bound, hAB₂, hAhom₂, hBhom₂, hAnorm₂, hBgrid₂,
    hprod₂, hconstant₂, hgraded₂, hU₂, hcurrent₂, hbelow₂, hsystem₂, hshift₂,
    hremainders₂, hK₂, hlower₂, hbracket₂, hextra₂, hlifts₂, hliftRemainders₂,
    hliftControls₂, hderivControls₂⟩ :=
    hcurrentStage F b w hF hgraded hs U (K.baseChange ℝ) hUV hV eCur f hj hCurGrade hCurU
      hH hnInput hCurrentMatrix hCurrentBasis hQuotient hStructure hq (Real.exp_nonneg v)
      (hμ.trans hpq) (hι.trans hpq) (hτ.trans hpq) (hσ.trans hpq) (hjp.trans hpq)
      hHq hHq hHq hInputBound (Real.exp_le_exp.mpr hvq) T hTE P₁
      hmidU hgraded₁ hP₁cur hmidK hmidLower hmidBracket small₁ rational₁ extra₁
      (fun i α => (hmidRemainders i α).1) (fun i α => (hmidRemainders i α).2)
      hmidExtra hmidSystem (fun i => (hmidControls i).2.2.1) (fun i => (hmidControls i).2.2.2)
      hprojectedBound (fun i α => realDenominatorGrid_subset_of_dvd hnQ hnQInput (hprojectedGrid i α))
      S₁ R₁ (fun r => (1 : ℝ) ⊗ₜ[ℚ] (eK r : L))
      (fun r => (hliftControls₁ r).2.2.1) (fun r => (hliftControls₁ r).2.2.2)
      hlifts₁ (fun r α => (hrems₁ r α).1) (fun r α => (hrems₁ r α).2.1)
      (fun r => (hmidLiftControls r).1.mono _ T hTpos hEuq)
      (fun r α => realDenominatorGrid_subset_of_dvd hn₁ hn₁Input ((hmidLiftControls r).2 α))
      (fun i => (hmidControls i).1.mono _ T hTpos (div_le_div_of_nonneg_right hEuq (hTpos i).le))
      (fun i α => realDenominatorGrid_subset_of_dvd hn₁ hn₁Input ((hmidControls i).2.1 α))
  let P₂ := A₂⁻¹ * P₁ * B₂⁻¹
  let S₂ := fun r => dualAdjoint A₂⁻¹ (S₁ r)
  let R₂ := fun r => dualAdjoint B₂ (R₁ r)
  let small₂ := fun i => dualAdjoint A₂⁻¹ (small₁ i - formalLogDerivative i A₂)
  let rational₂ := fun i => dualAdjoint B₂ (rational₁ i) - formalLogDerivative i B₂
  let n := n₀ * n₂
  have hn : 0 < n := Nat.mul_pos hn₀ hn₂
  have hn₀n : n₀ ∣ n := dvd_mul_right n₀ n₂
  have hn₂n : n₂ ∣ n := dvd_mul_left n₂ n₀
  have hnBound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (n₀ : ℝ) * (n₂ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp d * Real.exp z := mul_le_mul hn₀bound hn₂bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (d + z) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsumCap
  have hEz : Real.exp z ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hzCap
  have hS₁eval (x : κ → ℝ) : basisPolynomialLift (Pi.basisFun ℝ κ) S₁ x = Smap₁ x := by
    rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
      (Pi.basisFun ℝ κ) A₁⁻¹ X.S]
    rfl
  have hextraEq : (fun i => dualAdjoint A₂⁻¹ (extra₁ i)) =
      fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S₂ (k₁ i) := by
    funext i
    rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
      (Pi.basisFun ℝ κ) A₂⁻¹ S₁]
    change dualAdjoint A₂⁻¹ (Smap₁ (k₁ i)) =
      dualAdjoint A₂⁻¹ (basisPolynomialLift (Pi.basisFun ℝ κ) S₁ (k₁ i))
    rw [hS₁eval]
  have hsystemFinal : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ)
      P₂ small₂ rational₂ (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S₂ (k₁ i)) := by
    rw [← hextraEq]
    exact hsystem₂
  have hbracketsFinal : ∀ r < (j + 1) - 1, ∀ i α,
      ⁅basisGradeProjection (b.baseChange ℝ) w r (coefficients P₂.coord α),
        (1 : ℝ) ⊗ₜ[ℚ] (eK i : L)⁆ ∈ V.baseChange ℝ := by
    intro r hr i α
    have hrj : r < j := by omega
    have heq := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) (hbelow₂ r hrj)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at heq
    rw [heq]
    exact hbrackets₁ r hrj i α
  let Y : F.FormalInductionState b w U V K eK T (j + 1) ((p + C) ^ C) := {
    P := P₂
    S := S₂
    R := R₂
    small := small₂
    rational := rational₂
    k := k₁
    denominator := n
    denominator_pos := hn
    denominator_bound := hnBound
    constant_zero := hconstant₂.trans (hconstant₁.trans X.constant_zero)
    mem_U := hU₂
    graded := hgraded₂
    horizontal := hK₂
    lower_log := hlower₂
    lower_bracket := hbracketsFinal
    lift_system := hlifts₂
    derivative_system := hsystemFinal
    S_shift := fun r => (hliftControls₂ r).2.2.1
    R_shift := fun r => (hliftControls₂ r).2.2.2
    small_shift := fun i => (hshift₂ i).1
    rational_shift := fun i => (hshift₂ i).2
    S_remainder := fun r α => (hliftRemainders₂ r α).1
    R_remainder := fun r α => (hliftRemainders₂ r α).2
    small_remainder := fun i α => (hremainders₂ i α).1
    rational_remainder := fun i α => (hremainders₂ i α).2
    S_bound := fun r => (hliftControls₂ r).1.mono _ T hTpos hEz
    R_grid := fun r α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n ((hliftControls₂ r).2.1 α)
    small_bound := fun i => (hderivControls₂ i).1.mono _ T hTpos
      (div_le_div_of_nonneg_right hEz (hTpos i).le)
    rational_grid := fun i α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n ((hderivControls₂ i).2 α) }
  refine ⟨Y, A₁, A₂, B₁, B₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (A₁ * A₂) * P₂ * (B₂ * B₁) = X.P
    calc
      _ = A₁ * (A₂ * P₂ * B₂) * B₁ := by group
      _ = A₁ * P₁ * B₁ := by rw [hprod₂]
      _ = X.P := hprod₁
  · intro α
    exact ⟨hBrU (hAB₁ α).1, hCurU (hAB₂ α).1, hBrU (hAB₁ α).2, hCurU (hAB₂ α).2⟩
  · exact ⟨homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        (j - 1) A₁.coord hAhom₁ (fun α => hBrGrade _ (hAB₁ α).1),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        j A₂.coord hAhom₂ (fun α => hCurGrade _ (hAB₂ α).1),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        (j - 1) B₁.coord hBhom₁ (fun α => hBrGrade _ (hAB₁ α).2),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        j B₂.coord hBhom₂ (fun α => hCurGrade _ (hAB₂ α).2)⟩
  · have hzero₁ : Finsupp.weight (fun _ : σ => (1 : ℕ)) (0 : σ →₀ ℕ) ≠ j - 1 := by simp only [map_zero]; omega
    have hzero₂ : Finsupp.weight (fun _ : σ => (1 : ℕ)) (0 : σ →₀ ℕ) ≠ j := by simp only [map_zero]; omega
    exact ⟨hAhom₁ 0 hzero₁, hAhom₂ 0 hzero₂, hBhom₁ 0 hzero₁, hBhom₂ 0 hzero₂⟩
  · exact hA₁bound.mono _ T hTpos (Real.exp_le_exp.mpr hdCap)
  · have hA₂bound : CoefficientBound (b.baseChange ℝ) T (Real.exp z) A₂.coord :=
      (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) _).mpr hAnorm₂
    exact hA₂bound.mono _ T hTpos hEz
  · exact fun α => realDenominatorGrid_subset_of_dvd hn₀ hn₀n (hBgrid₁ α)
  · exact fun α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n (hBgrid₂ α)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UniformFormalInductionIteration
namespace OAI

section

namespace Erdos3

noncomputable def formalIterationBudget (C : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => (formalIterationBudget C p n + C) ^ C

@[simp] theorem formalIterationBudget_zero (C : ℕ) (p : ℝ) : formalIterationBudget C p 0 = p := rfl

@[simp] theorem formalIterationBudget_succ (C : ℕ) (p : ℝ) (n : ℕ) :
    formalIterationBudget C p (n + 1) = (formalIterationBudget C p n + C) ^ C := rfl

theorem formalIterationBudget_nonneg (C : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 ≤ formalIterationBudget C p n := by
  induction n with
  | zero => exact hp
  | succ n ih => exact pow_nonneg (add_nonneg ih (Nat.cast_nonneg C)) C

theorem formalIterationBudget_monotone {C : ℕ} (hC : 2 ≤ C) {p : ℝ} (hp : 0 ≤ p) :
    Monotone (formalIterationBudget C p) := by
  apply monotone_nat_of_le_succ
  intro n
  have hn := formalIterationBudget_nonneg C hp n
  have hCr : (2 : ℝ) ≤ C := Nat.cast_le.mpr hC
  calc
    formalIterationBudget C p n ≤ formalIterationBudget C p n + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
    _ ≤ (formalIterationBudget C p n + C) ^ C := by
      simpa only [pow_one] using pow_le_pow_right₀
        (by linarith : (1 : ℝ) ≤ formalIterationBudget C p n + C) (show 1 ≤ C by omega)

theorem formalIterationBudget_ge {C : ℕ} (hC : 2 ≤ C) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p ≤ formalIterationBudget C p n := formalIterationBudget_monotone hC hp (Nat.zero_le n)

noncomputable def formalIterationPolynomial (C : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | n + 1 => (formalIterationPolynomial C n + Polynomial.C C) ^ C

theorem formalIterationPolynomial_eval (C n : ℕ) (p : ℝ) :
    (formalIterationPolynomial C n).eval₂ (Nat.castRingHom ℝ) p = formalIterationBudget C p n := by
  induction n with
  | zero => simp [formalIterationPolynomial]
  | succ n ih => simp [formalIterationPolynomial, Polynomial.eval₂_pow, ih]

theorem exists_formal_iteration_uniform_budget (C n : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (n + 1 : ℝ) * formalIterationBudget C p n ≤ (p + D) ^ D := by
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_eval_budget
    (Polynomial.C (n + 1) * formalIterationPolynomial C n)
  refine ⟨D, hD, fun p hp => ?_⟩
  have h := hbound p hp
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, formalIterationPolynomial_eval] at h
  change ((n + 1 : ℕ) : ℝ) * formalIterationBudget C p n ≤ (p + D) ^ D at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_induction_iteration (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s → FormalStageGeometry b w U V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp (formalIterationBudget C p (s - 1)) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    Nonempty (F.FormalInductionRun b w U V K eK T X.P (s - 1)
      (formalIterationBudget C p (s - 1))) := by
  classical
  obtain ⟨C, hC, hstage⟩ := exists_formal_induction_stage s
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hrun : ∀ r, r ≤ s - 1 →
      Nonempty (F.FormalInductionRun b w U V K eK T X.P r (formalIterationBudget C p r)) := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨FormalInductionRun.start X⟩
    | succ r ih =>
      intro hr
      obtain ⟨W⟩ := ih (by omega)
      have hj : 2 ≤ 2 + r := by omega
      have hjs : 2 + r ≤ s := by omega
      let g := G (2 + r) hj hjs
      have hpq : p ≤ formalIterationBudget C p r := formalIterationBudget_ge hC hp r
      have hq : 0 ≤ formalIterationBudget C p r := formalIterationBudget_nonneg C hp r
      have hnext : formalIterationBudget C p r ≤ formalIterationBudget C p (r + 1) :=
        formalIterationBudget_monotone hC hp (Nat.le_succ r)
      have hcutoff : ∀ i, Real.exp ((formalIterationBudget C p r + C) ^ C) ≤ T i := by
        intro i
        exact (Real.exp_le_exp.mpr (formalIterationBudget_monotone hC hp hr)).trans (hT i)
      have hν : (Fintype.card (Fin g.bracketRank) : ℝ) ≤ formalIterationBudget C p r := by
        simpa only [Fintype.card_fin] using (hRanks (2 + r) hj hjs).1.trans hpq
      have hτ : (Fintype.card (Fin g.currentRank) : ℝ) ≤ formalIterationBudget C p r := by
        simpa only [Fintype.card_fin] using (hRanks (2 + r) hj hjs).2.trans hpq
      have hjp : ((2 + r : ℕ) : ℝ) ≤ formalIterationBudget C p r :=
        (Nat.cast_le.mpr hjs).trans (hsp.trans hpq)
      obtain ⟨Y, A₁, A₂, B₁, B₂, hfactor, hmem, hdeg, hzero,
        hA₁bound, hA₂bound, hB₁grid, hB₂grid⟩ :=
        hstage F b w hF hgraded hs U V K g.bracketSpace g.currentSpace hUV hV
          eK g.bracketBasis g.currentBasis f hK hj hH
          g.bracket_grade g.bracket_U g.bracket_K g.bracket_V
          g.current_grade g.current_U g.current_projection
          g.bracket_matrix_height g.current_matrix_height hKernelBasis
          g.bracket_basis_height g.current_basis_height hQuotient hStructure hq
          (hμ.trans hpq) (hι.trans hpq) (hκ.trans hpq) hν hτ (hσ.trans hpq) hjp
          (hHp.trans (Real.exp_le_exp.mpr hpq)) T hcutoff W.state
          (W.state.bracket_source g hU hj)
      exact ⟨W.extend hnext hTpos Y A₁ A₂ B₁ B₂ hfactor
        ⟨fun α => (hmem α).1, hdeg.1, hzero.1⟩
        ⟨fun α => (hmem α).2.1, hdeg.2.1, hzero.2.1⟩
        ⟨fun α => (hmem α).2.2.1, hdeg.2.2.1, hzero.2.2.1⟩
        ⟨fun α => (hmem α).2.2.2, hdeg.2.2.2, hzero.2.2.2⟩
        hA₁bound hA₂bound hB₁grid hB₂grid⟩
  exact hrun (s - 1) le_rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_induction_iteration (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧
    ∀ {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s → FormalStageGeometry b w U V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + D) ^ D) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    ∃ q : ℝ, p ≤ q ∧ 0 ≤ q ∧ q ≤ (p + D) ^ D ∧
      ∃ W : F.FormalInductionRun b w U V K eK T X.P (s - 1) q,
        (W.denominator : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hiteration⟩ := exists_formal_induction_iteration s
  obtain ⟨D, hD, hbudget⟩ := exists_formal_iteration_uniform_budget C (s - 1)
  refine ⟨D, hD, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  let q := formalIterationBudget C p (s - 1)
  have hpq : p ≤ q := formalIterationBudget_ge hC hp (s - 1)
  have hq : 0 ≤ q := formalIterationBudget_nonneg C hp (s - 1)
  have htotal : ((s - 1 : ℕ) + 1 : ℝ) * q ≤ (p + D) ^ D := hbudget p hp
  have hqcap : q ≤ (p + D) ^ D := by
    have hmul := mul_nonneg (Nat.cast_nonneg (s - 1) : (0 : ℝ) ≤ (s - 1 : ℕ)) hq
    nlinarith
  have hT' : ∀ i, Real.exp (formalIterationBudget C p (s - 1)) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hqcap).trans (hT i)
  obtain ⟨W⟩ := hiteration F b w hF hgraded hs U V K hUV hU hV eK f hK hH G
    hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T hT' X
  exact ⟨q, hpq, hq, hqcap, W, W.denominator_bound.trans (Real.exp_le_exp.mpr htotal)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end


