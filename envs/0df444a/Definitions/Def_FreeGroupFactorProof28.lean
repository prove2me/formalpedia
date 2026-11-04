-- Prove2me | Definitions.Def_FreeGroupFactorProof28
-- name    : FreeGroupFactorProof28
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:42:30.850767+00:00
-- url     : https://prove2.me/theorems/e4b36e11-ab94-4f12-913f-ee079516a2ca
-- title:
--   Free group factors: supporting development, part 28
-- statement:
--   Part 28 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof27

set_option linter.all false

section
namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
open scoped ENNReal
 theorem original_generators_mem {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t)
    (E : StarSubalgebra ℂ (Ambient ι κ)) (hE : IsClosed (E : Set (Ambient ι κ)))
    (hC : (generatorUnitary (none : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E)
    (t₀ : ℝ) (hXt : ∀ i, X t₀ i ∈ E)
    (hpass : ∀ k : κ, (generatorUnitary (some (Sum.inr k) : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E) :
    ∀ i : Option (ι ⊕ κ), (generatorUnitary i : Ambient ι κ) ∈ E := by
  have hXS := PolynomialFlow.solution_mem_subalgebra E hE
    (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) hS
    (laurentValue_mem E _ hC l) h X hX hU t₀ hXt
  intro i
  cases i with
  | none => exact hC
  | some j =>
    cases j with
    | inl i =>
      change groupUnitary (FreeGroup.of (some (Sum.inl i))) ∈ E
      simpa only [hX₀] using hXS 0 i
    | inr k => exact hpass k

 theorem orbit_total {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option (ι ⊕ κ))))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some (Sum.inl j))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) (t₀ : ℝ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g : FreeGroup (Option (ι ⊕ κ)) =>
      ((wordHom (extendUnitary (fun j => ⟨tuple (X t₀) j,tuple_unitary (X t₀) (hU t₀) j⟩)
        (generatorUnitary none)) g : groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))) :
          GroupOperator (FreeGroup (Option (ι ⊕ κ)))) deltaOne))).topologicalClosure := by
  classical
  let U := extendUnitary (fun j => ⟨tuple (X t₀) j,tuple_unitary (X t₀) (hU t₀) j⟩) (generatorUnitary none)
  let ρ : FreeGroup (Option (ι ⊕ κ)) →* GroupOperator (FreeGroup (Option (ι ⊕ κ))) :=
    (groupVonNeumann _).subtype.toMonoidHom.comp (wordHom U)
  let K := (Submodule.span ℂ (Set.range (fun g => ρ g deltaOne))).topologicalClosure
  let E := (reducingAlgebra K).comap (groupVonNeumann _).subtype
  have hK : IsClosed (K : Set (GroupHilbert (FreeGroup (Option (ι ⊕ κ))))) :=
    Submodule.isClosed_topologicalClosure _
  have hE : IsClosed (E : Set (groupVonNeumann (FreeGroup (Option (ι ⊕ κ))))) :=
    (reducingAlgebra_isClosed K hK).preimage continuous_subtype_val
  have hρ (g) : wordHom U g ∈ E := by
    constructor
    · exact closedSpan_invariant ρ deltaOne g
    · have he : star (ρ g) = ρ g⁻¹ := by
        change ((star (wordHom U g) : groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))) :
          GroupOperator (FreeGroup (Option (ι ⊕ κ)))) = _
        rw [← wordHom_inv]
        rfl
      change ∀ x ∈ K, (star (ρ g)) x ∈ K
      rw [he]
      exact closedSpan_invariant ρ deltaOne g⁻¹
  have hC : (generatorUnitary (none : Option (ι ⊕ κ)) : groupVonNeumann _) ∈ E := by
    simpa only [wordHom_of, U, extendUnitary, Option.elim_none] using hρ (FreeGroup.of none)
  have hXt : ∀ j, X t₀ j ∈ E := by
    intro j
    simpa only [wordHom_of, U, extendUnitary, Option.elim_some,tuple,Sum.elim_inl] using hρ (FreeGroup.of (some (Sum.inl j)))
  have hpass (k : κ) : (generatorUnitary (some (Sum.inr k) : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E := by
    change groupUnitary (FreeGroup.of (some (Sum.inr k))) ∈ E
    simpa only [wordHom_of,U,extendUnitary,Option.elim_some,tuple,Sum.elim_inr]
      using hρ (FreeGroup.of (some (Sum.inr k)))
  have hgen := original_generators_mem h l hS X hU hX₀ hX E hE hC t₀ hXt hpass
  change ⊤ ≤ K
  apply canonical_total_of_reducing K hK _ hgen
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

end
open UnitaryEvaluation

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

end

open UnitaryEvaluation

end FreeGroupFactorMain.FiniteActive

end

end OAI
end


