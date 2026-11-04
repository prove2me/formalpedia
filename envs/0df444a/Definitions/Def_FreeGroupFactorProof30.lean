-- Prove2me | Definitions.Def_FreeGroupFactorProof30
-- name    : FreeGroupFactorProof30
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T05:01:15.17725+00:00
-- url     : https://prove2.me/theorems/1359693a-0906-4222-8edc-afe596236729
-- title:
--   Free group factors: supporting development, part 30
-- statement:
--   Part 30 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof29

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

theorem bounded_flow (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K) :
    ∃ U : ℝ → ι → unitary (Ambient ι κ),
      U 0 = (fun i => generatorUnitary (some (Sum.inl i) : Option (ι ⊕ κ))) ∧
      (∀ t, HasDerivAt (fun t i => (U t i : Ambient ι κ))
        (PolynomialFlow.field (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)
          h (fun i => (U t i : Ambient ι κ))) t) ∧
      (∀ t k, ‖hamiltonianLinear
        (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) (U t) k‖ ≤
          3*K*Real.sqrt (k.sum (fun _ r => r^2))) ∧
      ∃ β : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
        (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
          (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) β ∧
        ∀ g, β (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨tuple (fun i => (U 1 i : Ambient ι κ)) j,
            tuple_unitary _ (fun i => (U 1 i).property) j⟩) (generatorUnitary none)) g := by
  obtain ⟨X,hX₀,hX,hU⟩ := basis_solution (ι := ι) (κ := κ) h l hS
  let U (t : ℝ) : ι → unitary (Ambient ι κ) := fun i => ⟨X t i,hU t i⟩
  refine ⟨U,?_,hX,?_,?_⟩
  · funext i
    exact Subtype.ext (congrFun hX₀ i)
  · exact bounded_solution (ι := ι) (κ := κ) h l h0 hS K hK hn X hU hX₀ hX
  · exact extension_at_time (ι := ι) (κ := κ) h l hS X hU hX₀ hX 1

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem wordHom_active (w : FreeGroup ι) :
    wordHom (fun i => generatorUnitary (some (Sum.inl i) : Option (ι ⊕ κ))) w =
      groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w) := by
  rw [← wordHom_generatorUnitary,wordHom_map]
  rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem wordHom_tuple_active (U : ι → unitary (Ambient ι κ)) (w : FreeGroup ι) :
    wordHom (extendUnitary (fun j => ⟨tuple (fun i => (U i : Ambient ι κ)) j,
      tuple_unitary _ (fun i => (U i).property) j⟩) (generatorUnitary none))
          (FreeGroup.map (fun i => some (Sum.inl i)) w) = wordHom U w := by
  rw [wordHom_map]
  rfl

omit [DecidableEq κ] in
theorem displacements_from_bounds
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)) (K : ℝ)
    (U : ℝ → ι → unitary (Ambient ι κ))
    (hU₀ : U 0 = fun j => generatorUnitary (some (Sum.inl j) : Option (ι ⊕ κ)))
    (hX : ∀ t, HasDerivAt (fun t j => (U t j : Ambient ι κ))
      (PolynomialFlow.field (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h
        (fun j => (U t j : Ambient ι κ))) t)
    (hbound : ∀ t k, ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) (U t) k‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2))) :
    (∀ j, ‖(U 1 j : Ambient ι κ) - groupUnitary (FreeGroup.of (some (Sum.inl j)))‖ ≤
      3*K*Real.sqrt ((h j).sum (fun _ r => r^2))) ∧
    ∀ w : FreeGroup ι, ‖wordHom (U 1) w - NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) *
      groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)‖ ≤
      3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  constructor
  · intro j
    have hd := generator_displacement (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h U hX
      (fun j => 3*K*Real.sqrt ((h j).sum (fun _ r => r^2)))
      (fun t j => hbound t (h j)) j
    rw [hU₀] at hd
    exact hd
  · intro w
    have hd := word_displacement (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) hS h U hX w
      (3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)))
      (fun t => hbound t (freeCocycle h w - Finsupp.single 1 1))
    rwa [hU₀, wordHom_active] at hd

end

open UnitaryEvaluation

end FreeGroupFactorMain.FiniteActive

end

end OAI
end


