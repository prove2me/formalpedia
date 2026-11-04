-- Prove2me | Definitions.Def_FreeGroupFactorProof29
-- name    : FreeGroupFactorProof29
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:52:04.635705+00:00
-- url     : https://prove2.me/theorems/b9fa5250-b387-47ae-b267-80d62bd31c82
-- title:
--   Free group factors: supporting development, part 29
-- statement:
--   Part 29 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof28

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

theorem extension_at_time {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) (t : ℝ) :
    ∃ Φ : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
        (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
          (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) Φ ∧
        ∀ g, Φ (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
            (generatorUnitary none)) g := by
  exact iso_extension_of_haar_total
    (wordHom (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
      (generatorUnitary none)))
    (fun g => (wordHom_inv _ g).symm)
    (moments h l hS X hU hX₀ hX t)
    (orbit_total h l hS X hU hX₀ hX t)

theorem basis_solution {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)) :
    ∃ (X : ℝ → ι → Ambient ι κ),
      X 0 = (fun i => groupUnitary (FreeGroup.of (some (Sum.inl i)))) ∧
      (∀ t, HasDerivAt X (PolynomialFlow.field
        (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) ∧
      ∀ t i, X t i ∈ unitary (Ambient ι κ) := by
  exact PolynomialFlow.global_unitary_solution (A := Ambient ι κ)
    (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) hS h
    (fun i => groupUnitary (FreeGroup.of (some (Sum.inl i)))) (fun _ => groupUnitary_mem_unitary _)

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

theorem hamiltonianLinear_mapDomain (S : A) (U : κ → unitary A)
    (f : ι → κ) (k : FreeGroup ι →₀ ℝ) :
    hamiltonianLinear S U (Finsupp.mapDomain (FreeGroup.map f) k) =
      hamiltonianLinear S (U ∘ f) k := by
  classical
  simp only [hamiltonianLinear,Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index (fun g => by simp)
    (fun g a b => by simp [add_smul])]
  apply Finsupp.sum_congr
  intro g hg
  rw [wordHom_map]

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] in
theorem flow_bound (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K)
    (U : ι → unitary (Ambient ι κ))
    (Φ : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ)
    (hΦ : ∀ g, Φ (groupUnitary g) = wordHom
      (extendUnitary (fun j => ⟨tuple (fun i => (U i : Ambient ι κ)) j,
        tuple_unitary _ (fun i => (U i).property) j⟩) (generatorUnitary none)) g)
    (k : FreeGroup ι →₀ ℝ) :
    ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) U k‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  let V : (ι ⊕ κ) → unitary (Ambient ι κ) := fun j =>
    ⟨tuple (fun i => (U i : Ambient ι κ)) j,tuple_unitary _ (fun i => (U i).property) j⟩
  have hb := flow_iso_hamiltonian_bound l h0 hS K hK hn V Φ hΦ
    (Finsupp.mapDomain (FreeGroup.map Sum.inl) k)
  rw [hamiltonianLinear_mapDomain,
    Finsupp.sum_mapDomain_index_inj (FreeGroup.map_injective Sum.inl_injective)] at hb
  exact hb

theorem bounded_solution (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K)
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) :
    ∀ t k, ‖hamiltonianLinear
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)
        (fun i => ⟨X t i,hU t i⟩) k‖ ≤ 3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  intro t k
  obtain ⟨Φ,_ht,_hc,hΦ⟩ := extension_at_time (ι := ι) (κ := κ) h l hS X hU hX₀ hX t
  exact flow_bound (ι := ι) (κ := κ) l h0 hS K hK hn (fun i => ⟨X t i,hU t i⟩) Φ hΦ k

end

open UnitaryEvaluation

end FreeGroupFactorMain.FiniteActive

end

end OAI
end


