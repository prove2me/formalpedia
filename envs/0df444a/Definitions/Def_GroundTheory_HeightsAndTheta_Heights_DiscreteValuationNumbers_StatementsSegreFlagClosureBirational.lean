-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:07.350068+00:00
-- url     : https://prove2.me/theorems/f0b91eac-6c6a-4851-b0dc-487d244670fc
-- title:
--   Statements Segre Flag Closure Birational
-- statement:
--   Definitions and structural lemmas for Statements Segre Flag Closure Birational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSegreFlagClosureBirational.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
abbrev lineBlocks (M M' : ℕ) : Option Unit → Type := bundleIdx (fun _ : Unit => Fin M) M'
section Objects
variable {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
  [Algebra Ω Φ]
def flagLinePt (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (t : Fin N → Φ) (k : ℕ) : (Σ o, lineBlocks M M' o) → Φ
  | ⟨none, l⟩ => ∑ i, flagCoord w e t k i * algebraMap Ω Φ (φ' l (w i))
  | ⟨some _, l⟩ => ∑ i, flagCoord w e t k i * algebraMap Ω Φ (φ l (w i))
end Objects
def SegreFlagClosureBirational.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t → 1 ≤ N →
      IsBirationalJoin O (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t 1)
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


