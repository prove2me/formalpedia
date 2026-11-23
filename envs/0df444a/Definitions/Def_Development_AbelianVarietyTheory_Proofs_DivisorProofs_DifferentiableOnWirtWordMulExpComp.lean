-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:03.041381+00:00
-- url     : https://prove2.me/theorems/b1f77fc9-f9e2-417e-8a20-2e9ab14ccd83
-- title:
--   Differentiable On Wirt Word Mul Exp Comp
-- statement:
--   Definitions and structural lemmas for Differentiable On Wirt Word Mul Exp Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpComp.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
noncomputable section
namespace GlobalTheory.WirtChain
open Complex
variable {Φ I : Type} [Fintype Φ] [Fintype I]
section Rep
variable (U : Set (I → ℂ)) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (l : (I → ℂ) → ℂ)
inductive ExpSum : (ℂ → (I → ℂ) → ℂ) → Prop
  | zero : ExpSum fun _ _ => 0
  | term (n : ℕ) (β : (I → ℂ) → ℂ) (w : List (Φ × Bool)) : ContDiffOn ℝ ∞ β U →
      ExpSum fun σ z => σ ^ n * β z * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z)
  | add {F₁ F₂ : ℂ → (I → ℂ) → ℂ} : ExpSum F₁ → ExpSum F₂ → ExpSum fun σ z => F₁ σ z + F₂ σ z
variable {U G t l}
end Rep
section Deriv
variable {U : Set (I → ℂ)} {G : ℂ → (Φ → ℂ) → ℂ} {t : (I → ℂ) → Φ → ℂ} {l : (I → ℂ) → ℂ}
end Deriv
end GlobalTheory.WirtChain


