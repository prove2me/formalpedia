-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:36.267898+00:00
-- url     : https://prove2.me/theorems/006e77c6-136a-425f-adb5-67c8edf4873b
-- title:
--   PSegre Flag Closure Pullback
-- statement:
--   Definitions and structural lemmas for PSegre Flag Closure Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
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
section Blocks
variable (K : Type*)
def closureBlockEquiv : Option (Option K) ≃ K ⊕ Option Unit where
  toFun
    | none => Sum.inr none
    | some none => Sum.inr (some ())
    | some (some k) => Sum.inl k
  invFun
    | Sum.inl k => some (some k)
    | Sum.inr none => none
    | Sum.inr (some _) => some none
  left_inv := by rintro (_ | (_ | k)) <;> rfl
  right_inv := by rintro (k | (_ | ⟨⟩)) <;> rfl
variable {K} (ι : K → Type) (M M' : ℕ)
def closureVarEquiv :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) ≃ (Σ s, Sum.elim ι (lineBlocks M M') s) where
  toFun
    | ⟨none, l⟩ => ⟨Sum.inr none, l⟩
    | ⟨some none, l⟩ => ⟨Sum.inr (some ()), l⟩
    | ⟨some (some k), i⟩ => ⟨Sum.inl k, i⟩
  invFun
    | ⟨Sum.inl k, i⟩ => ⟨some (some k), i⟩
    | ⟨Sum.inr none, l⟩ => ⟨none, l⟩
    | ⟨Sum.inr (some _), l⟩ => ⟨some none, l⟩
  left_inv := by rintro ⟨_ | (_ | k), l⟩ <;> rfl
  right_inv := by rintro ⟨k | (_ | ⟨⟩), l⟩ <;> rfl
end Blocks
section Data
variable {K : Type} {ι : K → Type} {m : ℕ}
def joinClosureDeg (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) : Fin (1 + m) → K ⊕ Option Unit → ℤ :=
  Fin.append (fun _ : Fin 1 => ζ ∘ (closureBlockEquiv K).symm) (fun j => joinDeg (L j))
def joinClosureForm {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (Sum.elim ι (lineBlocks M M')) R)
    (F : Fin m → MRing ι R) : Fin (1 + m) → MRing (Sum.elim ι (lineBlocks M M')) R :=
  Fin.append (fun _ : Fin 1 => h) (fun j => joinForm (F j))
end Data
section PointIdeal
end PointIdeal
end
end GroundTheory.Heights₂.Heights.NumbersDVR


