-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:18.936518+00:00
-- url     : https://prove2.me/theorems/4977326e-b01c-4719-b96a-dac4fdfc72bc
-- title:
--   Statements Swap
-- statement:
--   Definitions and structural lemmas for Statements Swap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSwap.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def SwapCycles.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (a a' : K → ℕ) (s s' : MRing ι),
    IsArithVar P d → IsMultiHomog s a → IsMultiHomog s' a' → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    ((divCycle P s).sum fun W m => m • divCycle W s') =
      (divCycle P s').sum fun W m => m • divCycle W s
def GeoNumCut.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (n : ℕ)
    (a : Fin n → K → ℤ) (b : K → ℕ) (t : MRing ι),
    IsMultiProjPrime V → (charOf V).Prime →
    ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    IsMultiHomog t b → t ∉ V →
    geoNum (n + 1) V (Fin.snoc a fun k => (b k : ℤ)) =
      ∑ᶠ U ∈ divSupp V t, (multAt (V ⊔ Ideal.span {t}) U : ℤ) * geoNum n U a
section Inhabitants
def fibTwo : Ideal (MRing (PBlk 2)) := Ideal.span {C 2}
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Inter


