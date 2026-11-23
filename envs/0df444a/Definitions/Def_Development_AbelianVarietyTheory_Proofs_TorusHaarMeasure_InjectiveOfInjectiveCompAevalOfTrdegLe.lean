-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_InjectiveOfInjectiveCompAevalOfTrdegLe
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_InjectiveOfInjectiveCompAevalOfTrdegLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:18.579311+00:00
-- url     : https://prove2.me/theorems/3e8e951f-1afa-4068-9ed4-214150db8015
-- title:
--   Injective Of Injective Comp Aeval Of Trdeg Le
-- statement:
--   Definitions and structural lemmas for Injective Of Injective Comp Aeval Of Trdeg Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/InjectiveOfInjectiveCompAevalOfTrdegLe.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
namespace GlobalTheory
open MvPolynomial
def elimEmb (D N : ℕ) (j0 : Fin (N + 1)) :
    Fin (N + 1) ⊕ (Fin D × Fin N) → TVar D N
  | Sum.inl j => (0, j)
  | Sum.inr q => (q.1.succ, j0.succAbove q.2)
noncomputable def elimImg {F : Type} [Field F] (D N : ℕ) (j0 : Fin (N + 1))
    (xx : Fin (N + 1) → F) (p : TVar D N) : MvPolynomial (Fin (N + 1) ⊕ (Fin D × Fin N)) F :=
  Fin.cases (motive := fun _ => MvPolynomial (Fin (N + 1) ⊕ (Fin D × Fin N)) F)
    (X (Sum.inl p.2))
    (fun i => Fin.insertNth (α := fun _ => MvPolynomial (Fin (N + 1) ⊕ (Fin D × Fin N)) F) j0
      (-∑ j : Fin N, X (Sum.inr (i, j)) * C (xx (j0.succAbove j)))
      (fun j => X (Sum.inr (i, j))) p.2) p.1
end GlobalTheory


