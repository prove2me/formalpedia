-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:16:12.875803+00:00
-- url     : https://prove2.me/theorems/ec5899eb-a4f9-4259-b44f-bfbf370bd8a8
-- title:
--   Snapper Cut Obj
-- statement:
--   Definitions and structural lemmas for Snapper Cut Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperCutObj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
section Defs
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
def eulerCharQuot {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubSystem k x E) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (Module.finrank k (SubSystem.quotH F₁ F₂ i) : ℤ)
def pieceChar (pp : Ideal (Poly k N)) (a : ℤ) {t : ℕ} (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : ℤ :=
  eulerCharQuot k
    (((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
    ((((twistSys k x a).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
      (twistSys k x c))
end Defs
def IsNumPolyLT (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) : Prop :=
  ∃ Q : MvPolynomial (Fin (t + 1)) ℚ, (Q = 0 ∨ Q.totalDegree < D) ∧
    ∀ (n : Fin t → ℕ) (c : ℤ), f n c = eval (Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)) Q
end
end GroundTheory.Heights₂.Heights.Kleiman


