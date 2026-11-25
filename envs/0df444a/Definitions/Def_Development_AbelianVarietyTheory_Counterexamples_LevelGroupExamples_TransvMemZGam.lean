-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_TransvMemZGam
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_TransvMemZGam
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:39:19.346592+00:00
-- url     : https://prove2.me/theorems/da3f03e9-bc67-4b9b-b3b8-e444dcca7ec0
-- title:
--   Transv Mem ZGam
-- statement:
--   Definitions and structural lemmas for Transv Mem ZGam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/TransvMemZGam.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ
open scoped ComplexConjugate
namespace GlobalTheory.FJCuspCheck
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
noncomputable def ev (χ : Matrix (Fin ρ) (Fin ρ) E) (u u' : Fin ρ → E) : E :=
  ∑ a, ∑ b, u a * χ a b * cc (u' b)
noncomputable def gen (X : Data E r) (b : E) (u u' : Fin ρ → E) : Matrix (Fin ρ) (Fin ρ) E :=
  Matrix.of fun i k => X.κ0 / 2 * (b * u i * cc (u' k) + cc b * u' i * cc (u k))
def cuspOfIso (X : Data E r) (ξ : Fin r → E) (h0 : ξ ≠ 0) (hi : herm X.Gm ξ ξ = 0) : CuspFD X 1 where
  e := fun _ => ξ
  ind := linearIndependent_unique_iff.2 h0
  iso := fun _ _ => hi
end GlobalTheory.FJCuspCheck


