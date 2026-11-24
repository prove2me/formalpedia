-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:36.657081+00:00
-- url     : https://prove2.me/theorems/36813df1-956b-4995-a464-e2bc164fa77d
-- title:
--   St Isolated Fibre Open Poly
-- statement:
--   Definitions and structural lemmas for St Isolated Fibre Open Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIsolatedFibreOpenPoly.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Topology ComplexSets
noncomputable section
def IsolatedFibreOpenPoly.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) → x ∈ zeroSet P →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x) →
    ∀ W' ∈ 𝓝 x, (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ W') ∈
      𝓝 (fun i => eval x (p i))
end
end GroundTheory.Heights₂.Heights


