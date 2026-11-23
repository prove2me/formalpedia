-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
-- name    : ReciprocityTheory_SemistableReduction_GaussValExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:07.393829+00:00
-- url     : https://prove2.me/theorems/da962460-c8cb-4a30-ad44-ea24f50c1887
-- title:
--   Gauss Val Exists
-- statement:
--   Definitions and structural lemmas for Gauss Val Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValExists.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
noncomputable def gaussRed {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    MvPolynomial σ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) :=
  ∑ α ∈ p.support, monomial α (IsLocalRing.residue _ ⟨p.coeff α, hc α⟩)
end ReciprocityTheory.MultiplicativeHeights


