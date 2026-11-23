-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:23.169579+00:00
-- url     : https://prove2.me/theorems/5d57747f-0da5-4c38-81ee-4c34467bb0bb
-- title:
--   Re Det Relation
-- statement:
--   Definitions and structural lemmas for Re Det Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.MxDet
noncomputable def linF {ι : Type} [Fintype ι] (x : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (x i) * MvPolynomial.X i
noncomputable def iterD {ι : Type} : (m : ℕ) → (Fin m → ι) → (MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ)
  | 0, _ => LinearMap.id
  | m + 1, a => (MvPolynomial.pderiv (a 0)).toLinearMap ∘ₗ iterD m (Fin.tail a)
end GlobalTheory.MxDet


