-- Prove2me | Definitions.Def_QAlgorithms_Defs_ChannelDiamondNorm
-- name    : QAlgorithms_Defs_ChannelDiamondNorm
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:50.76297+00:00
-- url     : https://prove2.me/theorems/4ab80435-a13a-4195-9865-8a419f795492
-- title:
--   ChannelDiamondNorm
-- statement:
--   ChannelDiamondNorm
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ChannelDiamondNorm.lean

import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Channel
noncomputable section

namespace QAlgorithms.IntrinsicLearning

/-- Complex-linear stabilized induced trace norm, without the distance factor 1/2
(2204.13691 p.20, Definition C.5). The unit trace-norm ball contains zero and is compact;
finite-dimensional linearity makes its image bounded, so this real supremum is meaningful. -/
def diamondNorm (d : ℕ) (_hd : 0 < d)
    (Delta : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {v | ∃ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
    traceNorm X ≤ 1 ∧ v = traceNorm (idTensorSuperop (R := Fin d) Delta X)}

example (d : ℕ) (hd : 0 < d) : diamondNorm d hd 0 = 0 := by
  have he : {v : ℝ | ∃ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      traceNorm X ≤ 1 ∧ v = traceNorm (idTensorSuperop (R := Fin d)
        (0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) X)} = {0} := by
    ext v
    have hz : ∀ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
        idTensorSuperop (R := Fin d) (0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
          Matrix (Fin d) (Fin d) ℂ) X = 0 := by intro X; ext a b; rfl
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, hz]
    constructor
    · rintro ⟨X,_,h⟩
      simpa [traceNorm,cfc_zero] using h
    · intro h
      refine ⟨0, by simp [traceNorm,cfc_zero], ?_⟩
      simpa [traceNorm,cfc_zero] using h
  unfold diamondNorm
  rw [he,csSup_singleton]

end QAlgorithms.IntrinsicLearning


