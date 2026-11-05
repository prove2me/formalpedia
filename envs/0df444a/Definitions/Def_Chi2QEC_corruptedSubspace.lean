-- Prove2me | Definitions.Def_Chi2QEC_corruptedSubspace
-- name    : Chi2QEC_corruptedSubspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:49.173986+00:00
-- url     : https://prove2.me/theorems/7b8ac0d7-cd51-4dac-a773-17a0f3730026
-- title:
--   The corrupted code subspace
-- statement:
--   The corrupted code subspace of a code $C$ under an error family $(E_h)_h$ is the span of all the error images,
--   $$
--   \sum_h E_h(C).
--   $$
--   For the single-photon-loss errors its dimension is the paper's $D_{\mathrm{loss}}$.
--
--   **Formalization Note** The single-photon-loss family contains the identity, so in that case this subspace contains $C$.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Sec. V B, pp.16–17

import Mathlib

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. V B, pp.16–17 ("the corrupted code subspace"): the span of the images
`E_h C` of the code `C` under all the errors. Its dimension is the paper's `D_loss` when `E` is
`lossError`.

**Formalization Note.** The family `lossError` contains the identity, so this subspace contains
`C` itself. -/
noncomputable def corruptedSubspace {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (E : κ → Matrix ι ι ℂ) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  ⨆ h, C.map (Matrix.toEuclideanLin (E h))

end Chi2QEC


