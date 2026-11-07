-- Prove2me | Definitions.Def_ConstDepthUnitary_IsTRS
-- name    : ConstDepthUnitary_IsTRS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:25.58655+00:00
-- url     : https://prove2.me/theorems/a070455a-1d45-4df9-b6b1-1d916886b915
-- title:
--   Traceless real symmetric unitaries
-- statement:
--   A real square matrix $S$ is a **traceless real symmetric unitary** when
--   $$S^{\mathsf T}=S,\qquad S^2=I,\qquad \operatorname{tr}S=0.$$
--   For a real symmetric matrix, being unitary is equivalent to $S^2=I$. Tracelessness is essential for Theorem 5.1.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 5.1, p.25; Lemma 3.1, item 4, p.15

import Mathlib

namespace ConstDepthUnitary

/-- A traceless real symmetric unitary: a real matrix with `Sᵀ = S`, `S² = I` and `tr S = 0`. For a
real symmetric `S`, being unitary is the same as `S² = I`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 5.1, p.25; Lemma 3.1 item 4 and footnote 10, p.15. -/
def IsTRS {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) : Prop :=
  S.IsSymm ∧ S * S = 1 ∧ S.trace = 0

end ConstDepthUnitary


