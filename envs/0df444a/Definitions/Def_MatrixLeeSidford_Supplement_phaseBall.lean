-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_phaseBall
-- name    : MatrixLeeSidford_Supplement_phaseBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:15:57.658571+00:00
-- url     : https://prove2.me/theorems/c7b9e434-b4bb-47ba-9a5a-83d095a66307
-- title:
--   Phase ball $B(y^\circ)=\{y:\|y-y^\circ\|_{\nabla^2F(y^\circ)}\le2/5\}$
-- statement:
--   For a centering call that starts at the feasible point $y^\circ$, its **phase ball** is the Dikin-type ellipsoid
--   $$
--   B(y^\circ):=\big\{y\in\mathbb R^m:\ \|y-y^\circ\|_{\nabla^2F(y^\circ)}\le 2/5\big\},\qquad \|v\|_{\nabla^2F(y^\circ)}=\sqrt{\nabla^2F(y^\circ)[v,v]},
--   $$
--   where $F$ is the matrix Lee–Sidford barrier. By self-concordance every phase ball lies in $\Omega$, and the Hessian of $F$ is within constant factors of $\nabla^2F(y^\circ)$ on it.
--
--   **Formalization Note** The local norm is the published one, the square root of the second Fréchet derivative of $F$ evaluated on the diagonal.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (8.3), p.56

import Mathlib
import Definitions.Def_MatrixLeeSidford_barrierF
import Definitions.Def_DoublyOptBandit_LocalNorm

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **phase ball** `B(y°) := {y : ‖y − y°‖_{∇²F(y°)} ≤ 2/5}` of a centering call that starts at `y°`
(Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Eq. (8.3), p.56).

**Formalization Note** `F` is the published `barrierF A C`; the local norm is the published
`DoublyOptBandit.localNorm`, `√(∇²F(y°)[v, v])` with `∇²F = iteratedFDeriv ℝ 2 F`. -/
noncomputable def phaseBall {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (y₀ : EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {y | DoublyOptBandit.localNorm (barrierF A C) y₀ (y - y₀) ≤ 2 / 5}

end MatrixLeeSidford.Supplement


