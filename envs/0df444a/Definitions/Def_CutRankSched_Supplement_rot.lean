-- Prove2me | Definitions.Def_CutRankSched_Supplement_rot
-- name    : CutRankSched_Supplement_rot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:38:01.057387+00:00
-- url     : https://prove2.me/theorems/aa61ac2a-dcc3-4356-922d-44f5100678fa
-- title:
--   Signed Pauli rotation $R_\epsilon(P)=\exp(-i\epsilon\pi P/8)$
-- statement:
--   For a sign $\epsilon\in\{+1,-1\}$ and a Hermitian operator $P$ with $P^2=1$, the **signed Pauli rotation** is
--   $$
--   R_\epsilon(P) = \exp(-i\epsilon\pi P/8) = \cos(\pi/8)\,\mathbf 1 - i\epsilon\sin(\pi/8)\,P .
--   $$
--   A single-qubit $T$ gate is $R_{+1}(Z)$ and a $T^\dagger$ gate is $R_{-1}(Z)$, up to a global phase.
--
--   **Formalization Note** The sign is a Boolean (`true` $=+1$), as in the base instance. The rotation is written in the closed form on the right, which equals the matrix exponential whenever $P^2=1$; it is only applied to the Pauli operators $P(p)$, which satisfy $P(p)^2=1$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.1, p.4

import Mathlib
import Definitions.Def_CutRankSched_Supplement_pauliOp

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The signed Pauli rotation `R_ε(P) = exp(−iεπP/8)` of a Hermitian Pauli operator `P`
(Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.1, p.4), written in closed form as `cos(π/8)·1 − iε sin(π/8)·P`.

**Formalization Note** The sign `ε ∈ {+1, −1}` is a `Bool` (`true` = `+1`), as in
`CutRankSched.Instance`. The closed form equals the matrix exponential `exp(−iεπP/8)` for every
`P` with `P² = 1`, in particular for every `pauliOp p`; only such `P` are ever rotated. -/
noncomputable def rot {m : ℕ} (ε : Bool) (P : Op m) : Op m :=
  (Real.cos (Real.pi / 8) : ℂ) • (1 : Op m) -
    ((if ε then (1 : ℂ) else -1) * Complex.I * (Real.sin (Real.pi / 8) : ℂ)) • P

end Supplement

end CutRankSched


