-- Prove2me | Definitions.Def_CutRankSched_Supplement_IsClifford
-- name    : CutRankSched_Supplement_IsClifford
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:40:37.616206+00:00
-- url     : https://prove2.me/theorems/4dcc6cfc-526b-412b-9c87-f4b06b69adde
-- title:
--   Clifford operators
-- statement:
--   An operator $F$ on $m$ qubits is **Clifford** if it is unitary and conjugates every Hermitian Pauli operator to a signed Hermitian Pauli operator: for every $p$ there are $p'$ and a sign $s\in\{\pm1\}$ with
--   $$
--   F\,P(p)\,F^\dagger = s\,P(p').
--   $$
--   This is the normalizer description of the Clifford group; $F$ may carry any global phase.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 4.1, p.6

import Mathlib
import Definitions.Def_CutRankSched_Supplement_pauliOp

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- `F` is **Clifford** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §4.1, Theorem 4.1, p.6): `F` is unitary and conjugates every
Hermitian Pauli operator to a signed Hermitian Pauli operator, `F P(p) F† = ±P(p')`.

**Formalization Note** This is the normalizer form of the Clifford group; `F` may carry any
global phase. -/
def IsClifford {m : ℕ} (F : Op m) : Prop :=
  F ∈ Matrix.unitaryGroup (Fin m → ZMod 2) ℂ ∧
    ∀ p : Pauli m, ∃ (p' : Pauli m) (s : Bool),
      F * pauliOp p * star F = (if s then (1 : ℂ) else -1) • pauliOp p'

end Supplement

end CutRankSched


