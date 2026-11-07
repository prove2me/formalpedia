-- Prove2me | Definitions.Def_PRUPermLayer_FwdAlg
-- name    : PRUPermLayer_FwdAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:02.801576+00:00
-- url     : https://prove2.me/theorems/3db1654c-3160-4052-960f-b6148494bfb8
-- title:
--   $t$-query forward algorithm (adaptive, with workspace and final measurement)
-- statement:
--   A **$t$-query forward algorithm** on an $n$-qubit oracle prepares a state on a query register ($N = 2^n$ basis labels), a workspace and a reference register, and then alternates $t$ times between an oracle call, which applies the oracle $U$ to the query register, and an arbitrary unitary on all registers; at the end it measures and outputs one bit. With intermediate measurements purified, it is given by
--
--   1. a number $m \ge 0$ of extra qubits (workspace and reference register together);
--   2. unitaries $A_0, A_1, \dots, A_t$ on the query register and the $m$ extra qubits, which do not depend on $U$;
--   3. an effect $M$, $0 \preceq M \preceq I$, the measurement operator of the output $1$.
--
--   Later queries may depend on earlier answers through the $A_i$, so these algorithms are adaptive.
--
--   **Formalization Note** Every finite-dimensional workspace or reference register embeds in a register of qubits, so taking $m$ qubits loses nothing. The output measurement is an arbitrary effect, which includes projective measurements and, by Naimark dilation into the workspace, gives the same optimal advantage.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information

namespace PRUPermLayer

/-- A `t`-query forward algorithm on an `n`-qubit oracle (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11): "A t-query
forward algorithm prepares a state on a query register, a workspace and a reference register, and
then alternates t times between an oracle call, which applies U to the query register, and an
arbitrary unitary on all registers. At the end it measures and outputs one bit. If we purify the
intermediate measurements, its final state is |AU⟩ = At UAt−1 · · · A1 UA0|0⟩").

The data are: the number `m` of extra qubits; the `t + 1` unitaries `A₀, …, A_t` on the query
register (`N = 2ⁿ` labels) together with the `m` extra qubits; and the effect `M` (`0 ⪯ M ⪯ I`)
of the final outcome "1".

**Formalization Note** The workspace and the reference register are merged into the `m` extra
qubits; every `m` is allowed, and every finite-dimensional register embeds in qubits. The final
two-outcome measurement is an arbitrary effect `M` (the published `QAlgorithms.IsEffect`), which
contains the projective measurements and gives the same optimal advantage (Naimark dilation into
the workspace). Intermediate measurements are purified, as on p.9; the `Aᵢ` do not depend on the
oracle. -/
structure FwdAlg (n t : ℕ) where
  /-- number of workspace (and reference) qubits -/
  m : ℕ
  /-- the unitaries `A₀, …, A_t` -/
  A : Fin (t + 1) → Matrix.unitaryGroup (Fin (2 ^ n) × QAlgorithms.Qubits m) ℂ
  /-- the effect of the output `1` -/
  M : Matrix (Fin (2 ^ n) × QAlgorithms.Qubits m) (Fin (2 ^ n) × QAlgorithms.Qubits m) ℂ
  isEffect : QAlgorithms.IsEffect M

end PRUPermLayer


