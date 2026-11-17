-- Prove2me | Definitions.Def_PRUPermLayer_Supplement_MixAlg
-- name    : PRUPermLayer_Supplement_MixAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:37:50.844886+00:00
-- url     : https://prove2.me/theorems/ddb0fc58-3621-486a-a41f-521163f2d272
-- title:
--   Fixed-direction $q$-query algorithm with forward and inverse oracle access (no controlled access)
-- statement:
--   A **fixed-direction $q$-query algorithm with forward and inverse access** to an $n$-qubit oracle $U$ ($N=2^n$) consists of
--
--   1. a direction $d_i\in\{\text{forward},\text{inverse}\}$ for each query $i=1,\dots,q$: a forward query applies $U$ to the query register, an inverse query applies $U^\dagger$;
--   2. a number $m\ge0$ of extra qubits (workspace and reference register);
--   3. unitaries $A_0,\dots,A_q$ on the query register and the $m$ extra qubits, which do not depend on $U$;
--   4. an effect $M$, $0\preceq M\preceq I$, the measurement operator of the output $1$.
--
--   The oracle is used only through $U\otimes I$ and $U^\dagger\otimes I$; there is no controlled version of $U$ or $U^\dagger$. This is the algorithm class of Theorem 1.6.
--
--   **Formalization Note** This is the mission's forward-query model `FwdAlg` with a fixed direction per query; the order of the directions is part of the algorithm. Section 2.2 allows the direction to be chosen classically from earlier measurement outcomes, while this is the fixed-direction subclass used by Theorem 1.6's exhibited attack. Intermediate measurements are purified into the workspace, whose size is arbitrary, and the final measurement is an arbitrary effect.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa33ec861a7e9c10d88cfcefc2794b77ad1674c02661c9298c5ba565bcb), §1.1, p.2 (PDF p.4); Theorem 1.6, p.4 (PDF p.6); §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information

namespace PRUPermLayer.Supplement

/-- A fixed-direction `q`-query algorithm with **forward and inverse access** to an `n`-qubit oracle `U`
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, p.2 (PDF p.4): "Forward queries apply the unitary itself, while inverse queries apply
its inverse"; Theorem 1.6, p.4 (PDF p.6); §2.2, p.9 (PDF p.11) for the forward model it extends).

The data are: the direction `d i` of query `i` (`true` = forward, the oracle applies `U`;
`false` = inverse, it applies `U†`); the number `m` of extra qubits (workspace and reference
register); unitaries `A₀, …, A_q` on the query register (`N = 2ⁿ` labels) together with the `m`
extra qubits; and the effect `M` (`0 ⪯ M ⪯ I`) of the output "1".

**Formalization Note** This is the published `PRUPermLayer.FwdAlg` with a direction for each
query and nothing else: every oracle call applies `U ⊗ I` or `U† ⊗ I` to the query register, so
there is no controlled access to `U` or `U†`. Section 2.2 permits the direction to be chosen
classically from earlier measurement outcomes; this structure is the fixed-direction subclass used
by the proof of Theorem 1.6, whose four calls occur in the fixed order `U†, U, U†, U`. Intermediate
measurements are purified into the workspace, whose size `m` is arbitrary, and the final
measurement is an arbitrary effect. -/
structure MixAlg (n q : ℕ) where
  /-- direction of query `i`: `true` = forward (`U`), `false` = inverse (`U†`) -/
  d : Fin q → Bool
  /-- number of workspace (and reference) qubits -/
  m : ℕ
  /-- the unitaries `A₀, …, A_q` -/
  A : Fin (q + 1) → Matrix.unitaryGroup (Fin (2 ^ n) × QAlgorithms.Qubits m) ℂ
  /-- the effect of the output `1` -/
  M : Matrix (Fin (2 ^ n) × QAlgorithms.Qubits m) (Fin (2 ^ n) × QAlgorithms.Qubits m) ℂ
  isEffect : QAlgorithms.IsEffect M

end PRUPermLayer.Supplement


