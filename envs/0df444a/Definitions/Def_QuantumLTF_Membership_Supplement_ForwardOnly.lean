-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_ForwardOnly
-- name    : QuantumLTF_Membership_Supplement_ForwardOnly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:33:50.497418+00:00
-- url     : https://prove2.me/theorems/97239a53-8201-438a-8c61-fca2d8234fd8
-- title:
--   Oracle circuit without inverse calls
-- statement:
--   An oracle circuit is **forward-only** if none of its oracle calls is an inverse call. Theorems 5.2 and 5.6 use the example oracle $\mathsf{QEX}_M(f_w,\gamma_n)$ itself, as opposed to Theorem 5.8, which also allows its inverse.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.2, p. 60 (PDF p. 61); Theorem 5.6, p. 70 (PDF p. 71)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit

namespace QuantumLTF.Membership.Supplement

open QAlgorithms

/-- **An oracle circuit that never calls an inverse oracle.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.2, p. 60 (PDF p. 61):
"using one query to `QEX_M(f_w, γ_n)`", and Theorem 5.6, p. 70 (PDF p. 71): "three additional queries
to `QEX_M(f_w, γ_n)`", as opposed to Theorem 5.8's "queries to `QEX_M(f_w, γ_n)` and its inverse".
Every oracle step has `adjoint = false`. -/
def ForwardOnly {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} (c : OracleCircuit S a m) : Prop :=
  ∀ st ∈ c, match st with
    | .gate _ => True
    | .query _ adj _ _ _ => adj = false

end QuantumLTF.Membership.Supplement


