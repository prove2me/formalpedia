-- Prove2me | Definitions.Def_CompNonlocal_ICirc_branchOn
-- name    : CompNonlocal_ICirc_branchOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:02.42929+00:00
-- url     : https://prove2.me/theorems/54b21829-e8d0-4f64-be36-f1f4f5ee9b8a
-- title:
--   The branch keeping the designated quantum output
-- statement:
--   The instrument branch of a classical-output event that keeps exactly the circuit's designated retained wires, in their order: the unnormalized retained state (e.g. a party's private state) jointly with the classical output event.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.4, p.20

import Mathlib
import Definitions.Def_CompNonlocal_ICirc_branchWires

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The branch of a circuit for a classical-output event, keeping its designated quantum output
`outQ` (in order). This is `branchWires` with `ws = outQ`: the unnormalized retained state after
the event, as in the QCCC model of Głuch, Morimae, *From Computational Nonlocality to Public-Key
Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.4, p.20. -/
noncomputable def ICirc.branchOn (C : ICirc) (m : ℕ) (x : Str) (ρ : Matrix (Bits m) (Bits m) ℂ)
    (P : Str → Bool) : Matrix (Bits C.outQ.length) (Bits C.outQ.length) ℂ :=
  C.branchWires C.outQ.get m x ρ P

end CompNonlocal


