-- Prove2me | Definitions.Def_PRUPermLayer_piEq
-- name    : PRUPermLayer_piEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:51.670301+00:00
-- url     : https://prove2.me/theorems/502ede3d-2e23-45f2-b64c-c68f1fce8f91
-- title:
--   Two-qubit equality projector $\pi_{\mathrm{eq}} = |00\rangle\langle 00| + |11\rangle\langle 11|$
-- statement:
--   On two qubits,
--   $$
--   \pi_{\mathrm{eq}} = |00\rangle\langle 00| + |11\rangle\langle 11| = \tfrac12 (I + Z\otimes Z),
--   $$
--   the projector onto equal computational-basis outcomes. After regrouping qubits by position, the $n$-qubit equality projector is $\Pi_{\mathrm{eq}} = \pi_{\mathrm{eq}}^{\otimes n}$ (Eq. (1)).
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)

import Mathlib

namespace PRUPermLayer

/-- The two-qubit equality projector `π_eq = |00⟩⟨00| + |11⟩⟨11| = (I + Z ⊗ Z)/2`
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)).

**Formalization Note** Indexed by `Bool × Bool`, first factor the first qubit. -/
def piEq : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.diagonal fun p => if p.1 = p.2 then 1 else 0

end PRUPermLayer


