-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_coherentCounts
-- name    : TwoFoldOPI_Supplement_coherentCounts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:02:09.465899+00:00
-- url     : https://prove2.me/theorems/685abe9a-3f70-4458-a5c3-7a0bbfff3ab3
-- title:
--   Coherent programs and their gate and query counts
-- statement:
--   A program is **coherent** if it is a straight-line sequence of gates and oracle queries (no measurement, reset, coin or classical step); it then applies one unitary. This definition returns its numbers of gates and of queries, or nothing if the program is not coherent.
--
--   It models the paper's coherent decoders and preparations ("a unitary whose inverse is also available").
--
--   **Formalization Note** Work registers are counted by the statements (the qubit count is added to the gate count).
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

/-- **Coherent programs and their gate and query counts.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26: "A quantum decoder is given as a uniform circuit. Its
measurements and random choices are deferred to work registers, so it is a unitary whose inverse is
also available. We count the cost of this coherent implementation, including its work registers."

`coherentCounts P = some (g, k)` when `P` is a straight-line sequence of gates and oracle queries
ending in `halt` (no measurement, reset, coin or classical step), with `g` gates and `k` queries;
otherwise `none`.

**Formalization Note.** Such a program applies one unitary (gates and oracle calls), so it is the
"coherent implementation" of the conventions. Work registers are counted by the statements that
use it (the number of qubits `N` is added to `g`). -/
def coherentCounts {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool} {N c out : ℕ} :
    AdaptiveMembershipProgram S a ctl N c out → Option (ℕ × ℕ)
  | .halt _ _ => some (0, 0)
  | .gate _ next => (coherentCounts next).map fun p => (p.1 + 1, p.2)
  | .query _ _ _ _ _ _ next => (coherentCounts next).map fun p => (p.1, p.2 + 1)
  | _ => none

end Supplement

end TwoFoldOPI


