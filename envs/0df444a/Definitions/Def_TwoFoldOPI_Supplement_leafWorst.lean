-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_leafWorst
-- name    : TwoFoldOPI_Supplement_leafWorst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:04:44.474729+00:00
-- url     : https://prove2.me/theorems/22cf5480-7dc9-4266-86aa-58adce79887b
-- title:
--   The worst-case value of an operation count over the branches of a program
-- statement:
--   The maximum of a chosen count (queries, or gates and other operations) over the branches of a run that have positive probability. It is the cost of the bounded-time algorithm of Theorem 5.28.
--
--   **Formalization Note** The branch convention of the published `QAlgorithms.OPI.membershipResources`, applied to one chosen count.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Theorem 5.28, p. 27

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

open Classical in
/-- **The worst-case value of an operation count over the branches of a program.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Theorem 5.28, p.27: "A bounded-time version has the same success guarantee and gate and
query bounds larger by a factor O(log(1/ϵ))."

`leafWorst P O cnt` is the maximum of `cnt(counts)` over the leaves of the run of `P` from
`|0^N⟩` with oracles `O` that have positive probability (count order: queries, gates, resets,
measurements, classical steps).

**Formalization Note.** The same branch convention as the published
`QAlgorithms.OPI.membershipResources`, applied to one chosen count. -/
noncomputable def leafWorst {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
    {N c out : ℕ} (P : AdaptiveMembershipProgram S a ctl N c out)
    (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) (cnt : (Fin 5 → ℕ) → ℕ) : ℕ :=
  (adaptiveExecution O P (pureDensity (zeroKet N)) (fun _ => false)).foldl
    (fun acc leaf => if 0 < leaf.1.2.trace.re then max acc (cnt leaf.2) else acc) 0

end Supplement

end TwoFoldOPI


