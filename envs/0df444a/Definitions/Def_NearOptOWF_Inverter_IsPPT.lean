-- Prove2me | Definitions.Def_NearOptOWF_Inverter_IsPPT
-- name    : NearOptOWF_Inverter_IsPPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:09.794955+00:00
-- url     : https://prove2.me/theorems/3c42637e-35d4-4edc-99b7-e170eee291cb
-- title:
--   Probabilistic polynomial-time algorithm
-- statement:
--   A randomized algorithm is **PPT** if its number of coins is polynomial in the encoded input length and one uniform machine (the published machine model `LaconicBarrier.PolyTimeOn`) computes its output from the input and the coins in polynomial time.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §3 Notations, p.8 (PDF p.10); Theorem 4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_NearOptOWF_Inverter
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace NearOptOWF

open LaconicBarrier

/-- The algorithm is **probabilistic polynomial time** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §3 Notations, p.8 (PDF p.10): "PPT
as shorthand for probabilistic polynomial time"; Theorem 4.1, p.11): polynomially many coins in the
encoded input length, and one uniform machine (the published `LaconicBarrier.PolyTimeOn` model)
computes the output from the input tuple and the coin string in polynomial time. -/
def Inverter.IsPPT (A : Inverter) : Prop :=
  (∃ q : Polynomial ℕ, ∀ ℓ, A.coins ℓ ≤ q.eval ℓ) ∧
  PolyTimeOn (ι := (inp : List (List Bool)) × (Fin (A.coins (KarpLiptonOM.tupleEnc inp).length) → Bool))
    (fun i => i.1 ++ [bits i.2]) (fun i => A.run i.1 (bits i.2))

end NearOptOWF


