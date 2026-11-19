-- Prove2me | Definitions.Def_DualSepClusterLP_SeparationEncoding
-- name    : DualSepClusterLP_SeparationEncoding
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-18T17:40:15.995952+00:00
-- url     : https://prove2.me/theorems/bb773b2f-ee1b-4d40-8a0c-d0a9a6328e7a
-- title:
--   Signed rational inputs and the two separator outputs
-- statement:
--   In vertex order, encode each reduced signed rational by a sign and two length-delimited binary integers. The separator outputs either a subset membership mask or a scaled-feasibility flag.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §2, Theorem 2.1, finite encodings. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_DualSepClusterLP_Setting

namespace DualSepClusterLP

/-- A unary length prefix followed by that many binary digits, least significant first. -/
def lengthPrefixedNat (a : ℕ) : List Bool :=
  List.replicate a.bits.length true ++ [false] ++ a.bits

/-- Sign bit, magnitude of the reduced numerator, and positive reduced denominator. -/
def priceBits (q : ℚ) : List Bool :=
  (decide (q.num < 0)) :: (lengthPrefixedNat q.num.natAbs ++ lengthPrefixedNat q.den)

/-- Prices in vertex order. The graph header already specifies their number. -/
def pricesBits {n : ℕ} (q : Fin n → ℚ) : List Bool :=
  (List.finRange n).flatMap fun i => priceBits (q i)

def separationInput {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) : List Bool :=
  graphInput t G ++ pricesBits q

/-- A false tag reports scaled feasibility. A true tag is followed by the witness membership bits. -/
def separationOutput {n : ℕ} : Option (Finset (Fin n)) → List Bool
  | none => [false]
  | some S => true :: (List.finRange n).map (fun i => decide (i ∈ S))

end DualSepClusterLP


