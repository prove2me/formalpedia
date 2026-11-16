-- Prove2me | Definitions.Def_QuantumLTF_Example_LowerModel
-- name    : QuantumLTF_Example_LowerModel
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-15T20:36:46.286607+00:00
-- url     : https://prove2.me/theorems/2a83bcf2-37ea-470e-a045-5cfa19901331
-- title:
--   Hard sign family for the Section 5 example-oracle lower bound
-- statement:
--   The Boolean sign strings, perturbed unit normals, Hamming distance, and finite total-variation distance used in the Assouad reduction proving Theorem 5.12.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, STOC 2027 submission #347, Eqs. (198)–(205), pp. 74–78.

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree

namespace QuantumLTF.Example

open QuantumLTF.Membership

abbrev SignString (m : ℕ) := Fin m → Bool

def signValue (b : Bool) : ℝ := if b then 1 else -1

/-- The hard family of unit normals used in the example-oracle lower bound. -/
noncomputable def hardWeight (m : ℕ) (ε : ℝ) (z : SignString m) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  let r := 4 * Real.pi * ε
  WithLp.toLp 2 (Fin.cases (Real.sqrt (1 - r ^ 2))
    (fun i => r / Real.sqrt m * signValue (z i)))

def hamming {m : ℕ} (z z' : SignString m) : ℕ :=
  (Finset.univ.filter fun i => z i ≠ z' i).card

/-- Total-variation distance for probability mass functions on a finite type. -/
noncomputable def pmfTV {α : Type*} [Fintype α] (P Q : PMF α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |(P a).toReal - (Q a).toReal|

end QuantumLTF.Example


