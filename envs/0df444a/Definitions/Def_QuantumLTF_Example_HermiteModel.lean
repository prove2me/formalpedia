-- Prove2me | Definitions.Def_QuantumLTF_Example_HermiteModel
-- name    : QuantumLTF_Example_HermiteModel
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-15T20:41:00.174072+00:00
-- url     : https://prove2.me/theorems/62f1f040-0bec-431b-8967-63d8bd1ade33
-- title:
--   Finite Gaussian grid and discrete Hermite states
-- statement:
--   The Section 5 Gaussian grid spacing and radius, coordinatewise rounding map, normalized probabilists’ Hermite functions, degree basis states, and finite discrete Hermite states.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Eqs. (150)–(158), pp.57–60.

import Mathlib
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_qex

namespace QuantumLTF.Example

open QAlgorithms

noncomputable def gridSpacing (M : ℕ) : ℝ := Real.sqrt (4 * Real.pi / M)

noncomputable def gridRadius (M : ℕ) : ℝ := gridSpacing M * M / 2

noncomputable def roundCoord (M : ℕ) (x : ℝ) : ℝ :=
  -gridRadius M + gridSpacing M * ⌊(x + gridRadius M) / gridSpacing M⌋

noncomputable def roundVec {n : ℕ} (M : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => roundCoord M (x i)

noncomputable def hermiteFn (k : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.hermite k).map (Int.castRingHom ℝ)).eval x / Real.sqrt k.factorial

noncomputable def scalarGrid {q : ℕ} (z : Qubits q) : ℝ :=
  ((bitsValue z : ℝ) - (2 ^ (q - 1) : ℕ)) * Real.sqrt (4 * Real.pi / 2 ^ q)

noncomputable def degreeKet (q k : ℕ) : EuclideanSpace ℂ (Qubits q) :=
  WithLp.toLp 2 fun z => if bitsToNat z = k then 1 else 0

noncomputable def discreteHermiteKet (q k : ℕ) : EuclideanSpace ℂ (Qubits q) :=
  let M := 2 ^ q
  WithLp.toLp 2 fun z =>
    (((2 : ℝ) / M) ^ (1 / 4 : ℝ) * Real.exp (-(scalarGrid z) ^ 2 / 4) *
      hermiteFn k (scalarGrid z) : ℝ)

end QuantumLTF.Example


