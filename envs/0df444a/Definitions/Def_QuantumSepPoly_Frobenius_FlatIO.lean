-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_FlatIO
-- name    : QuantumSepPoly_Frobenius_FlatIO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:40.673509+00:00
-- url     : https://prove2.me/theorems/76143c50-e095-4df1-8adf-f6af01af2952
-- title:
--   Scalar interface for computable flattening
-- statement:
--   The flattening program receives the matrix and both unitary matrices as scalar input together with the fixed accuracy. It writes the two computed matrix parts in consecutive output blocks. Their row-major complex addresses are fixed by
--   $$1+\mathrm{offset}+2(((ad+c)d+b)d+e).$$
--   This interface makes the efficient-computability clause of Lemma 3.3 a finite-program assertion rather than an unconnected runtime label.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 12 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_AlgorithmIO
import Definitions.Def_QuantumSepPoly_Frobenius_FlatDecomposition

noncomputable section

namespace QuantumSepPoly.Frobenius

def encodeOp {d : ℕ} (U : Op d) : List ℝ :=
  (List.finRange d).flatMap fun i => (List.finRange d).flatMap fun j => [(U i j).re,(U i j).im]

def flatInitial {d : ℕ} (δ : ℝ) (M : Bip d) (U V : Op d) : RAMState :=
  ramInitial δ d (encodeMatrix M ++ encodeOp U ++ encodeOp V)

def matrixOutput (d offset : ℕ) (s : RAMState) : Bip d := fun i j =>
  let a := 1 + offset + 2 * (((i.1.val*d + i.2.val)*d+j.1.val)*d+j.2.val)
  (s.real a : ℂ) + Complex.I * s.real (a+1)

end QuantumSepPoly.Frobenius


