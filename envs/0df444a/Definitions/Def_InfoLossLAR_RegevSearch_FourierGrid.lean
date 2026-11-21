-- Prove2me | Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
-- name    : InfoLossLAR_RegevSearch_FourierGrid
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:30:47.327918+00:00
-- url     : https://prove2.me/theorems/5380674a-dc53-482b-aa17-a7519161ad6a
-- title:
--   Signed coefficient events for a finite Gaussian Fourier register
-- statement:
--   For an integer basis matrix $B$, Gaussian width $r$ and a positive modulus $M$, the amplitude of a residue vector is the sum over its integer lifts of the lattice Gaussian weight at width $\sqrt2r$. The finite event probability is the normalized sum of the squared amplitudes over residues whose centered signed representatives belong to the event. The adequacy predicate specifies when the register modulus contains the geometric truncation region without aliasing.
-- source:
--   Readout for https://prove2.me/theorems/9fdfd0c1-342f-4e71-9410-562b6727463a. Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, §3.2.2, Lemma 3.14, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. The input-basis signed-coordinate register and its explicit adequacy predicate specialize the finite Fourier readout.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Mathlib.Data.ZMod.ValMinAbs

set_option autoImplicit false
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.RegevSearch
noncomputable section
variable {n : ℕ}

/-- The exact periodized amplitude in one finite register of the primal lattice. -/
def gridFiberAmplitude (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (M : ℕ) (c : Fin n → ZMod M) : ℝ :=
  ∑' z : Fin n → ℤ, if (fun i => (z i : ZMod M)) = c then rhoInt (Real.sqrt 2*r) (B.mulVec z) else 0

/-- The Born event of the finite Gaussian Fourier image read as signed integers. -/
def fourierEvent (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (M : ℕ) [NeZero M] (T : Finset (Fin n → ℤ)) : ℝ :=
  (∑ c : Fin n → ZMod M, if (fun i => (c i).valMinAbs) ∈ T then (gridFiberAmplitude B r M c)^2 else 0) /
    (∑ c : Fin n → ZMod M, (gridFiberAmplitude B r M c)^2)

/-- The modulus gives a decoding radius large enough for the retained Gaussian support. -/
def gridAdequate (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (M : ℕ) : Prop :=
  4 * ((∑ i, ∑ j, (B.adjugate i j).natAbs) + 1) * (n+1) * (⌈r⌉₊+1) ≤ M

end
end InfoLossLAR.WorstCase.RegevSearch


