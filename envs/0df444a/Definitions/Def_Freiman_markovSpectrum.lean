-- Prove2me | Definitions.Def_Freiman_markovSpectrum
-- name    : Freiman_markovSpectrum
-- status  : Definition
-- author  : @tp
-- created : 2026-09-08T23:20:56.461462+00:00
-- url     : https://prove2.me/theorems/9459fffd-d710-4da5-80ac-9b0d9147028d
-- title:
--   The classical Markov spectrum
-- statement:
--   For real coefficients $A,B,C$, consider the binary quadratic form
--   $$
--   Q(X,Y)=AX^2+BXY+CY^2.
--   $$
--   Its discriminant and absolute minimum on the integer lattice are
--   $$
--   \Delta(Q)=B^2-4AC,\qquad
--   \mu(Q)=\inf_{(p,q)\in\mathbb Z^2\setminus\{(0,0)\}}|Q(p,q)|.
--   $$
--   The Markov spectrum is
--   $$
--   M=\left\{\frac{\sqrt{\Delta(Q)}}{\mu(Q)}:
--   \Delta(Q)>0,\ \mu(Q)>0\right\}.
--   $$
--   The infimum includes every nonzero integer vector, including vectors on either coordinate axis. The positive discriminant makes the form indefinite, and the positive minimum makes the displayed ratio finite.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.3, p. 9, the definitions preceding Lemma 1.4.

import Mathlib.Analysis.Real.Sqrt

namespace Freiman

def quadraticValue (A B C : ℝ) (p q : ℤ) : ℝ :=
  A * (p : ℝ) ^ 2 + B * (p : ℝ) * (q : ℝ) + C * (q : ℝ) ^ 2

noncomputable def quadraticMinimum (A B C : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ p q : ℤ,
    (p ≠ 0 ∨ q ≠ 0) ∧ v = |quadraticValue A B C p q|}

def markovSpectrum : Set ℝ :=
  {t | ∃ A B C : ℝ,
    0 < B ^ 2 - 4 * A * C ∧
    0 < quadraticMinimum A B C ∧
    t = Real.sqrt (B ^ 2 - 4 * A * C) / quadraticMinimum A B C}

end Freiman


