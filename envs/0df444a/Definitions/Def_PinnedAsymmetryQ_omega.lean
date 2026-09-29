-- Prove2me | Definitions.Def_PinnedAsymmetryQ_omega
-- name    : PinnedAsymmetryQ_omega
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-24T04:24:11.476519+00:00
-- url     : https://prove2.me/theorems/214f710b-837b-4a3b-b1aa-df39a2458187
-- title:
--   Upper-branch frequency $\omega(k)$ on a $q$-dimensional lattice, and reversal along axis 0
-- statement:
--   Fix $q \ge 1$, real numbers $K$ (stiffness), $c$ (neighbour coupling), $\beta$ (gyroscopic strength), and a wavevector $k = (k_0, \dots, k_{q-1}) \in \mathbb{R}^q$. The **upper-branch frequency** is
--
--   $$
--   \omega(k) = \beta c \sin k_0 + \sqrt{\bigl(\beta c \sin k_0\bigr)^2 + K + 2c \sum_{a=0}^{q-1} (1 - \cos k_a)},
--   $$
--
--   with the gauge term acting along axis 0 and the sum over all axes. The **reversal along axis 0** is $\bar k = (-k_0, k_1, \dots, k_{q-1})$.
--
--   **Formalization Note** The square root is `Real.sqrt`, which returns $0$ on negative inputs; `flip0` is `Function.update` at index $0$.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1 (dispersion relation, extended to q axes): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib

open Real BigOperators

namespace PinnedAsymmetryQ

/-- Upper-branch frequency on a uniform lattice with q axes; the gauge term acts
along axis 0. Wavevector k, stiffness K, neighbour coupling c, strength β. -/
noncomputable def omega (q : ℕ) [NeZero q] (K c β : ℝ) (k : Fin q → ℝ) : ℝ :=
  β * c * sin (k 0) +
    Real.sqrt ((β * c * sin (k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (k a)))

/-- Reverse the wavevector along axis 0 only. -/
def flip0 (q : ℕ) [NeZero q] (k : Fin q → ℝ) : Fin q → ℝ :=
  Function.update k 0 (-(k 0))

end PinnedAsymmetryQ


