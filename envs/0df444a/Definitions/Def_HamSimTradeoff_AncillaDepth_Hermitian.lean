-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Hermitian
-- name    : HamSimTradeoff_AncillaDepth_Hermitian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:16.942422+00:00
-- url     : https://prove2.me/theorems/4b7567b8-7bc6-4a77-8b2e-08ec4d4fc52d
-- title:
--   Hermitian involution decompositions and ideal evolution
-- statement:
--   Let $L,d$ be natural numbers. A Hermitian involution decomposition consists of positive real weights $\alpha_j$ summing to one and Hermitian complex $d\times d$ matrices $H_j$ satisfying $H_j^2=I$. Define
--   $$A=\sum_{j=1}^L\alpha_jH_j,\qquad U_A(t)=\exp(-itA),\quad t\in\mathbb R.$$
--   The theorem restricts to $L\ge2$ and $d\ge1$. This definition supplies the general finite-dimensional Hamiltonian object independently of the coherent circuit model.
--
--   **Formalization Note** Matrices use `Fin d` coordinates; the scoped matrix norm is the spectral operator norm. The exponential is Mathlib's matrix exponential, and no commutativity between terms is assumed.
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), pp.4–5, §1.1 and Theorem 1.1

import Mathlib
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth
noncomputable section

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- The source's Hermitian involution decomposition, with no commutativity assumption. -/
structure Decomposition (L d : ℕ) where
  alpha : Fin L → ℝ
  H : Fin L → Mat d
  alpha_pos : ∀ j, 0 < alpha j
  alpha_sum : ∑ j, alpha j = 1
  hermitian : ∀ j, (H j).IsHermitian
  involution : ∀ j, H j * H j = 1

def hamiltonian {L d : ℕ} (alpha : Fin L → ℝ) (H : Fin L → Mat d) : Mat d :=
  ∑ j, (alpha j : ℂ) • H j

def evolution {d : ℕ} (A : Mat d) (t : ℝ) : Mat d :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • A)

end
end HamSimTradeoff.AncillaDepth


