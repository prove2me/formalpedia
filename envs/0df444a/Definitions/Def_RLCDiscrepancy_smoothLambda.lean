-- Prove2me | Definitions.Def_RLCDiscrepancy_smoothLambda
-- name    : RLCDiscrepancy_smoothLambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:10.688203+00:00
-- url     : https://prove2.me/theorems/692ee8a9-51fb-4d43-b3b2-750a83d56b81
-- title:
--   The level $\Lambda=\max\{\|f\|_\infty q^{-k},\sqrt\Gamma\}$
-- statement:
--   For $f:\mathbb F_q^n\to\mathbb R$, a length $k$ and $\Gamma\ge0$, Lemma 4.13 sets
--
--   $$
--   \Lambda=\max\{\|f\|_\infty\cdot q^{-k},\ \sqrt\Gamma\}.
--   $$
--
--   The smoothness budget for $f$ in Lemmas 4.13 and 4.14 is $q^t\Lambda$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.13, p.32

import Mathlib
import Definitions.Def_RLCDiscrepancy_capacity

namespace RLCDiscrepancy

/-- **The level Λ := max{∥f∥∞ · q^{−k}, √Γ}** of Lemma 4.13. Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.13, p.32:
"Set Λ := max{∥f∥∞ · q^{−k}, √Γ}." -/
noncomputable def smoothLambda {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ) (k : ℕ) (Γ : ℝ) : ℝ :=
  max (supNorm f * ((Fintype.card F : ℝ) ^ k)⁻¹) (Real.sqrt Γ)

end RLCDiscrepancy


