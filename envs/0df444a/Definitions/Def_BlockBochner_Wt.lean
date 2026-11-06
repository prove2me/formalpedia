-- Prove2me | Definitions.Def_BlockBochner_Wt
-- name    : BlockBochner_Wt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:48.325906+00:00
-- url     : https://prove2.me/theorems/9aa8ec45-710f-4d99-a6e7-329d62ff4f4c
-- title:
--   $\tilde W_i=H_T\cap(H_T\cap W_i^\perp)^\perp$
-- statement:
--   For $T\subseteq[n]$ and $i\in[n]$, $\tilde W_i=H_T\cap(H_T\cap W_i^\perp)^\perp$, the part of $H_T$ orthogonal to the vectors of $H_T$ that $P_i$ annihilates.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.2, p.21

import Mathlib
import Definitions.Def_BlockBochner_HT

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **`W̃_i = H_T ∩ (H_T ∩ W_i^⊥)^⊥`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.2, p.21.

**Formalization Note** A subspace of `H`; the orthogonal complement `(H_T ∩ W_i^⊥)^⊥` is taken in
`H`, as on the page. -/
noncomputable def Wt {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (T : Finset (Fin n)) (i : Fin n) :
    Submodule ℝ H :=
  HT W T ⊓ (HT W T ⊓ (W i : Submodule ℝ H)ᗮ)ᗮ

end BlockBochner


