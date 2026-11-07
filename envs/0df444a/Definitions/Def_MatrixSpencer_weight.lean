-- Prove2me | Definitions.Def_MatrixSpencer_weight
-- name    : MatrixSpencer_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:03.210902+00:00
-- url     : https://prove2.me/theorems/5d57847c-7ef2-42ea-8c07-4a88d32da3d9
-- title:
--   The weight $w(X)=e^{-V(X)}$
-- statement:
--   With $V(X)=\mathrm{Tr}\,v(X)$ for $\|X\|<1$ and $V(X)=+\infty$ otherwise, the weight is
--   $$w(X)=e^{-V(X)},$$
--   that is, $w(X)=\exp(-\mathrm{Tr}\,v(X))$ if $\|X\|<1$ and $w(X)=0$ otherwise. Here $\|\cdot\|$ is the operator norm.
--
--   **Formalization Note** The value $+\infty$ of $V$ is encoded by the real value $0$ of $w$.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8; proof of Theorem 2.5, Step 2, p.9

import Mathlib
import Definitions.Def_MatrixSpencer_vPot
import Definitions.Def_MatrixSpencer_specTrace
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer

/-- **The weight `w(X) = e^{−V(X)}`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8: "we let V(X) = Tr v(X) for ‖X‖ < 1, where we extend the value of potential by +∞
outside the unit operator norm ball", and Step 2, p.9: "Let w(X) = e^{−V(X)}".

**Formalization Note.** `V = +∞` is encoded by the real weight: `w X = exp(−Tr v(X))` if `‖X‖ < 1`,
and `w X = 0` otherwise. `‖·‖` is the operator norm (p.6). -/
noncomputable def weight {d : ℕ} (α β : ℝ) (p : ℕ) (X : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  open Classical in if ‖X‖ < 1 then Real.exp (-specTrace (vPot α β p) X) else 0

end MatrixSpencer


