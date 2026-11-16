-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_kerAvg
-- name    : SATotalCoeffLB_Supplement_kerAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:29:12.045338+00:00
-- url     : https://prove2.me/theorems/e2877883-4b88-4cfe-871c-7790c3a662b8
-- title:
--   The averaging kernel $\mathrm{Ker}_{\mathrm{avg}}$ without extension variables
-- statement:
--   With $W$, $Q$ and $\mathrm{Dep}$ as above, the **averaging kernel** is the linear subspace of $\mathbb R[W, Q]/\langle y^2 - 1 : y \in W \cup Q\rangle$
--
--   $$
--   \mathrm{Ker}_{\mathrm{avg}} := \operatorname{span}_{\mathbb R}\bigl\{\, a(W, Q)\, q_j \;:\; q_j \in Q,\ q_j \notin \mathrm{Dep}(a) \,\bigr\}.
--   $$
--
--   Its generators average to zero over a uniformly random $q \in \{\pm1\}^Q$, for a reason visible from which variables occur; an averaging extended Sherali–Adams refutation holds modulo this subspace.
--
--   **Formalization Note** The kernel is defined as the span exactly as printed (without extension variables, $G = \emptyset$), not by an equivalent description.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.6 (Averaging kernel Ker_avg); Appendix D, p.74

import Mathlib
import Definitions.Def_SATotalCoeffLB_Supplement_depQ

namespace SATotalCoeffLB.Supplement

open SATotalCoeffLB

/-- **The averaging kernel `Ker_avg` without extension variables** (p.6, "Averaging kernel", and
Appendix D, p.74, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)):
`Ker_avg := span_ℝ {a(W, Q) · q_j : q_j ∈ Q, q_j ∉ Dep(a)}`, a linear subspace of
`ℝ[W, Q]/⟨y² − 1 : y ∈ W ∪ Q⟩`.

**Formalization Note** With `G = ∅` the generators are the products `a · q_j` with `q_j` not
appearing in `a` (`depQ`). The kernel is defined as the span exactly as printed, not by an
equivalent characterization. -/
noncomputable def kerAvg {W Q : Type*} [Fintype W] [Fintype Q] [DecidableEq W] [DecidableEq Q] :
    Submodule ℝ (CubeFn (W ⊕ Q)) :=
  Submodule.span ℝ
    {F | ∃ (a : CubeFn (W ⊕ Q)) (j : Q), j ∉ depQ a ∧ F = a * var (Sum.inr j)}

end SATotalCoeffLB.Supplement


