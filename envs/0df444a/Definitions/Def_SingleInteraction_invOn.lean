-- Prove2me | Definitions.Def_SingleInteraction_invOn
-- name    : SingleInteraction_invOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:31.953198+00:00
-- url     : https://prove2.me/theorems/0809cc52-1df5-427f-8050-15588622e7e7
-- title:
--   Inverse of $QAQ$ on the range of $Q$
-- statement:
--   For an orthogonal projection $Q$ and an operator $A$ with $QAQ$ invertible on the range of $Q$, the inverse of $QAQ$ taken on $\operatorname{ran}Q$, extended by $0$ on its orthogonal complement:
--
--   $$\mathrm{invOn}(Q,A)=Q\,\bigl(QAQ+(I-Q)\bigr)^{-1}Q.$$
--
--   This is the "$(QH_0Q)^{-1}$, where the inverse is taken on the range of $Q$" of §5.1.4 and the "$(H_Q-EI_Q)^{-1}$" of §5.1.6.
--
--   **Formalization Note** The padding $I-Q$ makes the matrix invertible, so no default value of the inverse of a singular matrix enters.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.4, p.60; §5.1.6, p.63

import Mathlib

namespace SingleInteraction

/-- The inverse of `Q A Q` taken on the range of an orthogonal projection `Q` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.4, p.60:
"`H_eff^(2) = −PVQ(QH0Q)^{−1}QVP`, where the inverse is taken on the range of `Q`"; §5.1.6, p.63,
"`(H_Q − E I_Q)^{−1}`").

**Formalization Note** The value is `Q (Q A Q + (1 − Q))⁻¹ Q`. When `Q A Q` is invertible as an operator
on the range of `Q`, `Q A Q + (1 − Q)` is invertible (it is `QAQ` on ran `Q` and the identity on its
complement), and the value is the inverse of `QAQ|_{ran Q}` on ran `Q` and `0` on the complement. This
avoids `Matrix.inv` of the singular matrix `Q A Q`, which is `0`. -/
noncomputable def invOn {ι : Type*} [Fintype ι] [DecidableEq ι] (Q A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  Q * (Q * A * Q + (1 - Q))⁻¹ * Q

end SingleInteraction


