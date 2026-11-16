-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_PrincipalMinorCert
-- name    : AutobidSPPE_Supplement_PrincipalMinorCert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:48:44.64659+00:00
-- url     : https://prove2.me/theorems/c95c67f7-a593-422c-aecf-b1b3e4524072
-- title:
--   Principal-minor certificate (60)
-- statement:
--   A number $m$ is a **principal-minor certificate** if
--   $$
--   0<m\le1,\qquad \det(J_s(\alpha))_{II}\ge m\quad(\emptyset\ne I\subseteq[n],\ \alpha\in\mathcal K),
--   $$
--   where $(J_s)_{II}$ is the principal submatrix indexed by $I$. The constants (62) and the step condition (63) are computed from $m$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (60), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_spendJacT
import Definitions.Def_AutobidSPPE_Supplement_boxK

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The principal-minor certificate (60): `0 < m ≤ 1` and
`det(Js(α))_{II} ≥ m` for every nonempty `I ⊆ [n]` and every `α ∈ K` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (60), p.28).

**Formalization Note** `(Js)_{II}` is the principal submatrix indexed by the subtype of `I`. -/
def PrincipalMinorCert {n : ℕ} (vbar vhat ρ : Fin n → ℝ) (m : ℝ) : Prop :=
  0 < m ∧ m ≤ 1 ∧
  ∀ I : Finset (Fin n), I.Nonempty → ∀ α ∈ boxK vhat ρ,
    m ≤ ((spendJacT vbar α).submatrix (fun x : I => (x : Fin n)) (fun x : I => (x : Fin n))).det

end AutobidSPPE.Supplement


