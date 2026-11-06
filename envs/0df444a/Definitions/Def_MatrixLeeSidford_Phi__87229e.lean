-- Prove2me | Definitions.Def_MatrixLeeSidford_Phi__87229e
-- name    : MatrixLeeSidford_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:16.26412+00:00
-- url     : https://prove2.me/theorems/87229e86-4bbc-490e-83a9-498a97d6238a
-- title:
--   Matrix Lewis-weight potential $\Phi_p(y)$
-- statement:
--   For an integer $s\ge2$ and $p=2s$, the **matrix Lewis-weight potential** at $y\in\Omega$ is
--   $$
--   \Phi_p(y)=\frac12\min_{G\succ0}\Big\{\frac1s\operatorname{tr}\big[L_y(G)^s\big]-\log\det G-m\Big\}=\varphi(S(y)).
--   $$
--   When $C,A_1,\dots,A_m$ are diagonal it is the Lee–Sidford potential of the corresponding linear program.
--
--   **Formalization Note** Indexed by $s$; the minimum is an infimum (see $\varphi$).
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (2.1), p.29; Definition 4.3, p.34; Section 5.1, p.37

import Mathlib
import Definitions.Def_MatrixLeeSidford_phi
import Definitions.Def_MatrixLeeSidford_slack

open Matrix

namespace MatrixLeeSidford

/-- The matrix Lewis-weight potential `Φ_p(y) := ½ min_{G ≻ 0} f_y(G)`, `p = 2s` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Eq. (2.1),
p.29; Definition 4.3, Eq. (4.6), p.34), written as `Φ_p(y) = φ(S(y))` (Section 5.1, p.37).

**Formalization Note** Indexed by `s` (the paper writes `p := 2s`). The minimum is an infimum
(see `phi`). -/
noncomputable def Phi {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  phi A (slack A C y) s

end MatrixLeeSidford


