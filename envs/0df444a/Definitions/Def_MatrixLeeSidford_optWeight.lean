-- Prove2me | Definitions.Def_MatrixLeeSidford_optWeight
-- name    : MatrixLeeSidford_optWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:37.29308+00:00
-- url     : https://prove2.me/theorems/a288d81c-d9fd-4f72-abae-6e9250b996b1
-- title:
--   Optimal weight $G_*(S)$
-- statement:
--   The **optimal weight** $G_*(S)$ is the minimizer of $f_S$ over the positive definite $m\times m$ matrices. Under the standing assumptions (4.3) it exists, is unique and depends smoothly on $S$ (Lemma 4.4, Section 5.1).
--
--   **Formalization Note** Defined as a chosen minimizer when one exists, and as the junk value $0$ (not positive definite) otherwise; existence and uniqueness are theorems of the mission.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 4.3 and Lemma 4.4, p.34; Section 5.1, p.37

import Mathlib
import Definitions.Def_MatrixLeeSidford_fObj

open Matrix

namespace MatrixLeeSidford

/-- The optimal weight `G_*(S)`, the minimizer of `f_S` over `G ≻ 0` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 4.3 and
Lemma 4.4, p.34; Section 5.1, p.37).

**Formalization Note** A chosen minimizer: if some positive definite `G` minimizes `f_S` over the
positive definite matrices, `optWeight` is one such `G` (by `Classical.choose`); otherwise it is
the junk value `0`, which is not positive definite. Existence and uniqueness are theorems
(Lemma 4.4), not assumptions. -/
noncomputable def optWeight {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  open Classical in
  if h : ∃ G : Matrix (Fin m) (Fin m) ℝ,
      G.PosDef ∧ ∀ G' : Matrix (Fin m) (Fin m) ℝ, G'.PosDef → fObj A S s G ≤ fObj A S s G' then
    h.choose
  else 0

end MatrixLeeSidford


