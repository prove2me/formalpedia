-- Prove2me | Definitions.Def_KSPolySign_IsDualPair
-- name    : KSPolySign_IsDualPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:58.661723+00:00
-- url     : https://prove2.me/theorems/2a7979e2-aee8-4a49-9cdd-ada80be7da94
-- title:
--   Dual multipliers of the potential program
-- statement:
--   Given primal matrices $U,V$ at $y$, a pair $(W,Z)$ of **dual multipliers** consists of positive definite matrices with
--   $$\mathrm{tr}[W+Z]=1,\qquad W = UK_y(Z)U+\rho U^2,\qquad Z = VK_y(W)V+\rho V^2,$$
--   the equations (7) of Lemma 3.7.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(a), Eq. (7), p.19 (PDF p.19)

import Mathlib
import Definitions.Def_KSPolySign_coupling
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Dual multipliers.** `(W, Z)` is a pair of dual multipliers for the primal matrices `(U, V)` at `y`
when `W, Z ≻ 0` and Eq. (7) holds:
`tr[W + Z] = 1`, `W = U K_y(Z) U + ρU²`, `Z = V K_y(W) V + ρV²`.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(a), Eq. (7), p.19 (PDF p.19). -/
def IsDualPair {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (ρ : ℝ) (y : Fin k → ℝ)
    (U V W Z : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  W.PosDef ∧ Z.PosDef ∧ (W + Z).trace = 1 ∧
    W = U * coupling C y Z * U + ((ρ : ℝ) : ℂ) • (U * U) ∧
    Z = V * coupling C y W * V + ((ρ : ℝ) : ℂ) • (V * V)

end KSPolySign


