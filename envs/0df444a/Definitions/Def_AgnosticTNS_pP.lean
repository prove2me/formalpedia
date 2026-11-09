-- Prove2me | Definitions.Def_AgnosticTNS_pP
-- name    : AgnosticTNS_pP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:19.845217+00:00
-- url     : https://prove2.me/theorems/1c199d7b-0e50-4493-ba9e-69ea99f807b8
-- title:
--   Residual size $p_i$
-- statement:
--   At step $i$, $p_i:=\max\{1,\lceil\log_d\Lambda_i\rceil\}$, the maximal number of residual qudits kept after step $i$.
--
--   **Formalization Note** For $\Lambda\ge1$, $\lceil\log_d\Lambda\rceil$ is the least $k$ with $\Lambda\le d^k$, i.e. `Nat.clog d Λ`.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 3.2, p.18

import Mathlib
import Definitions.Def_AgnosticTNS_LambdaP

namespace AgnosticTNS

/-- **The residual size `p_i := max{1, ⌈log_d Λ_i⌉}`**, §3.2, p.18 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).

**Formalization Note** For `Λ ≥ 1` and `d ≥ 2`, `⌈log_d Λ⌉` is the least `k` with `Λ ≤ d^k`, which is
`Nat.clog d Λ`. -/
noncomputable def pP {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (χ : ℕ) (Ls : LearningSequence n)
    (ε ϑ : ℝ) (i : Fin Ls.L) : ℕ :=
  max 1 (Nat.clog d (LambdaP G χ Ls ε ϑ i))

end AgnosticTNS


