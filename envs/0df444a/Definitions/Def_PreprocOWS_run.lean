-- Prove2me | Definitions.Def_PreprocOWS_run
-- name    : PreprocOWS_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:21:22.685212+00:00
-- url     : https://prove2.me/theorems/94829406-893b-47ca-9f7b-75770c6917a7
-- title:
--   Phase oracle $O_R$ and the run $(O_RU)^T$
-- statement:
--   For an algorithm with query map $q$ and an oracle $R$, the **phase oracle** is the diagonal unitary
--   $$
--   O_R|s\rangle=R(q(s))\,|s\rangle,\qquad R(\bot):=1,
--   $$
--   and the **run** is $(O_RU)^T=O_R\,U_T\cdots O_R\,U_1$.
--
--   This is the query access of the algorithm to the random oracle in the QROM.
--
--   **Formalization Note** `optSgn R o` is $R(o)$ with $R(\bot)=1$.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §3.1, p.11 (PDF p.14); §5.1, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Alg
open Matrix

namespace PreprocOWS

/-- The sign `R(o)` of an optional oracle input: `R(none) = 1` (no query), `R(some p) = sgn (R p)`
(arXiv:2610.02101, §3.1, p.11). -/
def optSgn {K N : ℕ} (R : Oracle K N) : Option (Fin K × Fin N) → ℂ
  | none => 1
  | some p => sgn (R p)

/-- The **phase oracle** `O_R |s⟩ = R(q(s)) |s⟩` of an algorithm `A`, Dong–Lombardi, arXiv:2610.02101
(version of 2026-11-02, sha256 7a0bd8da…), §3.1, p.11 (PDF p.14): the diagonal matrix with entry
`R(q(s)) ∈ {±1}` (and `1` where `q(s) = none`). -/
def phaseOracle {S T K N w : ℕ} (A : Alg S T K N w) (R : Oracle K N) :
    Matrix (Ω S N w) (Ω S N w) ℂ :=
  Matrix.diagonal fun s => optSgn R (A.q s)

/-- The **run** `(O_R U)^T = O_R U_T ⋯ O_R U_1` of the algorithm with oracle `R`
(arXiv:2610.02101, §5.1, p.17, PDF p.20). -/
def run {S T K N w : ℕ} (A : Alg S T K N w) (R : Oracle K N) : Matrix (Ω S N w) (Ω S N w) ℂ :=
  layeredRun (phaseOracle A R) (fun i => (A.U i : Matrix (Ω S N w) (Ω S N w) ℂ))

end PreprocOWS


