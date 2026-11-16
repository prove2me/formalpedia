-- Prove2me | Definitions.Def_PreprocOWS_Supplement_QAccess
-- name    : PreprocOWS_Supplement_QAccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:08:48.408236+00:00
-- url     : https://prove2.me/theorems/0c4c736a-6845-43b1-bb26-735b4f622f12
-- title:
--   Query access to $R$ on the workspace: $A_R=(O_RU)^T$ and the pre-query isometry $V_R$
-- statement:
--   In the §10 variants of the oracle state games the adversary also queries the random oracle $R:[K]\times[N]\to\{\pm1\}$. Query access on the $M$-dimensional workspace consists of
--
--   1. a **query map** $q:[M]\to\{\text{none}\}\cup([K]\times[N])$, giving the oracle $O_R|s\rangle = R(q(s))|s\rangle$ with $R(\text{none}) = 1$;
--   2. unitaries $U_1,\dots,U_T$ on $\mathbb C^M$, giving the **post-query computation**
--   $$
--   A_R = (O_R U)^T = O_R U_T\cdots O_R U_1 .
--   $$
--
--   With $t+1$ further unitaries $U'_1,\dots,U'_{t+1}$ and a fixed isometry $V_0:\mathbb C^N\to\mathbb C^M$, the **pre-query isometry** is
--   $$
--   V_R = U'_{t+1}(O_R U'_t)\cdots(O_R U'_1)\,V_0 ,
--   $$
--   where $U'_{t+1}$ is the computation between the last pre-query and the arbitrary phase query.
--
--   The query map and all unitaries are fixed independently of $R$ and of the challenge.
--
--   **Formalization Note** The paper uses one unitary $U$ and a phase query on a designated register; a general query map and distinct $U_i$ contain that form, as in the base mission's algorithm model.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §10, p.43 (PDF p.46); §10.1.1, p.44 (PDF p.47); §10.3, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_PreprocOWS_run
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Query access to `R` on the workspace** for the §10 variants of the oracle state games,
Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §10, p.43 (PDF p.46) and
§10.1.1, p.44 (PDF p.47): a query map `q : [M] → Option ([K] × [N])` and `T` unitaries on `ℂ^M`.
A query to `R` applies `O_R |s⟩ = R(q(s)) |s⟩` (with `R(none) = 1`), and the `T` post-queries form
`A_R = (O_R U)^T = O_R U_T ⋯ O_R U_1`.

**Formalization Note.** The page uses one fixed unitary `U` and a phase query on a query register; a
general query map and distinct `U_i` include that form. `q` and `U` are fixed independently of `R`
and of the challenge. -/
structure QAccess (K N M T : ℕ) where
  q : Fin M → Option (Fin K × Fin N)
  U : Fin T → Matrix.unitaryGroup (Fin M) ℂ

/-- The phase oracle `O_R = diag(R(q(s)))_s` on `ℂ^M` of a query access (arXiv:2610.02101, §10.1.1,
p.44). -/
def QAccess.oracle {K N M T : ℕ} (Q : QAccess K N M T) (R : Oracle K N) :
    Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal fun s => optSgn R (Q.q s)

/-- The `T`-query post-processing `A_R = (O_R U)^T` (arXiv:2610.02101, §10.1.1, p.44, PDF p.47). -/
def QAccess.postRun {K N M T : ℕ} (Q : QAccess K N M T) (R : Oracle K N) :
    Matrix (Fin M) (Fin M) ℂ :=
  layeredRun (Q.oracle R) (fun i => (Q.U i : Matrix (Fin M) (Fin M) ℂ))

/-- The pre-query isometry `V_R = U'_{t+1} (O_R U'_t) ⋯ (O_R U'_1) V_0 : ℂ^N → ℂ^M` that includes `t`
queries to `R` before the arbitrary phase query (arXiv:2610.02101, §10.3, p.49, PDF p.52), for a fixed
isometry `V_0` (fixed ancillas absorbed), fixed unitaries `U'_1, …, U'_t` on `ℂ^M` before the
pre-queries and a fixed unitary `U'_{t+1}` (`Ufin`) between the last pre-query and the arbitrary phase
query (§3.1, p.11: an algorithm is `U_1, O_R, …, U_t, O_R, U_{t+1}`), with the same oracle `O_R` as
`Q`.

**Formalization Note.** `Ufin` cannot be absorbed elsewhere: without it the last pre-query `O_R` would
sit directly before the arbitrary phase query `O_f` and merge into it. -/
def QAccess.preIso {K N M T t : ℕ} (Q : QAccess K N M T) (Upre : Fin t → Matrix.unitaryGroup (Fin M) ℂ)
    (Ufin : Matrix.unitaryGroup (Fin M) ℂ) (V₀ : Matrix (Fin M) (Fin N) ℂ) (R : Oracle K N) :
    Matrix (Fin M) (Fin N) ℂ :=
  (Ufin : Matrix (Fin M) (Fin M) ℂ) *
    layeredRun (Q.oracle R) (fun i => (Upre i : Matrix (Fin M) (Fin M) ℂ)) * V₀

end PreprocOWS.Supplement


