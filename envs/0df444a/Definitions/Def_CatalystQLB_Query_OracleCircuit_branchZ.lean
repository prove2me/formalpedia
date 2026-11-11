-- Prove2me | Definitions.Def_CatalystQLB_Query_OracleCircuit_branchZ
-- name    : CatalystQLB_Query_OracleCircuit_branchZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:52.364762+00:00
-- url     : https://prove2.me/theorems/de4670b8-a940-482a-982b-04b4f0bb984e
-- title:
--   Branch operators $Z_i$ of Notation 74
-- statement:
--   With the segments $V_i$ and $\Pi=|g(x)\rangle\langle g(x)|_Q\otimes I_{RC}$, $\Pi^\perp=I-\Pi$, define
--   $$Z_1=V_1,\qquad Z_i=V_i\,O_f\,\Pi^\perp Z_{i-1}\quad(2\le i\le q).$$
--   $Z_i$ is the part of the circuit up to $V_i$ along which every earlier query to $f$ was made off the point $g(x)$; it is a contraction and does not depend on the value $f(g(x))$.
--
--   **Formalization Note** 1-indexed as in the paper; the unused value at index $0$ is $Z_1$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), §5.3, p.45 (PDF 48), after Eq. (43)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit_segmentOp
import Definitions.Def_CatalystQLB_Query_firstQueryProj

namespace CatalystQLB.Query

open QAlgorithms

namespace OracleCircuit

variable {n ℓ : ℕ}

/-- The branch operators `Z_i` of Notation 74 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), §5.3, p.45 (PDF 48), after Eq. (43):
"`Z_1 := V_1` and `Z_i := V_i O_f Π^⊥ Z_{i−1}` for `2 ≤ i ≤ q`"), with
`Π = |g(x)⟩⟨g(x)|_Q ⊗ I_RC` and `Π^⊥ = I − Π`. `Z_i` is the part of the circuit up to `V_i` on
which no earlier `O_f` query was made with the query register at `g(x)`.

**Formalization Note** 1-indexed as in the paper (`1 ≤ i ≤ q = numF C + 1`); the junk value at
`i = 0` is `Z_1`. -/
noncomputable def branchZ (C : OracleCircuit n ℓ) (f g : Qubits n → Qubits n) (x : Qubits n) :
    ℕ → Matrix (Idx n ℓ) (Idx n ℓ) ℂ
  | 0 => C.segmentOp f g 1
  | 1 => C.segmentOp f g 1
  | i + 2 => C.segmentOp f g (i + 2) * Step.mat f g .queryF *
      (1 - firstQueryProj (g x)) * branchZ C f g x (i + 1)

end OracleCircuit

end CatalystQLB.Query


