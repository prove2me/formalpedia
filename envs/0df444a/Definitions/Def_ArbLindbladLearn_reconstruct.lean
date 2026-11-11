-- Prove2me | Definitions.Def_ArbLindbladLearn_reconstruct
-- name    : ArbLindbladLearn_reconstruct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:52.856339+00:00
-- url     : https://prove2.me/theorems/d2ff7f10-efb2-433d-abb7-37713002398c
-- title:
--   Algorithm 2: coefficient reconstruction from witness derivatives
-- statement:
--   From witness-derivative values $D(A)=\hat f_A'(0)$, Algorithm 2 (line 25) returns
--   $$\hat h_a=D(A^{\mathrm i}_{a0})-\tfrac12\big(D(P_a)+D(I)\big),\qquad\hat\gamma_{aa}=D(P_a),$$
--   $$\hat\gamma_{ab}=\Big[D(A_{ab})-\tfrac12\big(D(P_a)+D(P_b)\big)\Big]+\mathrm i\Big[\tfrac12\big(D(P_a)+D(P_b)\big)-D(A^{\mathrm i}_{ab})\Big]\quad(a\neq b).$$
--
--   **Formalization Note** Defined on every label; the algorithm reads it on the candidate supports.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Algorithm 2 line 25, p.31

import Mathlib
import Definitions.Def_ArbLindbladLearn_Coeffs
import Definitions.Def_ArbLindbladLearn_pairWitness

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The coefficient reconstruction of Algorithm 2, line 25 (Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.31),
from witness-derivative values `D(A) = f̂′_A(0)`:
`ĥ_a = D(A^i_{a0}) − ½(D(P_a) + D(I))`, `γ̂_aa = D(P_a)`, and for `a ≠ b`
`γ̂_ab = [D(A_ab) − ½(D(P_a) + D(P_b))] + i[½(D(P_a) + D(P_b)) − D(A^i_ab)]`.

**Formalization Note** It is defined on every label; Algorithm 2 reads it on the candidate supports
only. `I = pauliMatrix 0`. -/
def reconstruct {n : ℕ} (D : Op (Qubits n) → ℝ) : Coeffs n where
  h a := D (pairWitnessI a 0) - (D (pauliMatrix a) + D (pauliMatrix 0)) / 2
  γ a b := if a = b then (D (pauliMatrix a) : ℂ) else
    ⟨D (pairWitness a b) - (D (pauliMatrix a) + D (pauliMatrix b)) / 2,
      (D (pauliMatrix a) + D (pauliMatrix b)) / 2 - D (pairWitnessI a b)⟩

end ArbLindbladLearn


