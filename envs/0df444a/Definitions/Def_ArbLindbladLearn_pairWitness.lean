-- Prove2me | Definitions.Def_ArbLindbladLearn_pairWitness
-- name    : ArbLindbladLearn_pairWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:41.578465+00:00
-- url     : https://prove2.me/theorems/03d760df-4bfd-4072-9d89-956d30b22851
-- title:
--   Pair witnesses $A_{ab}$ and $A^{\mathrm i}_{ab}$
-- statement:
--   For labels $a,b$:
--   $$A_{ab}=\frac{P_a+P_b}{\sqrt2},\qquad A^{\mathrm i}_{ab}=\frac{P_a+\mathrm iP_b}{\sqrt2}.$$
--   With $b=0$, $A^{\mathrm i}_{a0}=(P_a+\mathrm iI)/\sqrt2$. Together with the diagonal witnesses $P_a$ they form the witness family of Definition 4.1, whose signals recover the coefficients (Lemma 4.2).
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 4.1, p.25

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The pair witness `A_ab = (P_a + P_b)/√2` (Definition 4.1, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…),
p.25). -/
def pairWitness {n : ℕ} (a b : Pauli n) : Op (Qubits n) :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (pauliMatrix a + pauliMatrix b)

/-- The pair witness `A^i_ab = (P_a + i P_b)/√2` (Definition 4.1, p.25); for `b = 0` it is
`A^i_{a0} = (P_a + iI)/√2` (`pauliMatrix 0 = I`). -/
def pairWitnessI {n : ℕ} (a b : Pauli n) : Op (Qubits n) :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (pauliMatrix a + Complex.I • pauliMatrix b)

end ArbLindbladLearn


