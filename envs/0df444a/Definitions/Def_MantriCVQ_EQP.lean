-- Prove2me | Definitions.Def_MantriCVQ_EQP
-- name    : MantriCVQ_EQP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:46.317667+00:00
-- url     : https://prove2.me/theorems/ff796ace-07e0-4ae7-9c11-c0d8ef31e0c0
-- title:
--   The class $\mathsf{EQP}^O$ over a gate set
-- statement:
--   $\mathsf{EQP}^O$ over $G$ is the class of languages $L$ decided **exactly** by a uniform polynomial-size family of circuits over $G$ with oracle gates: the family accepts every $x\in L$ with probability exactly $1$ and every $x\notin L$ with probability exactly $0$.
--
--   The generator does not see the oracle and sees only the input length. Without this uniformity the class would contain every unary language by hardwiring.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_ExactFamily

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The class `EQP^O` over the gate set `G` (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33),
§3.1, p. 14 (PDF p. 16): "A uniform family of polynomial-size quantum circuits over this gate set,
with oracle gates, decides a language L exactly if it accepts every string in L with probability one
and every other string with probability zero. The class EQP^O consists of the languages decided
exactly by such families"). -/
def EQP (G : List Gate) (O : Oracle) : Set (Set Str) :=
  {L | ∃ F : ExactFamily G, F.Uniform ∧ F.PolyBounded ∧
    ∀ x : Str, (x ∈ L → F.acceptProb O x = 1) ∧ (x ∉ L → F.acceptProb O x = 0)}

end MantriCVQ


