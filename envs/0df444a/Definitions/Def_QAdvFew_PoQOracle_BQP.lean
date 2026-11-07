-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_BQP
-- name    : QAdvFew_PoQOracle_BQP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:03.155801+00:00
-- url     : https://prove2.me/theorems/1985b0ae-e6cd-48f1-8a2d-33d695b2e646
-- title:
--   $\mathsf{BQP}^O$
-- statement:
--   A language $L$ is in $\mathsf{BQP}^O$ if there is a QPT oracle algorithm $\mathcal A^O$ such that, for every $x$, $\Pr[\mathcal A^O(x)\to1]\ge 2/3$ if $x\in L$ and $\Pr[\mathcal A^O(x)\to1]\le 1/3$ if $x\notin L$.
--
--   **Formalization Note** A QPT oracle algorithm is a uniform, polynomially bounded family of oracle Clifford+T circuits. The circuit generator has no oracle access, so a nonuniform family, which would decide every unary language, is excluded.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.6, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OQFamily

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The class `BQP^O` for a classical oracle `O` (Goldin, Lombardi, Morimae, *Quantum Advantage has
Few Complexity Implications*, arXiv:2611.05303v1, Definition 3.6, p. 13 (PDF p. 15)): `L ∈ BQP^O` if
there is a QPT oracle algorithm `A^O` such that `Pr[A^O(x) → 1] ≥ 2/3` for `x ∈ L` and
`Pr[A^O(x) → 1] ≤ 1/3` for `x ∉ L`.

**Formalization Note** A QPT oracle algorithm is a uniform, polynomially bounded family of oracle
Clifford+T circuits (`OQFamily`), with the query map `|x, z⟩ ↦ |x, z ⊕ O(x)⟩` (§3.2.2); the circuit
generator has no oracle access. -/
def BQP (O : Oracle) : Set (Set Str) :=
  {L | ∃ Q : OQFamily, Q.Uniform ∧ Q.PolyBounded ∧ ∀ x : Str,
    (x ∈ L → (2 : ℝ) / 3 ≤ Q.accept O x) ∧ (x ∉ L → Q.accept O x ≤ (1 : ℝ) / 3)}

end QAdvFew.PoQOracle


