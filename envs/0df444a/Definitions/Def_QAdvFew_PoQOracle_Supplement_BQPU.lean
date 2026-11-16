-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_BQPU
-- name    : QAdvFew_PoQOracle_Supplement_BQPU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:13:39.787205+00:00
-- url     : https://prove2.me/theorems/2420bd58-961a-420b-ba6a-bfaee15edbc1
-- title:
--   $\mathsf{BQP}^{U,C}$ for a unitary oracle
-- statement:
--   For a unitary oracle $U$ and a classical oracle $C$, a language $L$ is in $\mathsf{BQP}^{U,C}$ if a QPT oracle algorithm $A$ satisfies, for every $x\in\{0,1\}^*$,
--
--   $$
--   x\in L\Rightarrow \Pr[A^{U,C}(x)\to1]\ge\tfrac23,\qquad x\notin L\Rightarrow \Pr[A^{U,C}(x)\to1]\le\tfrac13 .
--   $$
--
--   The promise version requires these conditions only on yes- and no-instances. With $C$ the constant-$0$ oracle this is $\mathsf{BQP}^U$ of Definition 3.6.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.6 and the promise-problem convention, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_UQFamily

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- The class `BQP^{U,C}` of languages, for a unitary oracle `U` and a classical oracle `C`
(Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Definition 3.6, p. 13 (PDF p. 15): "`L ∈ BQP^U` if there is a QPT oracle algorithm `A^U` such
that … `x ∈ L ⇒ Pr[A^U(x) → 1] ≥ 2/3`, `x ∉ L ⇒ Pr[A^U(x) → 1] ≤ 1/3`"; §3.2.3: "multiple
oracles may be listed in a superscript").

**Formalization Note** A QPT oracle algorithm is a uniform, polynomially bounded `UQFamily`. With
`C = fun _ => false` the classical oracle gates do nothing and this is `BQP^U`. -/
def BQPU {ar : ℕ → ℕ → ℕ} (U : UOracle ar) (C : Oracle) : Set (Set Str) :=
  {L | ∃ Q : UQFamily ar, Q.Uniform ∧ Q.PolyBounded ∧ ∀ x : Str,
    (x ∈ L → (2 : ℝ) / 3 ≤ Q.accept U C x) ∧ (x ∉ L → Q.accept U C x ≤ (1 : ℝ) / 3)}

/-- The promise version of `BQP^{U,C}` (p. 13, PDF p. 15: "For a promise problem `(L_yes, L_no)`,
the same acceptance and verification conditions are required only on promised inputs"). -/
def PromiseBQPU {ar : ℕ → ℕ → ℕ} (U : UOracle ar) (C : Oracle) : Set PromiseProblem :=
  {Pp | ∃ Q : UQFamily ar, Q.Uniform ∧ Q.PolyBounded ∧ ∀ x : Str,
    (x ∈ Pp.yes → (2 : ℝ) / 3 ≤ Q.accept U C x) ∧ (x ∈ Pp.no → Q.accept U C x ≤ (1 : ℝ) / 3)}

end QAdvFew.PoQOracle.Supplement


