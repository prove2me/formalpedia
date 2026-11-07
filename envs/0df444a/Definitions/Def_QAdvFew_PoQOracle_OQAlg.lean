-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_OQAlg
-- name    : QAdvFew_PoQOracle_OQAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:24.680687+00:00
-- url     : https://prove2.me/theorems/fc780b07-57f0-4bab-99a8-58bf68458c95
-- title:
--   Input-free oracle quantum algorithms
-- statement:
--   A family of oracle quantum algorithms indexed by $N$: at index $N$, an oracle circuit started in $|0\cdots0\rangle$, whose first wire is measured at the end. The input of Lemma 3.10 is accessed only as the oracle.
--
--   The family is **uniform in $\log N$** if a polynomial-time computable map sends the binary expansion of $N$ to the circuit at index $N$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 3.10(1), p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OInstr

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A family of input-free oracle quantum algorithms indexed by `N` (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Lemma 3.10(1), p. 14
(PDF p. 16): "a quantum algorithm `A` making `polylog(N)` queries to its input and running in time
`polylog(N)`"): at index `N`, an oracle circuit on `W N + 1` qubits, started in `|0…0⟩`, whose wire
`0` is measured at the end. The input is accessed only as the oracle. -/
structure OQAlg where
  W : ℕ → ℕ
  circ : (N : ℕ) → OCirc (W N + 1)

namespace OQAlg

/-- `Pr[A^O → 1]` at index `N`. -/
noncomputable def accept (Q : OQAlg) (O : Oracle) (N : ℕ) : ℝ :=
  ∑ y : Bits (Q.W N + 1),
    if y 0 then ‖(Q.circ N).run O (basisState fun _ => false) y‖ ^ 2 else 0

/-- Uniformity in `log N`: a polynomial-time computable map sends the binary expansion of `N` (of
length about `log₂ N`) to the work-qubit count and the circuit at index `N`. -/
def Uniform (Q : OQAlg) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ N : ℕ, f (Nat.bits N) = encNat (Q.W N) ++ (Q.circ N).enc

end OQAlg

end QAdvFew.PoQOracle


