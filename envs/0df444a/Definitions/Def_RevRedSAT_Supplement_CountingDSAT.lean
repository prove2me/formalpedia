-- Prove2me | Definitions.Def_RevRedSAT_Supplement_CountingDSAT
-- name    : RevRedSAT_Supplement_CountingDSAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:53:40.554954+00:00
-- url     : https://prove2.me/theorems/e92da369-20fc-4dc7-a908-c88f2ad118b1
-- title:
--   The Counting $d$-SAT Assumption (Assumption 4.5)
-- statement:
--   This is Assumption 4.5 of the paper. Let $\lambda(t)=\log_2(t+2)$ and $\eta(t)=\log_2\log_2(t+4)$.
--
--   **Assumption 4.5.** For every fixed clause width $d$ there are a deterministic algorithm and constants $C_d$, $c_d$ such that, for every CNF formula $F$ of width at most $d$ on a listed set of $N$ variables, the algorithm returns the exact number of assignments of the $N$ variables that satisfy $F$ within
--
--   $$\Bigl\lfloor 2^{C_d\,N\eta(N)^2/\sqrt{\lambda(N)}}\;|F|^{c_d}\Bigr\rfloor$$
--
--   steps. Here $N$ counts all listed variables, including those that occur in no clause, and $|F|$ includes this list.
--
--   Theorems 2.5, 8.1, 8.3, 8.6 and 8.7 are stated under this assumption. Unlike Assumptions 4.2 and 4.3, the algorithm and both constants may depend on $d$.
--
--   **Formalization Note** $N$ is the declared variable count $n$ of a formula `MainResults.CNF n`, which `RevRedSAT.encCNF` writes first; the count is `MainResults.numSat`, written in self-delimiting binary.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §4.2, pp.29–30 (Assumption 4.5)

import Mathlib
import Definitions.Def_MainResults
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_encCNF

set_option autoImplicit false

namespace RevRedSAT.Supplement

open RSListDecodingCapacity.AllRates

/-- **The Counting d-SAT Assumption (4.5).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §4.2, p.30: "For every fixed clause width d, there is a deterministic algorithm that returns the
exact number of satisfying assignments of a CNF formula F of width at most d in time
|F|^{O_d(1)} 2^{O_d(Nη(N)²/√λ(N))}, where λ(t) = log2(t + 2) and η(t) = log2(log2(t + 4)). Here N
counts all Boolean variables listed in the input, including those that appear in no clause. The
input length |F| includes this list. The hidden constants and polynomial exponent may depend on d."

For every width `d` there are a machine `M` with finite alphabets, a constant `C` and an exponent
`c` (all depending on `d`) such that on the code of every formula `φ` on the variables
`0, …, n − 1` of width at most `d`, `M` outputs the number of assignments `Fin n → Bool` satisfying
`φ`, in self-delimiting binary, within `⌊2^{C·nη(n)²/√λ(n)} · |F|^c⌋` steps.

**Formalization Note** `N` is the declared number `n` of variables, which the code `encCNF` writes
first; assignments range over all `n` variables, used or not (§4.2: "if a formula has five
satisfying assignments on its occurring variables and two additional unused variables, then it has
5 · 2² = 20"). Unlike Assumptions 4.2 and 4.3, the machine and the constants depend on `d`. -/
def CountingDSAT : Prop :=
  ∀ d : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
    ∃ (C : ℝ) (c : ℕ), ∀ (n : ℕ) (φ : MainResults.CNF n), width φ ≤ d →
      HMBinPacking.OutputsWithin M (encCNF φ) (encNat (MainResults.numSat φ))
        (expBound (C * n * eta n ^ 2 / Real.sqrt (lam n)) (encCNF φ).length c)

end RevRedSAT.Supplement


