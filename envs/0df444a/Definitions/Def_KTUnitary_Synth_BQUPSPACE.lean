-- Prove2me | Definitions.Def_KTUnitary_Synth_BQUPSPACE
-- name    : KTUnitary_Synth_BQUPSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:35:16.721874+00:00
-- url     : https://prove2.me/theorems/8da6cb7c-6f51-4656-9541-7180d7e5d54d
-- title:
--   The class $\mathsf{BQUPSPACE}^{\mathcal O}$
-- statement:
--   Defined as $\mathsf{BQP}^{\mathcal O}$ but with a **space-uniform** family of valid $\mathcal O$-oracle unitary circuits on $n+\mathrm{poly}(n)$ qubits (all eight oracle gates), with a designated output qubit printed with the circuit. A promise problem is in it if measuring that qubit of $C_n|x\rangle|0^a\rangle$ gives the right answer with probability at least $2/3$ on every promise input.
--
--   It appears in Proposition 5.8 and as item 5 of Theorem 6.17.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.6, p. 15; footnote 7, p. 24

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_ancPad
import Definitions.Def_KTUnitary_Synth_measProb
import Definitions.Def_KTUnitary_Synth_PromiseProblem
import Definitions.Def_KTUnitary_Synth_SpaceUniform

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `BQUPSPACE^𝒪` of promise problems** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.6, p. 15, and footnote 7,
p. 24: "`BQUPSPACE^𝒪` is defined the same as in Definition 4.6, but with a family of `𝒪`-oracle
unitary quantum circuits"). A promise problem `(Y, N)` is in it if there are an encoding `f` with an
FPTEAS, a space-uniform family `C n` of `𝒪`-oracle unitary circuits (all eight oracle gate kinds of
Definition 5.5) on `N` qubits with `n ≤ N ≤ n + p(n)`, and a designated output wire `o n`, such that
for every `x ∈ {0,1}^n`, measuring wire `o n` of `C_n |x⟩|0^a⟩` gives `1` with probability at least
`2/3` if `x ∈ Y` and at most `1/3` if `x ∈ N`.

**Formalization Note** Space uniformity by bit queries, with polynomial-length gate descriptions
(`SpaceUniform`); `x` on the first `n` wires.

**Formalization Note (designated output qubit)** The output wire `o n` is part of the family: the
uniformity machine prints it together with the circuit (`tup [(C n).code, bin (o n)]`). A wire chosen
outside the description would be non-uniform advice: with `C n` holding a `|0⟩` and a `|1⟩` wire, a
free `o n` would decide every unary language. -/
def BQUPSPACE (O : ULang) : Set PromiseProblem :=
  {pr | ∃ (f : Str → ℝ) (C : ℕ → UCircuit) (o : (n : ℕ) → Fin (C n).N) (p : Polynomial ℕ),
    HasFPTEAS f ∧
    SpaceUniform (fun n : ℕ => tup [unary n]) (fun n => tup [(C n).code, Nat.bits (o n)])
      (fun n => (C n).gateCodes) ∧
    ∀ n : ℕ, (C n).Valid f ∧ ∃ h : n ≤ (C n).N, (C n).N ≤ n + p.eval n ∧
      ∀ x : Bits n,
        (List.ofFn x ∈ pr.1 → (2 / 3 : ℝ) ≤
          measProb (((C n).unitary f O).mulVec (ancPad h (Pi.single x 1))) (fun z => z (o n) = true)) ∧
        (List.ofFn x ∈ pr.2 →
          measProb (((C n).unitary f O).mulVec (ancPad h (Pi.single x 1))) (fun z => z (o n) = true)
            ≤ 1 / 3)}

end KTUnitary.Synth


