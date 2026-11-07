-- Prove2me | Definitions.Def_KTUnitary_Synth_BQP
-- name    : KTUnitary_Synth_BQP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:32:10.323642+00:00
-- url     : https://prove2.me/theorems/e2f9e876-94a1-4f37-b1f6-118db9bfe870
-- title:
--   The class $\mathsf{BQP}^{\mathcal O}$ with the gates of Definition 5.5
-- statement:
--   A promise problem $(Y,N)$ is in $\mathsf{BQP}^{\mathcal O}$ if there are an FPTEAS encoding $f$, a time-uniform family $\{C_n\}$ of valid $\mathcal O$-oracle unitary circuits on $n+a(n)\le n+\mathrm{poly}(n)$ qubits (all eight oracle gates of Definition 5.5) and a designated output qubit printed with the circuit by the uniformity machine, such that for every $x\in\{0,1\}^n$, measuring the output qubit of $C_n|x\rangle|0^a\rangle$ gives $1$ with probability at least $2/3$ if $x\in Y$ and at most $1/3$ if $x\in N$.
--
--   This is the language class of Proposition 5.8 ("the unitary oracle model for the language classes allows the same gates as in Definition 5.5").
--
--   **Formalization Note** $x$ occupies the first $n$ wires; a language $A$ is in the class when $(A,A^{\mathrm c})$ is.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.8, p. 18; Definition 4.6, p. 15

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_ancPad
import Definitions.Def_KTUnitary_Synth_measProb
import Definitions.Def_KTUnitary_Synth_PromiseProblem
import Definitions.Def_KTUnitary_Synth_TimeUniform

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `BQP^𝒪` of promise problems, with the gates of Definition 5.5** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31),
Proposition 5.8, p. 18: "where the unitary oracle model for the language classes allows the same
gates as in Definition 5.5"; the pattern of Definition 4.6, p. 15, with time uniformity). A promise
problem `(Y, N)` is in it if there are an encoding `f` with an FPTEAS, a time-uniform family `C n` of
`𝒪`-oracle unitary circuits (descriptions computed from `tup [1^n]`) on `N` qubits with
`n ≤ N ≤ n + p(n)`, and a designated output wire `o n`, such that for every `x ∈ {0,1}^n`, measuring
wire `o n` of `C_n |x⟩|0^a⟩` gives `1` with probability at least `2/3` if `x ∈ Y` and at most `1/3`
if `x ∈ N`.

**Formalization Note** `x ∈ {0,1}^n` is placed on wires `0, …, n − 1`, read as the string
`x₀ x₁ ⋯ x_{n−1}`; the ancillas are the last wires. A language `A` is in it when `(A, Aᶜ)` is.

**Formalization Note (designated output qubit)** The output wire `o n` is part of the family: the
uniformity machine prints it together with the circuit (`tup [(C n).code, bin (o n)]`). A wire chosen
outside the description would be non-uniform advice: with `C n` holding a `|0⟩` and a `|1⟩` wire, a
free `o n` would decide every unary language. -/
def BQP (O : ULang) : Set PromiseProblem :=
  {pr | ∃ (f : Str → ℝ) (C : ℕ → UCircuit) (o : (n : ℕ) → Fin (C n).N) (p : Polynomial ℕ),
    HasFPTEAS f ∧ TimeUniform (fun n : ℕ => tup [unary n]) (fun n => tup [(C n).code, Nat.bits (o n)]) ∧
    ∀ n : ℕ, (C n).Valid f ∧ ∃ h : n ≤ (C n).N, (C n).N ≤ n + p.eval n ∧
      ∀ x : Bits n,
        (List.ofFn x ∈ pr.1 → (2 / 3 : ℝ) ≤
          measProb (((C n).unitary f O).mulVec (ancPad h (Pi.single x 1))) (fun z => z (o n) = true)) ∧
        (List.ofFn x ∈ pr.2 →
          measProb (((C n).unitary f O).mulVec (ancPad h (Pi.single x 1))) (fun z => z (o n) = true)
            ≤ 1 / 3)}

end KTUnitary.Synth


