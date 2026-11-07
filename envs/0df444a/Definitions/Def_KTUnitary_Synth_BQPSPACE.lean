-- Prove2me | Definitions.Def_KTUnitary_Synth_BQPSPACE
-- name    : KTUnitary_Synth_BQPSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:34:02.550635+00:00
-- url     : https://prove2.me/theorems/f5840b5d-5d1e-4a1d-afaa-a7d9165ee7f5
-- title:
--   The class $\mathsf{BQPSPACE}^L$
-- statement:
--   A promise problem $(Y,N)$ is in $\mathsf{BQPSPACE}^L$ if there are an FPTEAS encoding $f$, a space-uniform family $\{C_n\}$ of valid $L$-oracle quantum circuits (general CPTP gates) on $n+\mathrm{poly}(n)$ qubits and a designated output qubit printed with the circuit, such that for every $x\in\{0,1\}^n$ the probability of reading $1$ on the output qubit of $\Lambda_n(|x0^a\rangle\langle x0^a|)$ is at least $2/3$ if $x\in Y$ and at most $1/3$ if $x\in N$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.6, p. 15

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_QCircuit
import Definitions.Def_KTUnitary_Synth_ancPad
import Definitions.Def_KTUnitary_Synth_SpaceUniform
import Definitions.Def_KTUnitary_Synth_PromiseProblem

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

open Classical in
/-- **The class `BQPSPACE^L` of promise problems** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.6, p. 15): "A promise
problem `Π` is in `BQPSPACE^L` if there exists a space-uniform family of `L`-oracle quantum circuits
`{C_n}` on `n + a(n) ≤ poly(n)` qubits such that for every `x ∈ {0,1}^n` that is in the promise of
`Π`, measuring a designated output qubit of `C_n` applied to `|x⟩|0^a⟩` yields `Π(x)` with probability
at least `2/3`."

Here: an encoding `f` with an FPTEAS, a space-uniform family `C n` of valid (CPTP-gate) `L`-oracle
circuits on `N` qubits with `n ≤ N ≤ n + p(n)`, and an output wire `o n`, such that for every
`x ∈ {0,1}^n` the probability `Σ_{z : z_{o n} = 1} Λ(|x0^a⟩⟨x0^a|)_{zz}` of reading `1` is at least `2/3`
if `x ∈ Y` and at most `1/3` if `x ∈ N`.

**Formalization Note** `x` on the first `n` wires; space uniformity by bit queries
(`SpaceUniform`).

**Formalization Note (designated output qubit)** The output wire `o n` is part of the family: the
uniformity machine prints it together with the circuit (`tup [(C n).code, bin (o n)]`). A wire chosen
outside the description would be non-uniform advice: with `C n` holding a `|0⟩` and a `|1⟩` wire, a
free `o n` would decide every unary language. -/
def BQPSPACE (L : Oracle) : Set PromiseProblem :=
  {pr | ∃ (f : Str → ℝ) (C : ℕ → QCircuit) (o : (n : ℕ) → Fin (C n).N) (p : Polynomial ℕ),
    HasFPTEAS f ∧
    SpaceUniform (fun n : ℕ => tup [unary n]) (fun n => tup [(C n).code, Nat.bits (o n)])
      (fun n => (C n).gateCodes) ∧
    ∀ n : ℕ, (C n).Valid f ∧ ∃ h : n ≤ (C n).N, (C n).N ≤ n + p.eval n ∧
      ∀ x : Bits n,
        (List.ofFn x ∈ pr.1 → (2 / 3 : ℝ) ≤ ∑ z : Bits (C n).N, if z (o n) = true then
          ((C n).channel f L (Matrix.vecMulVec (ancPad h (Pi.single x 1))
            (star (ancPad h (Pi.single x 1)))) z z).re else 0) ∧
        (List.ofFn x ∈ pr.2 → (∑ z : Bits (C n).N, if z (o n) = true then
          ((C n).channel f L (Matrix.vecMulVec (ancPad h (Pi.single x 1))
            (star (ancPad h (Pi.single x 1)))) z z).re else 0) ≤ 1 / 3)}

end KTUnitary.Synth


