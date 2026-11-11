-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_SpaceUniform
-- name    : UnitaryQIPPSPACE_SpaceUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:25.023089+00:00
-- url     : https://prove2.me/theorems/5167e0c2-39f9-49a9-bf74-fd7473774769
-- title:
--   Space-uniform circuit families (Definition 2.3)
-- statement:
--   A family of circuits $\{C_n\}$ (with $\mathrm{in}(n)$ input qubits) is **space uniform** if there are a deterministic Turing machine $M$ and a polynomial $p$ such that for every $n$:
--   1. $C_n$ uses at most $p(n)$ qubits at every step;
--   2. for every $i\le|C_n|$, the machine on input $(1^n,i)$ halts after visiting at most $p(n)$ tape cells and outputs the description of the $i$-th operation of $C_n$ if $i<|C_n|$, and the empty string if $i=|C_n|$.
--
--   This is the uniformity of $\mathsf{unitaryPSPACE}$: circuits may have exponentially many operations, but each one is computable in polynomial space.
--
--   **Formalization Note** Machines are the published oracle Turing machines `QAdvFew.PoQOracle.OTM` with the empty oracle; their space counts all visited cells, the input included; the running time is not bounded. The empty output at $i=|C_n|$ marks the end of the circuit, so the machine determines the whole circuit (the standard reading); it forces $|C_n|\le 2^{O(p(n))}$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Definition 2.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_Circuit

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- The empty oracle: a deterministic Turing machine without oracle is an oracle Turing machine
(`QAdvFew.PoQOracle.OTM`) run with the oracle that answers every query `false`. -/
def noOracle : Oracle := fun _ => false

/-- **Space-uniform circuit family** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819,
held version sha256 9e357a00…, Definition 2.3, p. 10 (PDF p. 12)): "A family of quantum circuits
`{C_n}` is polynomial-space if there exists a polynomial `p` such that for every `n ∈ ℕ`, the circuit
`C_n` uses at most `p(n)` space. We say that `{C_n}` is space-uniform if it is polynomial-space and
there exists a deterministic Turing machine using space polynomial in `n` that, on input `(1^n, i)`,
outputs the `i`-th operation of `C_n`."

Here `inLen n` is the number of input qubits of `C_n`. There are a machine `M` and a polynomial
`p` such that for every `n`:
* `C_n` uses at most `p(n)` qubits at every step (on `inLen n` input qubits);
* for every `i ≤ |C_n|`, the run of `M` on `tup [1^n, bin(i)]` halts after visiting at most `p(n)`
  tape cells, and its output is the description of the `i`-th operation (counting from `0`) if
  `i < |C_n|`, and the empty string for `i = |C_n|`, which marks the end of the circuit (operation
  codes are nonempty).

**Formalization Note** Machines are the published `QAdvFew.PoQOracle.OTM` with the empty oracle;
their space counts every visited cell, the input cells included, and the running time is not
bounded. The size of `C_n` is not bounded polynomially (it is at most exponential, since the
input `bin(i)` must fit in the space bound). The end marker at `i = |C_n|` makes the circuit, not
only its operations, determined by the machine, as in the standard reading of space uniformity
([MY23]). -/
def SpaceUniform (C : ℕ → Circuit) (inLen : ℕ → ℕ) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ n : ℕ, (C n).space (inLen n) ≤ p.eval n ∧
    ∀ i : ℕ, i ≤ (C n).length → ∃ T : ℕ,
      M.result noOracle (tup [unary n, natCode i]) T ≠ none ∧
      M.space noOracle (tup [unary n, natCode i]) T ≤ p.eval n ∧
      M.output noOracle (tup [unary n, natCode i]) T =
        (if h : i < (C n).length then ((C n).get ⟨i, h⟩).code else [])

end UnitaryQIPPSPACE


