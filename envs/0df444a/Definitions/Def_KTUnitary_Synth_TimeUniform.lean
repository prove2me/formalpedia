-- Prove2me | Definitions.Def_KTUnitary_Synth_TimeUniform
-- name    : KTUnitary_Synth_TimeUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:04.75208+00:00
-- url     : https://prove2.me/theorems/9fbbaf0d-c078-41cd-b696-8605fa4edc08
-- title:
--   Time-uniform family of descriptions
-- statement:
--   A family of descriptions $(d_i)_{i\in I}$ with parameter strings $(s_i)_{i\in I}$ is **time-uniform** if one deterministic Turing machine $M$ without oracle and one polynomial $p$ satisfy: for every $i$, on input $s_i$, $M$ halts within $p(|s_i|)$ steps and outputs $d_i$.
--
--   Circuit families $\{C_{n,\varepsilon}\}$ use the parameter string $(1^n,1^\lambda)$ with $\varepsilon=2^{-\lambda}$, and families $\{C_n\}$ use $1^n$ ("we will always encode the parameter labeled $n$ in unary").
--
--   **Formalization Note** The uniformity machine has no oracle; oracle access enters only through the oracle gates of the described circuit. The output is read from the work tape at the halting step, which computes the same descriptions as a write-only output tape.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.5, p. 14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Time-uniform family of descriptions** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.5, p. 14): "A family `{C_x}` of
quantum circuits is time-uniform if there exists a polynomial-time Turing machine `M` with a
write-only output tape such that `M(x)` outputs a description of `C_x`."

Here a family is indexed by `i : ι`, its parameter string is `idx i` and its description is
`d i`. It is time-uniform if one machine `M` without oracle and one polynomial `p` are such that,
for every `i`, `M` on input `idx i` halts within `p(|idx i|)` steps with output `d i`.

**Formalization Note** The uniformity machine has no oracle (it runs with `fun _ => false`); oracle
access enters only through the oracle gates of the circuit it describes. "When a circuit family is
indexed by several parameters, such as `{C_{n,ε}}`, we regard it as a family indexed by a single
binary string encoding those parameters" (p. 14): the mission uses `idx (n, l) = tup [1^n, 1^l]`
for `ε = 2^{−l}`, and `idx n = tup [1^n]`. The output is read off the work tape at the halting
step; a write-only output tape computes the same descriptions within the same time bound. -/
def TimeUniform {ι : Type} (idx : ι → Str) (d : ι → Str) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ i : ι,
    M.result (fun _ => false) (idx i) (p.eval (idx i).length) ≠ none ∧
    M.output (fun _ => false) (idx i) (p.eval (idx i).length) = d i

end KTUnitary.Synth


