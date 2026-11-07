-- Prove2me | Definitions.Def_KTUnitary_Synth_emb
-- name    : KTUnitary_Synth_emb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:14.356464+00:00
-- url     : https://prove2.me/theorems/2dd02384-92cb-4809-9c03-0a58e718e37a
-- title:
--   Unitary embedding of a language
-- statement:
--   For a language $L:\{0,1\}^*\to\{0,1\}$, its **unitary embedding** is the unitary language $\{U_n\}$ with
--   $$U_n\,|x,b\rangle=|x,\ b\oplus L(x)\rangle\qquad (x\in\{0,1\}^{n-1},\ b\in\{0,1\}).$$
--   These are also the oracle gates of an $L$-oracle circuit (Definition 4.4). As in the paper, $L$ also stands for its embedding when it is used as an oracle.
--
--   **Formalization Note** $x$ is the first $n-1$ qubits and $b$ the last. For $n=0$ the formula gives $U_0=1$, which the paper leaves undefined. That each $U_n$ is unitary is proved in the mission's verification file.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.10, p. 16; Definition 4.4, p. 14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Oracle
import Definitions.Def_KTUnitary_Synth_ULang

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

open Classical in
/-- **Unitary embedding of a language** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.10, p. 16): "If `L : {0,1}* → {0,1}`
is a language, the unitary embedding of `L` is the unitary language `𝒰 = {U_n}` whose constituent
unitaries act as `U_n |x, b⟩ = |x, b ⊕ L(x)⟩` for every `x ∈ {0,1}^{n−1}` and `b ∈ {0,1}`." The
same unitaries are the oracle gates of an `L`-oracle circuit (Definition 4.4, p. 14). "We may
sometimes overload `L` to mean both the language and its unitary embedding" (p. 16).

The matrix entry in row `i`, column `j` is `1` if `i` and `j` agree on the first `n − 1` qubits and
the last qubit of `i` is the last qubit of `j` XOR `L` of the first `n − 1` qubits of `j`, and `0`
otherwise.

**Formalization Note** `x` is the first `n − 1` qubits (wires `0, …, n − 2`, read as the string
`x₀ x₁ ⋯`) and `b` is the last qubit. For `n = 0` the formula gives the `1 × 1` identity, `U_0 = 1`
(the paper does not define `U_0`). -/
noncomputable def emb (L : Oracle) : ULang :=
  ULang.ofMatrices fun _ => Matrix.of fun i j =>
    if (List.ofFn i).dropLast = (List.ofFn j).dropLast ∧
      (List.ofFn i).getLast? = ((List.ofFn j).getLast?).map (fun b => xor b (L (List.ofFn j).dropLast))
    then 1 else 0

end KTUnitary.Synth


