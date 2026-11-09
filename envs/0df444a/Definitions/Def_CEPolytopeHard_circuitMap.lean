-- Prove2me | Definitions.Def_CEPolytopeHard_circuitMap
-- name    : CEPolytopeHard_circuitMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:53.892514+00:00
-- url     : https://prove2.me/theorems/2cdd3f8f-0e1c-4a7e-9b3c-afe199047b10
-- title:
--   Polynomial map $f:[0,1]^d\to[0,1]^d$ of a generalized circuit
-- statement:
--   For a generalized circuit with $d$ nodes, a tolerance $\tau$ and a degree $p$, the **polynomial map** $f : [0,1]^d \to [0,1]^d$ has coordinates
--   $$
--   f(x)_i = f_i(x_{a_i}, x_{b_i}),
--   $$
--   where $f_i$ is the Bernstein approximation of degree $p$ of the gate map $h_i$ of gate $i$, and $a_i, b_i$ are the inputs of gate $i$. Its approximate fixed points encode approximate circuit assignments (proof of Theorem 4(i), "A polynomial map").
--
--   **Formalization Note** A gate with fewer than two inputs receives $0$ in the unused argument, which its gate map ignores.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), proof of Theorem 4(i), p.20

import Mathlib
import Definitions.Def_CEPolytopeHard_GCircuit
import Definitions.Def_CEPolytopeHard_gateMap
import Definitions.Def_CEPolytopeHard_bern

set_option autoImplicit false

namespace CEPolytopeHard

/-- The **polynomial map `f : [0, 1]^d → [0, 1]^d` of a generalized circuit** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, proof of
Theorem 4(i), "A polynomial map", p.20): coordinate `i` is the Bernstein approximation of degree
`p` of the gate map `h_i` of gate `i`, evaluated at the values `x_{a_i}, x_{b_i}` of its inputs:
`f(x)_i = f_i(x_{a_i}, x_{b_i})`.

**Formalization Note** A gate with fewer than two inputs receives `0` in the unused argument, which
its gate map ignores. -/
noncomputable def circuitMap (τ : ℝ) (p : ℕ) (C : GCircuit) (x : Fin C.d → ℝ) : Fin C.d → ℝ :=
  fun i => bern p (gateMap τ (C.gates.get i)) (C.valO x (C.gates.get i).argA)
    (C.valO x (C.gates.get i).argB)

end CEPolytopeHard


