-- Prove2me | Definitions.Def_KTUnitary_Synth_outputState
-- name    : KTUnitary_Synth_outputState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:33:53.419821+00:00
-- url     : https://prove2.me/theorems/0e7d03ea-afd4-4ead-a81e-25689eb7e717
-- title:
--   The state output by a circuit
-- statement:
--   For an $L$-oracle quantum circuit $C$ with encoding $f$ and output wires $o$, the mixed state obtained by applying $C$ to $|0^N\rangle\langle0^N|$ and tracing out all wires except $o$. These are the states $\rho_{0,n}$, $\rho_{1,n}$ of an EFI pair.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38

import Mathlib
import Definitions.Def_KTUnitary_Synth_QCircuit
import Definitions.Def_KTUnitary_Synth_reducedState

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The state output by a circuit** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38: "quantum circuit families
`{C_{0,n}}` and `{C_{1,n}}` whose outputs on security parameter `n` are mixed states `ρ_{0,n}` and
`ρ_{1,n}`"): the circuit `C` (with encoding `f` and oracle `L`) is applied to the all-zero state
`|0^N⟩⟨0^N|`, and the result is reduced to the output wires `out`. -/
noncomputable def outputState (C : QCircuit) (f : Str → ℝ) (L : Oracle) {m : ℕ}
    (out : Fin m ↪ Fin C.N) : Matrix (Bits m) (Bits m) ℂ :=
  reducedState out (C.channel f L (Matrix.of fun z z' =>
    if z = (fun _ => false) ∧ z' = (fun _ => false) then 1 else 0))

end KTUnitary.Synth


