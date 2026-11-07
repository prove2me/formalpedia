-- Prove2me | Definitions.Def_KTUnitary_Synth_acceptProb
-- name    : KTUnitary_Synth_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:33:39.137292+00:00
-- url     : https://prove2.me/theorems/894fdde8-774d-45bd-acaa-928a903635bc
-- title:
--   Acceptance probability of a distinguisher
-- statement:
--   For an $L$-oracle quantum circuit $D$ with encoding $g$, input wires and an output wire $o$, and an input state $\rho$: $\Pr[D(\rho)=1]$, the probability of reading $1$ on wire $o$ after $D$ is applied to $\rho$ on the input wires with all other wires in $|0\rangle$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38

import Mathlib
import Definitions.Def_KTUnitary_Synth_QCircuit
import Definitions.Def_KTUnitary_Synth_placeState

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Acceptance probability of a distinguisher** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38:
`Pr[D_n(ρ) = 1]`): the circuit `D` (with encoding `g` and oracle `L`) is applied to `ρ` loaded on
the input wires `inp` (other wires in `|0⟩`), and wire `o` is measured; the value is the
probability `Σ_{z : z_o = 1} (D(ρ ⊗ |0⟩⟨0|))_{zz}` of reading `1`. -/
noncomputable def acceptProb (D : QCircuit) (g : Str → ℝ) (L : Oracle) {m : ℕ}
    (inp : Fin m ↪ Fin D.N) (o : Fin D.N) (ρ : Matrix (Bits m) (Bits m) ℂ) : ℝ :=
  ∑ z : Bits D.N, if z o = true then (D.channel g L (placeState inp ρ) z z).re else 0

end KTUnitary.Synth


