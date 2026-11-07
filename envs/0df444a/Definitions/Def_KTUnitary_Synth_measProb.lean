-- Prove2me | Definitions.Def_KTUnitary_Synth_measProb
-- name    : KTUnitary_Synth_measProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:03.270303+00:00
-- url     : https://prove2.me/theorems/7c257578-f5dc-441a-8882-174774f13672
-- title:
--   Probability of a measurement outcome
-- statement:
--   For an $N$-qubit vector $v$ and a set $S$ of basis states, $\sum_{z\in S}|v_z|^2$: the probability that measuring all qubits in the computational basis gives an outcome in $S$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.6 and 6.1, pp. 15, 24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

open Classical in
/-- **Probability of a measurement outcome** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.6 and 6.1, pp. 15 and 24:
"measuring a designated output qubit/register … yields … with probability"): for an `N`-qubit
vector `v` and a set `S` of computational basis states, `Σ_{z ∈ S} |v_z|²`, the probability that
measuring all qubits of `v` in the computational basis gives an outcome in `S`. -/
noncomputable def measProb {N : ℕ} (v : Bits N → ℂ) (S : Bits N → Prop) : ℝ :=
  ∑ z, if S z then ‖v z‖ ^ 2 else 0

end KTUnitary.Synth


