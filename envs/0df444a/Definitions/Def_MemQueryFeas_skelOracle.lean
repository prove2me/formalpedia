-- Prove2me | Definitions.Def_MemQueryFeas_skelOracle
-- name    : MemQueryFeas_skelOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:37:57.069264+00:00
-- url     : https://prove2.me/theorems/27923b34-31ec-449b-86ae-869153ccc51a
-- title:
--   Transform oracle of the hard instance
-- statement:
--   The transform separation oracle built from the path oracles of given versions $E^{(i)}_{v',p}$, with the standing parameters $N_p=\lfloor\log(1/\varepsilon)/(2Pp\log d)\rfloor$ and $\delta_p^{(i)}=d^{-1}\varepsilon^{(p-1)/(2P)}d^{-pi}$, and a given final oracle.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 4, p.9; §3.1, p.7

import Mathlib
import Definitions.Def_MemQueryFeas_transOracle
import Definitions.Def_MemQueryFeas_pathOracle
import Definitions.Def_MemQueryFeas_Np
import Definitions.Def_MemQueryFeas_delta

namespace MemQueryFeas

/-- **The transform separation oracle of the hard instance.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 4, p.9 (PDF p.10),
with the standing parameters of §3.1, p.7: `N_p = ⌊log(1/ϵ)/(2Pp log d)⌋` and
`δ_p^(i) = d^{−1}ϵ^{(p−1)/(2P)}λ_p^i`.

`skelOracle d ε P c fin` is `transOracle` built from the path oracles `O_ℓ` of the realized versions
`c p v' i = E^(i)_{v',p}`, with `N = Np d ε P`, accuracies `delta d ε P` and final oracle `fin`. -/
noncomputable def skelOracle (d : ℕ) (ε : ℝ) (P : ℕ) (c : ℕ → List ℕ → ℕ → Op d)
    (fin : List (Vec d) → Vec d → Option (Vec d)) : List (Vec d) → Vec d → Option (Vec d) :=
  transOracle (pathOracle (delta d ε P) c) (Np d ε P) P fin

end MemQueryFeas


