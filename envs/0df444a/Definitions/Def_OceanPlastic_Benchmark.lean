-- Prove2me | Definitions.Def_OceanPlastic_Benchmark
-- name    : OceanPlastic_Benchmark
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:51.470484+00:00
-- url     : https://prove2.me/theorems/9f180cd3-16f5-4fb2-97e4-9d9fb939efec
-- title:
--   Benchmark Case: collector utility, total volume, processor objective and the closed forms $V^B$, $\Pi^B_C$, $\Pi^B_P$
-- statement:
--   In the Benchmark Case there is no firm. A collector paid $h$ per unit who collects $q$ units has utility
--   $$hq-\frac{k q^2}{2},$$
--   and the total collected volume at unit payment $h$ is $q_t(h)=Mh/k$. The processor chooses $h$ to maximize $(p_m-h)\,q_t(h)$.
--
--   The benchmark outcomes are the closed forms of Proposition 1,
--   $$V^B=\frac{Mp_m}{2k},\qquad \Pi^B_C=\Pi^B_P=\frac{Mp_m^2}{4k}.$$
--
--   These quantities are the baseline against which the firm's additional volume and its social and environmental impacts are measured. Proposition 1 in this mission certifies that the closed forms are the equilibrium of the benchmark game.
--
--   **Formalization Note** The module declares `collectorUtility`, `qt`, `processorObjB`, `VB`, `PiBC`, `PiBP` in the namespace `OceanPlastic.Params`. The collectors' total income is the gross payment received, not their net utility.
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, §3.1, pp.7–8, Proposition 1, p.8

import Mathlib
import Definitions.Def_OceanPlastic_Params

namespace OceanPlastic

namespace Params

/-- **A collector's utility** `h q − k q² / 2`: a collector who receives `h` per unit and collects
`q` units. Baron–Romero–Zhang–Zhou, MSOM, doi:10.1287/msom.2022.0643, §3.1, p. 8
("max_q {hq − kq²/2}"); in Case O the unit payment is `h + r_c` (§3.2(a), p. 10). -/
noncomputable def collectorUtility (P : Params) (h q : ℝ) : ℝ :=
  h * q - P.k * q ^ 2 / 2

/-- **Total collected volume** `q_t(h) = M h / k`, §3.1, p. 8, and §3.2(a), p. 10 (with argument
`h + r_c`). `proposition_1` shows that it is `M` times a collector's optimal choice. -/
noncomputable def qt (P : Params) (h : ℝ) : ℝ :=
  P.M * h / P.k

/-- **The processor's objective in the Benchmark Case**, `(p_m − h) q_t(h)`, §3.1, p. 7. -/
noncomputable def processorObjB (P : Params) (h : ℝ) : ℝ :=
  (P.pm - h) * P.qt h

/-- **Benchmark recycled volume** `V^B = M p_m / (2k)`, Proposition 1, p. 8. -/
noncomputable def VB (P : Params) : ℝ :=
  P.M * P.pm / (2 * P.k)

/-- **Benchmark collectors' total income** `Π^B_C = M p_m² / (4k)`, Proposition 1, p. 8.

**Formalization Note** The income is the gross payment received (price times volume), not the
collectors' net utility, which would be half of it. -/
noncomputable def PiBC (P : Params) : ℝ :=
  P.M * P.pm ^ 2 / (4 * P.k)

/-- **Benchmark processor's profit** `Π^B_P = M p_m² / (4k)`, Proposition 1, p. 8. -/
noncomputable def PiBP (P : Params) : ℝ :=
  P.M * P.pm ^ 2 / (4 * P.k)

end Params

end OceanPlastic


