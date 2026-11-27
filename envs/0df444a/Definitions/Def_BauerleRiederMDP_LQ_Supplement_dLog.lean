-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_dLog
-- name    : BauerleRiederMDP_LQ_Supplement_dLog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:42:18.956993+00:00
-- url     : https://prove2.me/theorems/787a5adb-ec30-54ef-b38d-8506201270b1
-- title:
--   The sequence $(d_n)$ of the logarithmic-utility case
-- statement:
--   **The sequence $(d_n)$ of the logarithmic-utility case**, recursion (6.6) (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Theorem 6.1.7 a), eq. (6.6), p.182, PDF 195): $d_0(\rho ) = 0$, $d_n(\rho ) = \log (1 + i) + \sup _{\alpha  \in  \tilde A } \int \int  \log (1 + \alpha  \cdot  z) Q^R(dz|y) \rho (dy) + \int \int  d_{n-1}(\Phi (\rho , z)) Q^R(dz|y) \rho (dy)$.
--
--   **Formalization Note.** Values in `EReal`; the supremum over $\tilde A $ (`AtildePos`, nonempty: $0 \in  \tilde A $) is in `EReal`, the integrals are `eint`; $\Phi $ is the published Bayes operator `Market.Phi`. That $d_n$ is finite is part of the content of Theorem 6.1.7.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 6.1.7 a), eq. (6.6), p.182, PDF 195

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_AtildePos
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_logObj

open MeasureTheory
open BauerleRiederMDP.PartialObs (Market)
open BauerleRiederMDP.RegimeSwitching (eint)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The sequence `(d_n)` of the logarithmic-utility case**, recursion (6.6) (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), Theorem 6.1.7 a), eq. (6.6),
p.182, PDF 195): `d_0(ρ) = 0`,
`d_n(ρ) = log(1 + i) + sup_{α ∈ Ã} ∫∫ log(1 + α · z) Q^R(dz|y) ρ(dy) + ∫∫ d_{n−1}(Φ(ρ, z)) Q^R(dz|y) ρ(dy)`.

**Formalization Note.** Values in `EReal`; the supremum over `Ã` (`AtildePos`, nonempty: `0 ∈ Ã`)
is in `EReal`, the integrals are `eint`; `Φ` is the published Bayes operator `Market.Phi`. That
`d_n` is finite is part of the content of Theorem 6.1.7. -/
noncomputable def dLog {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (i : ℝ) :
    ℕ → ProbabilityMeasure EY → EReal
  | 0, _ => 0
  | n + 1, ρ => ((Real.log (1 + i) : ℝ) : EReal) + (⨆ α ∈ AtildePos M, logObj M ρ α) +
      eint (ρ : Measure EY) fun y => eint (M.QR y) fun z => dLog M i n (M.Phi ρ z)

end BauerleRiederMDP.LQ.Supplement


