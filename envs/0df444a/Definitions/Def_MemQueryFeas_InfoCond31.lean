-- Prove2me | Definitions.Def_MemQueryFeas_InfoCond31
-- name    : MemQueryFeas_InfoCond31
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:40:51.034707+00:00
-- url     : https://prove2.me/theorems/c81b3b23-20f0-469d-aa42-e08090b2d210
-- title:
--   Information constraint (3.1)
-- statement:
--   A layer-$p$ phase $w=(v\,\|\,i_p)$ with parent $v$ satisfies **(3.1)** if
--   $$
--   I\big(E_w;E_v\mid E^{(<i_p)}_{v,p},\mathrm{Mem}_v,C_v,E_{>p}\big)\le\frac{16M}{N_pN_{p-1}}\text{ bits}.
--   $$
--
--   **Formalization Note** Bits as in Definition 4.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 2, Eq. (3.1), p.12 (PDF p.13)

import Mathlib
import Definitions.Def_MemQueryFeas_memV
import Definitions.Def_MemQueryFeas_memCode
import Definitions.Def_MemQueryFeas_ctxV
import Definitions.Def_MemQueryFeas_EgtV
import Definitions.Def_MemQueryFeas_truncSeq
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo

open MeasureTheory

namespace MemQueryFeas

/-- **The information constraint (3.1).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 2, Eq. (3.1), p.12 (PDF p.13): child phases
`w = (v ∥ i_p)` of `v` that "additionally satisfy
`I(E_w; E_v | E^(<i_p)_{v,p}, Mem_v, C_v, E_{>p}) ≤ 16M/(N_pN_{p−1})`. (3.1)"

For `w` of layer `p = |w|` with parent `v = w.dropLast` and last entry `i_p`: the conditional mutual
information of `E_w = ch p v i_p` and `E_v = ch (p−1) v.dropLast i_{p−1}` given
`(E^(<i_p)_{v,p}, Mem_v, C_v, E_{>p})` is at most `16M/(N_p N_{p−1})` bits.

**Formalization Note.** Bits as in `WellBehaved`: `≤ ENNReal.ofReal (X · ln 2)` for the nats-valued
`condMutualInfo`. `E^(<i_p)_{v,p}` is `truncSeq i_p` of the version sequence of `(v, p)`. -/
noncomputable def InfoCond31 {Ω : Type} [MeasurableSpace Ω] {d M : ℕ} (ε : ℝ) (P : ℕ)
    (alg : DetMemAlg d M) (fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d))
    (μ : Measure Ω) [IsFiniteMeasure μ] (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d)
    (w : List ℕ) : Prop :=
  ThompsonTutorial.InfoRatio.condMutualInfo μ
      (fun ω => ch w.length w.dropLast (w.getLastD 0) ω)
      (fun ω => ch (w.length - 1) w.dropLast.dropLast (w.dropLast.getLastD 0) ω)
      (fun ω => (truncSeq (w.getLastD 0) (fun j => ch w.length w.dropLast j ω),
        memCode (memV ε P alg (fun p u i => ch p u i ω) (fin (fun p => Eb p ω)) w.dropLast),
        ctxV (fun p u i => ch p u i ω) w.dropLast, EgtV (fun p => Eb p ω) P w.length))
    ≤ ENNReal.ofReal (16 * M / (Np d ε P w.length * Np d ε P (w.length - 1)) * Real.log 2)

end MemQueryFeas


