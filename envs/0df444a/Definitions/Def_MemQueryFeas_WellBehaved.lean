-- Prove2me | Definitions.Def_MemQueryFeas_WellBehaved
-- name    : MemQueryFeas_WellBehaved
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:40:01.876204+00:00
-- url     : https://prove2.me/theorems/727c1212-456c-40b3-90c7-3cb3938f7f9a
-- title:
--   Well-behaved phase (Definition 4)
-- statement:
--   A layer-$p$ phase $w=(v\,\|\,i_p)$ with parent $v$ is **well-behaved** if
--   $$
--   I(E_w;\mathrm{Mem}_v\mid E_{>p},C_w)\le 4M/N_p \text{ bits},
--   $$
--   where $E_w=E^{(i_p)}_{v,p}$.
--
--   **Formalization Note** Conditional mutual information is the platform's `condMutualInfo` (in nats, valued in $[0,\infty]$); a bound of $X$ bits is $X\ln 2$ nats.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Definition 4, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_MemQueryFeas_memV
import Definitions.Def_MemQueryFeas_memCode
import Definitions.Def_MemQueryFeas_ctxV
import Definitions.Def_MemQueryFeas_EgtV
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo

open MeasureTheory

namespace MemQueryFeas

/-- **Well-behaved phase (Definition 4).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Definition 4, p.10 (PDF p.11): "Fix `p ∈ [P]` and a
layer-`p` phase `w = (v ∥ i_p) ∈ V_p`, where `v` denotes its parent. We recall that by construction,
`E_w := E^(i_p)_{v,p}`. We say that `w` is well-behaved if `I(E_w; Mem_v | E_{>p}, C_w) ≤ 4M/N_p`."

For `w` of layer `p = |w|`, parent `v = w.dropLast` and last entry `i_p`: the conditional mutual
information of `E_w = ch p v i_p` and `Mem_v` given `(E_{>p}, C_w)` is at most `4M/N_p` bits.

**Formalization Note.** Information is the platform's `condMutualInfo` (KL form, in nats, valued in
`ℝ≥0∞`); "`≤ X` bits" is `≤ ENNReal.ofReal (X · ln 2)` (log is base 2, p.7), never a `toReal`.
`Mem_v` enters through `memCode`. -/
noncomputable def WellBehaved {Ω : Type} [MeasurableSpace Ω] {d M : ℕ} (ε : ℝ) (P : ℕ)
    (alg : DetMemAlg d M) (fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d))
    (μ : Measure Ω) [IsFiniteMeasure μ] (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d)
    (w : List ℕ) : Prop :=
  ThompsonTutorial.InfoRatio.condMutualInfo μ
      (fun ω => ch w.length w.dropLast (w.getLastD 0) ω)
      (fun ω => memCode (memV ε P alg (fun p u i => ch p u i ω) (fin (fun p => Eb p ω))
        w.dropLast))
      (fun ω => (EgtV (fun p => Eb p ω) P w.length, ctxV (fun p u i => ch p u i ω) w))
    ≤ ENNReal.ofReal (4 * M / Np d ε P w.length * Real.log 2)

end MemQueryFeas


