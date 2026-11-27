-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Treal
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_Treal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:16:12.996355+00:00
-- url     : https://prove2.me/theorems/9f1fa0b2-c3d8-5c11-9440-609a61e10fa8
-- title:
--   The operator $T$ of (9.15) on real functions
-- statement:
--   **The operator $T$ of (9.15) on real functions** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (9.15), p.285, PDF 295): $(T v)(t, x) = \sup _{\alpha  \in  A} {e^{-\lambda (T-t)} U(\varphi ^\alpha _{T-t}(x)) + \lambda  \int _0^{T-t} e^{-\lambda s} \int  v(t + s, \varphi ^\alpha _s(x)(1 + \alpha _s \cdot  y)) Q^Y(dy) ds}$.
--
--   **Formalization Note.** The published `StageModel.T` of `JumpMarket.stage` (an `EReal` supremum), applied to $v$ cast to `EReal` and read back with `toReal`; on $IB_b$ (Proposition 9.3.2, $T : IB_b \to  IB_b$) the value is finite, so the conversion is exact there.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (9.15), p.285, PDF 295

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_stage

namespace BauerleRiederMDP.LQ.Supplement

/-- **The operator `T` of (9.15) on real functions** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), eq. (9.15), p.285, PDF 295):
`(T v)(t, x) = sup_{α ∈ A} {e^{−λ(T−t)} U(φ^α_{T−t}(x)) + λ ∫_0^{T−t} e^{−λs} ∫ v(t + s, φ^α_s(x)(1 + α_s · y)) Q^Y(dy) ds}`.

**Formalization Note.** The published `StageModel.T` of `JumpMarket.stage` (an `EReal` supremum),
applied to `v` cast to `EReal` and read back with `toReal`; on `IB_b` (Proposition 9.3.2,
`T : IB_b → IB_b`) the value is finite, so the conversion is exact there. -/
noncomputable def JumpMarket.Treal {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ) (v : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  ((Mk.stage U).T (fun q => (v q : EReal)) p).toReal

end BauerleRiederMDP.LQ.Supplement


