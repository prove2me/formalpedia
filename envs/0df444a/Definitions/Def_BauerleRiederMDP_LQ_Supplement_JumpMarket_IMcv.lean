-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_IMcv
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_IMcv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:13:09.890822+00:00
-- url     : https://prove2.me/theorems/a5f0b10c-9678-5ca5-8661-02ca4018d2c2
-- title:
--   The set $IM_cv$
-- statement:
--   **The set $IM_cv$** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, p.285, PDF 295): `IM_cv := {v ∈ IB_b | v is continuous, v(t, x) is concave and increasing in x and decreasing in t, v ≥ U}`.
--
--   **Formalization Note.** Functions on $E = [0, T] \times  \mathbb R _+$ are functions on $\mathbb R  \times  \mathbb R $ constrained on $E$: measurable on $E$, $\|v\|_b < \infty $ ($IB_b$), continuous on $E$, concave and increasing in $x \in  [0, \infty )$ for each $t \in  [0, T]$, decreasing in $t \in  [0, T]$ for each $x \ge  0$, and $v(t, x) \ge  U(x)$ on $E$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, p.285, PDF 295

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Eset
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_bfun
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_normb

namespace BauerleRiederMDP.LQ.Supplement

/-- **The set `IM_cv`** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), §9.3, p.285, PDF 295): `IM_cv := {v ∈ IB_b | v is continuous, v(t, x) is concave and
increasing in x and decreasing in t, v ≥ U}`.

**Formalization Note.** Functions on `E = [0, T] × ℝ_+` are functions on `ℝ × ℝ` constrained on `E`:
measurable on `E`, `‖v‖_b < ∞` (`IB_b`), continuous on `E`, concave and increasing in `x ∈ [0, ∞)`
for each `t ∈ [0, T]`, decreasing in `t ∈ [0, T]` for each `x ≥ 0`, and `v(t, x) ≥ U(x)` on `E`. -/
def JumpMarket.IMcv {d : ℕ} (Mk : JumpMarket d) (γ : ℝ) (U : ℝ → ℝ) : Set (ℝ × ℝ → ℝ) :=
  {v | Measurable (Mk.Eset.domRestrict v) ∧ Mk.normb γ v < ⊤ ∧ ContinuousOn v Mk.Eset ∧
    (∀ t ∈ Set.Icc 0 Mk.T, ConcaveOn ℝ (Set.Ici 0) (fun x => v (t, x)) ∧
      MonotoneOn (fun x => v (t, x)) (Set.Ici 0)) ∧
    (∀ x, 0 ≤ x → AntitoneOn (fun t => v (t, x)) (Set.Icc 0 Mk.T)) ∧
    ∀ p ∈ Mk.Eset, U p.2 ≤ v p}

end BauerleRiederMDP.LQ.Supplement


