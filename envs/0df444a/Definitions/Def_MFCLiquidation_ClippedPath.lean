-- Prove2me | Definitions.Def_MFCLiquidation_ClippedPath
-- name    : MFCLiquidation_ClippedPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:23:42.692779+00:00
-- url     : https://prove2.me/theorems/a0bd95ba-1380-41a2-9752-4d33defd57ba
-- title:
--   A path clipped to $[t,T)$, and the continuous part $[X,Y]^c$ of a bracket
-- statement:
--   Two auxiliary notions for Itô's formula on $[t,T)$.
--
--   1. For a path $S$ and times $t<T$, the **clipped path** equals $S_t$ up to time $t$, $S_s$ for $t\le s<T$, and the left limit $S_{T-}$ from $T$ on. Its stochastic integrals and brackets over $[0,T]$ are those of $S$ over the open interval $(t,T)$.
--   2. For processes $X,Y$ with bracket $Q=[X,Y]$, a process $Q^c$ is the **continuous part** $[X,Y]^c$ if, almost surely, for every $s$ the jump products are absolutely summable and
--   $$Q^c_s=Q_s-\sum_{0<u\le s}\Delta X_u\,\Delta Y_u .$$
--
--   **Formalization Note** `Summable` over an uncountable index set is absolute summability; it excludes the default value $0$ of an unsummable `tsum`.
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, first display on p.17 (Itô's formula over (t, T−) with Tr(A_s d[𝒳, 𝒳]^c_s))

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open MeasureTheory
open scoped NNReal
open KurtzProtter91.Integrals

namespace MFCLiquidation

/-- The path of `S` between `t` and `T−`: equal to `S_t` up to `t`, to `S_s` for `t ≤ s < T`, and
to the left limit `S_{T−}` from `T` on. Integrals and brackets of this process over `[0, T]` are
those of `S` over `(t, T)`, the range of the display on p.17 of arXiv:2207.00446v3 after its atom
at `t` is removed. -/
noncomputable def clipped {Ω : Type*} {n : ℕ} (t T : ℝ≥0) (S : ℝ≥0 → Ω → Fin n → ℝ) :
    ℝ≥0 → Ω → Fin n → ℝ :=
  fun s ω => if s < T then S (max s t) ω else leftLim (fun u => S u ω) T

/-- `Qc` is the continuous part `[X, Y]^c` of the bracket `Q = [X, Y]`: the bracket minus the sum
of the products of the jumps, `[X, Y]^c_s = [X, Y]_s − ∑_{0<u≤s} ΔX_u ΔY_u`. The sum converges
absolutely for semimartingales; the `Summable` clause excludes the default value of `tsum`. -/
def IsContinuousBracket {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y Q Qc : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
    Summable (fun u : Set.Ioc (0 : ℝ≥0) s => jump (fun v => X v ω) u * jump (fun v => Y v ω) u) ∧
    Qc s ω = Q s ω
      - ∑' u : Set.Ioc (0 : ℝ≥0) s, jump (fun v => X v ω) u * jump (fun v => Y v ω) u

end MFCLiquidation


