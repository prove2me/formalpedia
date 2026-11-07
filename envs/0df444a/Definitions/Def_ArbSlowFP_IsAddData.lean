-- Prove2me | Definitions.Def_ArbSlowFP_IsAddData
-- name    : ArbSlowFP_IsAddData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:51:11.705112+00:00
-- url     : https://prove2.me/theorems/53f70d75-d8bd-4b8d-9f76-ea002eac02d0
-- title:
--   Definition 6.2 — additional data for the next step
-- statement:
--   Let $(A,R,C,b,v)$ be parent tables of order $k$, with baseline $H$. A rational row $t$ is the **target row** when
--   $$tF_\tau=\zeta^\circ+\zeta^\circ B-(2H-c_{\mathrm{ref}})e_{0,w}^\top ,$$
--   where $\zeta^\circ$ is the height row at gain $c_{\mathrm{ref}}$. The **additional data** are an integer $\tau\ge1$, a rational $c_{\mathrm{ref}}\in(0,1)$, an integer row $\ell_*$ of width $k+1$ and a strictly positive vector $a_P$ with
--
--   1. $\langle Z^{(h)},(D^\circ)^\top X-\ell_*^\top\psi^\circ\rangle=0$ for every even $k<h\le2k$;
--   2. $a_P^\top C$ is the target row.
--
--   These data make the lift repeatable: the correction satisfies the higher compatibility tests, and the weights represent the target height polynomial.
--
--   **Formalization Note** The predicate is on bare tables with $H$ an argument; a clock passes $H=A_k+3$. Right multiplication by $F_\tau$ is injective on rows for $\tau\ge1$, so the target row is unique.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.38, Definition 6.2, eq. (30)

import Mathlib
import Definitions.Def_ArbSlowFP_IsClock
import Definitions.Def_ArbSlowFP_tblD

open Matrix

namespace ArbSlowFP

variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `t` is the target row `t_{τ,cref}(χ)` of (30), p.38:
`t F_τ = ζ° + ζ°B - (2H - cref)e⊤_{0,w}`. Right multiplication by `F_τ` is injective on width-`k`
rows, by (26), so at most one row satisfies this for `τ ≥ 1`. -/
def IsTargetRow (P : Parent k ι) (H : ℚ) (τ : ℕ) (cref : ℚ) (t : Fin k → ℚ) : Prop :=
  t ᵥ* transF k τ =
    P.zeta H τ cref + P.zeta H τ cref ᵥ* shiftB (k + 1) - (2 * H - cref) • e0Row (k + 1)

/-- Definition 6.2 (additional data for the next step), p.38: an integer `τ ≥ 1`, a rational
`cref ∈ (0, 1)`, an integer row `ℓ∗` and a strictly positive `a_P` with (i) the compatibility tests
(31) with indices above `k`, and (ii) `a_P⊤ C = t_{τ,cref}(χ)`.

**Formalization Note.** Stated on bare tables, with `H` an argument; a clock passes `H = A_k + 3`. -/
structure IsAddData (P : Parent k ι) (H : ℚ) (τ : ℕ) (cref : ℚ) (ℓ : Fin (k + 1) → ℚ)
    (aP : ι → ℚ) : Prop where
  τ_pos : 1 ≤ τ
  cref_pos : 0 < cref
  cref_lt : cref < 1
  ℓ_int : ∀ j, ∃ z : ℤ, ℓ j = z
  aP_pos : ∀ i, 0 < aP i
  /-- (31). -/
  tests : ∀ h, Even h → k < h → h ≤ 2 * k → frob (testZ k h) (P.testResidual H τ cref ℓ) = 0
  /-- Definition 6.2 (ii). -/
  weights : IsTargetRow P H τ cref (aP ᵥ* P.C)

/-- The bare tables `(A, R, C, b, v)` of a clock's data. -/
def ClockData.parent (d : ClockData k ι) : Parent k ι := ⟨d.A, d.R, d.C, d.b, d.v⟩

end ArbSlowFP


