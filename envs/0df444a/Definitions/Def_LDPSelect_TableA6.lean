-- Prove2me | Definitions.Def_LDPSelect_TableA6
-- name    : LDPSelect_TableA6
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:38.437446+00:00
-- url     : https://prove2.me/theorems/d68158d0-6a11-4d86-8cff-a479c4cc9323
-- title:
--   The rows of the table of A.6 and the instance of $B_m$
-- statement:
--   Each row of the table in A.6 lists, for one of $O_1,\dots,O_9$, an arrival order, the two deterministic tail values in order of arrival, the thresholds $(t_0,t_1)$, the continuations $(\beta_0,\beta_1)$ and $\gamma$:
--
--   | family | order | tail values | $(t_0,t_1)$ | $(\beta_0,\beta_1)$ | $\gamma$ |
--   |---|---|---|---|---|---|
--   | $O_1$ | 1,2,3,4 | $\ell,h$ | $(h,\ell)$ | $(0,0)$ | $\delta$ |
--   | $O_2$ | 1,2,3,4 | $\ell,2\mu$ | $(h,\ell)$ | $(\ell,0)$ | $\mu$ |
--   | $O_3$ | 1,2,3,4 | $2\delta,h$ | $(\ell,h)$ | $(2\delta,0)$ | $\delta$ |
--   | $O_4$ | 1,2,3,4 | $2\delta,h$ | $(\ell,h)$ | $(2\delta,0)$ | $\delta$ |
--   | $O_5$ | 1,3,2,4 | $h,\ell$ | $(\ell,h)$ | $(h,0)$ | $\mu$ |
--   | $O_6$ | 1,3,2,4 | $2\delta,h$ | $(h,\ell)$ | $(2\delta,2\delta)$ | $\delta$ |
--   | $O_7$ | 1,2,3,4 | $\ell,h$ | $(\ell,h)$ | $(h,0)$ | $\mu$ |
--   | $O_8$ | 1,2,3,4 | $\ell,2\mu$ | $(\ell,h)$ | $(2\mu,\ell)$ | $\mu$ |
--   | $O_9$ | 1,3,2,4 | $\ell,h$ | $(\ell,h)$ | $(h,\ell)$ | $\delta$ |
--
--   The prior of $B_m$ (§5): two elements of $[m]$ arrive first, uniform on $\{0,2\mu\}$ and $Y$, then the remaining $m-2$ elements of $[m]$ with value $\ell$, and last $x$ with value $(m-2)\ell+h$.
--
--   **Formalization Note** The order $1,3,2,4$ is the transposition of the `Fin 4` values $1,2$, so that the paper's element $3$ arrives second. The tail values sit at positions $2,3$.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), A.6, p.19 (pdf p.20); §5, p.9 (pdf p.10)

import Mathlib
import Definitions.Def_LDPSelect_TwoState

open scoped NNReal

namespace LDPSelect

/-!
# The table of A.6

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), A.6, p.19.

**Formalization Note.** Row `i : Fin 9` is the paper's `O_{i+1}`. The order `1, 3, 2, 4` is the
transposition of `Fin 4` values `1, 2`, so that position `1` holds element `2` (the paper's element `3`).
-/

/-- A row of the table: the tail values in order of arrival, `(t_0, t_1)`, `(β_0, β_1)` and `γ`. -/
structure A6Row where
  tail1 : ℝ
  tail2 : ℝ
  t0 : ℝ
  t1 : ℝ
  β0 : ℝ
  β1 : ℝ
  γ : ℝ

/-- The rows of the table of A.6, p.19, as functions of `a, μ` through `δ, ℓ, h`. -/
noncomputable def a6Row (a μ : ℝ) : Fin 9 → A6Row
  | 0 => ⟨ell a μ, high a μ, high a μ, ell a μ, 0, 0, deltaParam a μ⟩
  | 1 => ⟨ell a μ, 2 * μ, high a μ, ell a μ, ell a μ, 0, μ⟩
  | 2 => ⟨2 * deltaParam a μ, high a μ, ell a μ, high a μ, 2 * deltaParam a μ, 0, deltaParam a μ⟩
  | 3 => ⟨2 * deltaParam a μ, high a μ, ell a μ, high a μ, 2 * deltaParam a μ, 0, deltaParam a μ⟩
  | 4 => ⟨high a μ, ell a μ, ell a μ, high a μ, high a μ, 0, μ⟩
  | 5 => ⟨2 * deltaParam a μ, high a μ, high a μ, ell a μ, 2 * deltaParam a μ,
      2 * deltaParam a μ, deltaParam a μ⟩
  | 6 => ⟨ell a μ, high a μ, ell a μ, high a μ, high a μ, 0, μ⟩
  | 7 => ⟨ell a μ, 2 * μ, ell a μ, high a μ, 2 * μ, ell a μ, μ⟩
  | 8 => ⟨ell a μ, high a μ, ell a μ, high a μ, high a μ, ell a μ, deltaParam a μ⟩

/-- The arrival order of each row: the identity, or `1, 3, 2, 4` on rows `O5, O6, O9`. -/
def a6Order : Fin 9 → Equiv.Perm (Fin 4)
  | 4 => Equiv.swap 1 2
  | 5 => Equiv.swap 1 2
  | 8 => Equiv.swap 1 2
  | _ => Equiv.refl _

/-- The deterministic values of a row: positions `2, 3` carry the two tail values. -/
noncomputable def a6Tail (r : A6Row) : Fin (2 + 2) → ℝ≥0 := fun i =>
  if i.val = 2 then r.tail1.toNNReal else if i.val = 3 then r.tail2.toNNReal else 0

/-- The prior of `B_m` in §5, p.9: two elements of `[m]` first, uniform on `{0, 2μ}` and `Y`, then the
other `m − 2` elements of `[m]` with value `ℓ`, and last `x` with value `(m − 2) ℓ + h`. -/
noncomputable def bPrior (a μ : ℝ) (m : ℕ) : Fin (m + 1) → MeasureTheory.Measure ℝ≥0 := fun i =>
  if i.val = 0 then uniform2 μ
  else if i.val = 1 then Y μ
  else if i.val = m then MeasureTheory.Measure.dirac (((m : ℝ) - 2) * ell a μ + high a μ).toNNReal
  else MeasureTheory.Measure.dirac (ell a μ).toNNReal

end LDPSelect


