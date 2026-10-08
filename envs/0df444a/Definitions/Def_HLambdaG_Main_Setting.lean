-- Prove2me | Definitions.Def_HLambdaG_Main_Setting
-- name    : HLambdaG_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:23:32.350986+00:00
-- url     : https://prove2.me/theorems/5724d43a-673a-4097-b7d3-efc47eb63743
-- title:
--   §1–§2: marginal averages, inverse, left limit, and conditions (14)–(15)
-- statement:
--   For a cumulative input $F$, the **marginal averages** from (1) are
--   $$
--   G(s)=\frac{F(s,\infty)}{s},\qquad H(t)=\frac{F(\infty,t)}{t}.
--   $$
--   For a time change $T$, the **right-continuous inverse** and left limit are
--   $$
--   S(t)=\inf\{s\geq0:T(s)>t\},\qquad T(s-)=\sup_{0\leq u<s}T(u).
--   $$
--   The approximation conditions for a cumulative input $F$ and time change $T$ are
--   $$
--   \lim_{s\to\infty}\frac{F(s,T(s-))-F(\infty,T(s-))}{s}=0\quad(14),
--   \qquad
--   \lim_{s\to\infty}\frac{F(s,\infty)-F(s,T(s))}{s}=0\quad(15).
--   $$
--
--   These derived objects are used throughout the mission to compare customer and time averages.
--
--   **Formalization Note** At $s=0$, the left-limit supremum is empty and is set to zero. The averages at zero take Lean's total division-by-zero value $0$; all asserted limits are at infinity. The time change tends to infinity, making the inverse set nonempty. Extended-real lim inf and lim sup are used so unbounded averages retain their infinite values.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 635, §1 displays (1), (3); p. 638, §2 displays (14)–(15), https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_CumulativeInput
import Definitions.Def_HLambdaG_Main_TimeChange

open scoped NNReal

namespace HLambdaG.Main

open Filter Topology

/-- The finite limit F(s, ∞). -/
noncomputable def FsInf (C : CumulativeInput) (s : ℝ≥0) : ℝ := ⨆ t, C.F s t

/-- The finite limit F(∞, t). -/
noncomputable def FInfT (C : CumulativeInput) (t : ℝ≥0) : ℝ := ⨆ s, C.F s t

/-- The customer-indexed marginal average in (1). -/
noncomputable def G (C : CumulativeInput) (s : ℝ≥0) : ℝ := ((s : ℝ))⁻¹ * FsInf C s

/-- The time-indexed marginal average in (1). -/
noncomputable def H (C : CumulativeInput) (t : ℝ≥0) : ℝ := ((t : ℝ))⁻¹ * FInfT C t

/-- The right-continuous inverse in (3). -/
noncomputable def inv (τ : TimeChange) (t : ℝ≥0) : ℝ≥0 := sInf {s | t < τ.T s}

/-- The left limit T(s−). At zero the empty supremum gives T(0−) = 0. -/
noncomputable def leftLim (τ : TimeChange) (s : ℝ≥0) : ℝ≥0 := sSup (τ.T '' Set.Iio s)

/-- Approximation condition (14). -/
def Cond14 (C : CumulativeInput) (τ : TimeChange) : Prop :=
  Tendsto (fun s : ℝ≥0 => ((s : ℝ))⁻¹ *
    (C.F s (leftLim τ s) - FInfT C (leftLim τ s))) atTop (𝓝 0)

/-- Approximation condition (15). -/
def Cond15 (C : CumulativeInput) (τ : TimeChange) : Prop :=
  Tendsto (fun s : ℝ≥0 => ((s : ℝ))⁻¹ *
    (FsInf C s - C.F s (τ.T s))) atTop (𝓝 0)

/-- Extended-real limit inferior of a real-valued function along the positive half-line. -/
noncomputable def liminfE (f : ℝ≥0 → ℝ) : EReal := Filter.liminf (fun x => (f x : EReal)) atTop

/-- Extended-real limit superior of a real-valued function along the positive half-line. -/
noncomputable def limsupE (f : ℝ≥0 → ℝ) : EReal := Filter.limsup (fun x => (f x : EReal)) atTop

end HLambdaG.Main


