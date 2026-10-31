-- Prove2me | Definitions.Def_PCLAssort_FLLowerBound
-- name    : PCLAssort_FLLowerBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:20.739991+00:00
-- url     : https://prove2.me/theorems/7aa00421-ec01-4751-aa71-a8b3997a734c
-- title:
--   F/L lower bound (Definition 2)
-- statement:
--   For functions $F,L$ on $[0,1]^n$, a constant $\alpha$ and a point $x\in[0,1]^n$, the F/L lower bound property holds at $x$ if
--
--   $$
--   F(x)\ge \alpha\,L(x).
--   $$
--
--   Combined with pipage rounding, which does not decrease $F$, it turns a relaxation solution into an integral solution within a factor $\alpha$ of the relaxation value.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Definition 2, p.794 (PDF p.10)

import Mathlib

namespace PCLAssort

/-- Definition 2 (F/L lower bound) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.794): for a given `x ∈ [0,1]^n`, `F(x) ≥ α L(x)`. -/
def FLLowerBound {V : Type} (F L : (V → ℝ) → ℝ) (α : ℝ) (x : V → ℝ) : Prop :=
  α * L x ≤ F x

end PCLAssort


