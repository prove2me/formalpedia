-- Prove2me | Definitions.Def_StrategicNRM_Fluid
-- name    : StrategicNRM_Fluid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:34.412911+00:00
-- url     : https://prove2.me/theorems/221e7ff5-1a5d-4a6c-bf4d-54ddb252e095
-- title:
--   The fluid problem (18), its value $\bar J^\chi$, and Assumption 1
-- statement:
--   Let $\bar F_j(v)=\int_v^\infty f_j$, with $\bar F_j(\infty)=0$. For $\chi\in[0,1]$, $\bar J^\chi$ is the optimal value of the deterministic problem
--
--   $$
--   \max_{q\in[0,\infty]^n}\ \lambda T\sum_{j=1}^n q^j\bar F_j(q^j)
--   \quad\text{s.t.}\quad \sum_{j=1}^n\bar F_j(q^j)\le\chi,\qquad \lambda T\sum_{j=1}^n A_{ij}\bar F_j(q^j)\le x_0^i\ \ \forall i,
--   $$
--
--   with $\infty\cdot 0=0$. If $q^j$ is read as a static price, $\bar F_j(q^j)$ is the probability that a customer buys product $j$.
--
--   **Assumption 1**: the virtual value $v-\bar F_j(v)/f_j(v)$ is non-decreasing. It is required on the interior of the support: $f_j>0$ almost everywhere on $\{v>0:\ 0<\bar F_j(v)<1\}$, and the virtual value is non-decreasing on the points of that set where $f_j>0$.
--
--   $\bar J^1$ is the bound of the goal theorem, and Assumption 1 is the assumption under which it holds.
--
--   **Formalization Note** Prices range over $[0,\infty]$ rather than $\mathbb R$. A negative price is dominated by $0$, and $\infty$ encodes $\bar F_j=0$. Whenever the real problem is feasible the two suprema agree; but if $x_0^i=0$ and a product using $i$ has unbounded support, the real problem is infeasible and a real supremum would be a junk value. The domain of Assumption 1 is a reading: p.18 says "for all $v\ge 0$", but the same paragraph names the uniform distribution, whose density vanishes on part of $[0,\infty)$; a Lean division by $0$ returns $0$, so those points are excluded. A support with a gap is excluded, as printed.
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.2, p.18, problem (18) and Assumption 1

import Mathlib
import Definitions.Def_StrategicNRM_Instance

open MeasureTheory
open scoped ENNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- The c.c.d.f. `F̄ⱼ(v) = ∫_{[v,∞)} fⱼ` of the valuation for product `j` (p.7). -/
noncomputable def Instance.FbarR (I : Instance n m) (j : Fin n) (v : ℝ) : ℝ :=
  ∫ w in Set.Ici v, I.f j w

/-- `F̄ⱼ` on `[0,∞]`, with `F̄ⱼ(∞) = 0`. -/
noncomputable def Instance.Fbar (I : Instance n m) (j : Fin n) (q : ℝ≥0∞) : ℝ :=
  if q = ⊤ then 0 else I.FbarR j q.toReal

/-- The constraints of problem (18), p.18:
`Σⱼ F̄ⱼ(qʲ) ≤ χ` and `λT Σⱼ A_{ij} F̄ⱼ(qʲ) ≤ xⁱ₀` for every `i`. -/
def Instance.FluidFeasible (I : Instance n m) (χ : ℝ) (q : Fin n → ℝ≥0∞) : Prop :=
  ∑ j, I.Fbar j (q j) ≤ χ ∧
    ∀ r, I.lam * I.T * ∑ j, (I.A r j : ℝ) * I.Fbar j (q j) ≤ I.x0 r

/-- The objective `λT Σⱼ qʲ F̄ⱼ(qʲ)` of problem (18), with `∞ · 0 = 0`. -/
noncomputable def Instance.fluidValue (I : Instance n m) (q : Fin n → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (I.lam * I.T) * ∑ j, q j * ENNReal.ofReal (I.Fbar j (q j))

/-- `J̄^χ`, the optimal value of problem (18), p.18.

**Formalization Note.** The prices range over `[0,∞]`, not over `ℝ`. A negative price is dominated
by `0`, and `∞` encodes `F̄ⱼ = 0`. Whenever the real problem is feasible the two suprema agree; but
with `x₀ⁱ = 0` and a product using `i` with unbounded support the real problem is infeasible, and a
real supremum over the empty set would be a junk value, while this one is the right value. -/
noncomputable def Instance.Jbar (I : Instance n m) (χ : ℝ) : EReal :=
  ⨆ q : {q : Fin n → ℝ≥0∞ // I.FluidFeasible χ q}, ((I.fluidValue q.1 : ℝ≥0∞) : EReal)

/-- The support of `fⱼ`, without its endpoints: `0 < v` and `0 < F̄ⱼ(v) < 1`. -/
def Instance.supportInterior (I : Instance n m) (j : Fin n) : Set ℝ :=
  {v | 0 < v ∧ 0 < I.FbarR j v ∧ I.FbarR j v < 1}

/-- Assumption 1, p.18: the virtual value `v − F̄ⱼ(v)/fⱼ(v)` is non-decreasing.

**Formalization Note (reading).** p.18 says "for all `v ≥ 0`", but the same paragraph names the
uniform distribution, whose density vanishes on part of `[0,∞)`, where the ratio is undefined. So
the assumption is read on the interior of the support: `fⱼ > 0` almost everywhere there, and the
virtual value is non-decreasing on the points of it where `fⱼ > 0`. In Lean `F̄/0 = 0`, so these
points must be excluded from the monotonicity. A support with a gap is excluded, as printed. -/
def Instance.Assumption1 (I : Instance n m) : Prop :=
  ∀ j, (∀ᵐ v, v ∈ I.supportInterior j → 0 < I.f j v) ∧
    MonotoneOn (fun v => v - I.FbarR j v / I.f j v) (I.supportInterior j ∩ {v | 0 < I.f j v})

end StrategicNRM


