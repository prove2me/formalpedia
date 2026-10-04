-- Prove2me | Definitions.Def_BRWMinimum_Law_PointProcess
-- name    : BRWMinimum_Law_PointProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T23:09:57.81512+00:00
-- url     : https://prove2.me/theorems/3fbdb154-0476-463b-97fe-8af519938f09
-- title:
--   Offspring point process ℒ and the standing assumptions (1.1), (1.3), (1.4), non-lattice
-- statement:
--   This file fixes the offspring point process $\mathcal L$ of the branching random walk and the assumptions that Aïdékon's paper imposes on it throughout.
--
--   A **point configuration** on $\mathbb R$ is a pair $c=(N,p)$ with $N\in\{0,1,2,\dots\}\cup\{\infty\}$ the number of points and $p=(p_0,p_1,\dots)$ their positions; only the indices $i<N$ are points. The law of $\mathcal L$ is a probability measure $L$ on such configurations. For $f\ge0$ write $\sum_{v\in c} f(v)=\sum_{i<N} f(p_i)\in[0,\infty]$. Writing $V(x)$, $|x|=1$, for the points of $\mathcal L$, the paper's assumptions are:
--
--   1. **Boundary case (1.1).**
--   $$\mathbf E\Big[\sum_{|x|=1}1\Big]>1,\qquad \mathbf E\Big[\sum_{|x|=1}e^{-V(x)}\Big]=1,\qquad \mathbf E\Big[\sum_{|x|=1}V(x)e^{-V(x)}\Big]=0.$$
--   2. **Non-lattice.** There are no $a\in\mathbb R$, $d>0$ such that almost surely every point of $\mathcal L$ lies in $a+d\mathbb Z$.
--   3. **Second moment (1.3).** $\mathbf E\big[\sum_{|x|=1}V(x)^2e^{-V(x)}\big]<\infty$.
--   4. **Log moments (1.4).** With $X=\sum_{|x|=1}e^{-V(x)}$ and $\tilde X=\sum_{|x|=1}V(x)_+e^{-V(x)}$ (1.2), $\mathbf E[X(\ln_+X)^2]<\infty$ and $\mathbf E[\tilde X\ln_+\tilde X]<\infty$, where $\ln_+ t=\max(\ln t,0)$.
--
--   The boundary case is the normalisation in which the minimum of the walk grows like $\frac32\ln n$; every branching random walk satisfying mild assumptions can be brought to it by an affine change of the positions.
--
--   **Formalization Note** A configuration is an element of $\mathbb N_\infty\times(\mathbb N\to\mathbb R)$. All expectations are lower Lebesgue integrals of $[0,\infty]$-valued sums, so none of them is a junk value. The signed condition $\mathbf E[\sum V e^{-V}]=0$ is written as: the expectations of $\sum V_+e^{-V}$ and of $\sum V_-e^{-V}$ are equal and finite. $t(\ln_+t)^p$ is taken to be $\infty$ at $t=\infty$. Non-lattice keeps the shift $a$: a law supported on $\tfrac12+\mathbb Z$ is lattice.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 1, §1, eq. (1.1); p. 2, eqs. (1.2)–(1.4) and the standing assumptions

import Mathlib

namespace BRWMinimum.Law

open MeasureTheory

/-- A point configuration on `ℝ`: `c.1 ∈ ℕ∞` is the number of points (possibly infinite) and
`c.2 i` is the position of the `i`-th point; only the indices `i` with `(i : ℕ∞) < c.1` are points.
The law `L` of the offspring point process `ℒ` is a probability measure on this space. -/
abbrev PointConfig : Type := ℕ∞ × (ℕ → ℝ)

/-- `pointSum c f = Σ_{points v of c} f v`, an `ℝ≥0∞`-valued sum (never junk). -/
noncomputable def pointSum (c : PointConfig) (f : ℝ → ENNReal) : ENNReal :=
  ∑' i : ℕ, if (i : ℕ∞) < c.1 then f (c.2 i) else 0

/-- The boundary case (1.1):
`E[Σ_{|x|=1} 1] > 1`, `E[Σ_{|x|=1} e^{-V(x)}] = 1`, `E[Σ_{|x|=1} V(x) e^{-V(x)}] = 0`.
The signed condition is written as: the expectations of `Σ V₊ e^{-V}` and `Σ V₋ e^{-V}` are
finite and equal. -/
def BoundaryCase (L : Measure PointConfig) : Prop :=
  1 < ∫⁻ c, pointSum c (fun _ => 1) ∂L ∧
  ∫⁻ c, pointSum c (fun v => ENNReal.ofReal (Real.exp (-v))) ∂L = 1 ∧
  ∫⁻ c, pointSum c (fun v => ENNReal.ofReal (max v 0 * Real.exp (-v))) ∂L ≠ ⊤ ∧
  ∫⁻ c, pointSum c (fun v => ENNReal.ofReal (max v 0 * Real.exp (-v))) ∂L =
    ∫⁻ c, pointSum c (fun v => ENNReal.ofReal (max (-v) 0 * Real.exp (-v))) ∂L

/-- `ℒ` is non-lattice: there are no `a ∈ ℝ`, `d > 0` such that `L`-almost surely every point
of the configuration lies in `a + dℤ`. -/
def NonLattice (L : Measure PointConfig) : Prop :=
  ¬ ∃ a d : ℝ, 0 < d ∧
    ∀ᵐ c ∂L, ∀ i : ℕ, (i : ℕ∞) < c.1 → ∃ k : ℤ, c.2 i = a + (k : ℝ) * d

/-- Condition (1.3): `E[Σ_{|x|=1} V(x)² e^{-V(x)}] < ∞`. -/
def SecondMoment (L : Measure PointConfig) : Prop :=
  ∫⁻ c, pointSum c (fun v => ENNReal.ofReal (v ^ 2 * Real.exp (-v))) ∂L < ⊤

/-- `X = Σ_{|x|=1} e^{-V(x)}` of (1.2), in `ℝ≥0∞`. -/
noncomputable def Xvar (c : PointConfig) : ENNReal :=
  pointSum c (fun v => ENNReal.ofReal (Real.exp (-v)))

/-- `X̃ = Σ_{|x|=1} V(x)₊ e^{-V(x)}` of (1.2), in `ℝ≥0∞`. -/
noncomputable def Xtilde (c : PointConfig) : ENNReal :=
  pointSum c (fun v => ENNReal.ofReal (max v 0 * Real.exp (-v)))

/-- `t ↦ t (ln₊ t)^p` on `[0, ∞]`, with value `∞` at `t = ∞`. -/
noncomputable def mulPosLogPow (p : ℕ) (t : ENNReal) : ENNReal :=
  if t = ⊤ then ⊤ else ENNReal.ofReal (t.toReal * (Real.posLog t.toReal) ^ p)

/-- Condition (1.4): `E[X (ln₊ X)²] < ∞` and `E[X̃ ln₊ X̃] < ∞`. -/
def LogMoments (L : Measure PointConfig) : Prop :=
  ∫⁻ c, mulPosLogPow 2 (Xvar c) ∂L < ⊤ ∧ ∫⁻ c, mulPosLogPow 1 (Xtilde c) ∂L < ⊤

end BRWMinimum.Law


