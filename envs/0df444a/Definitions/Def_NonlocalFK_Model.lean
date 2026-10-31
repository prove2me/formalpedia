-- Prove2me | Definitions.Def_NonlocalFK_Model
-- name    : NonlocalFK_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:46.641564+00:00
-- url     : https://prove2.me/theorems/51b63be3-6eec-494a-bd0a-13ff8980049e
-- title:
--   The nonlocal problem: jump measures, the operator $\mathcal B$, the law $\tilde\nu$, Assumptions 2.1 and 2.2
-- statement:
--   The **nonlocal problem** adds to the local data a boundary payoff $h$, for each $(t,x)\in\partial_pQ$ a positive Borel measure $\nu_{t,x}$ on $Q$, a set $D$ and a point $x'\in\mathcal O$. Write $\bar\nu(t,x)=\nu_{t,x}(Q)$ and
--
--   $$
--   \mathcal BW(t,x)=\iint_QW(s,z)\,\nu_{t,x}(ds,dz),\qquad
--   \tilde\nu_{v_0,x_0}=\begin{cases}\nu_{v_0,x_0}/\bar\nu(v_0,x_0)&\bar\nu(v_0,x_0)>0,\\ \delta_{(0,x')}&\bar\nu(v_0,x_0)=0.\end{cases}
--   $$
--
--   The **standing assumptions** are those on the local data, $0\le\bar\nu\le1$ and $\nu_{t,x}((t,T)\times\mathcal O)=0$ on $\partial_pQ$, Borel measurability of $h$ and of $(t,x)\mapsto\nu_{t,x}$ for the weak convergence topology, and **Assumption 2.1**: both are continuous on $\partial_pQ\setminus D$ with $D$ small.
--
--   **Assumption 2.2** asks for $t_0\in[0,T)$, $\delta>0$, $0<p_0\le1$ with $\tilde\nu_{v_0,x_0}([0,t_0]\times\mathcal O)\ge p_0$ if $v_0=T$ and $\tilde\nu_{v_0,x_0}([0,v_0]\times\mathcal O_\delta)\ge p_0$ if $v_0<T$, for all $(v_0,x_0)\in\partial_pQ$, where $\mathcal O_\delta=\{x\in\mathcal O:\operatorname{dist}(x,\partial\mathcal O)>\delta\}$.
--
--   The module also defines the bound $|h|\le K_hT$ (`Growth`), the solutions of (1.1)–(1.2) (`IsSolution`), and the iteration of §3 (`IsIteration`): $W_0=0$ and $W_{i+1}$ a bounded solution with data $h+\mathcal BW_i$.
--
--   **Formalization Note** $\nu_{t,x}$ lies in `FiniteMeasure` on the subtype $Q$, whose topology is the weak convergence topology on $Q$ itself, so mass cannot escape to $\partial Q$. $\tilde\nu$ is a measure on $\mathbb R\times\mathbb R^d$ carried by $Q$. The bound $|h|\le K_hT$ is implied by the paper's (2.16), $|h(s,x)|\le K_h s$, and is what its proofs use.
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, eq. (1.3), p.2; §2.1, p.6; Assumption 2.1, p.7; eq. (2.8), p.8; Assumption 2.2, p.9; eq. (2.16), p.10; eq. (3.1)-(3.2), p.11

import Definitions.Def_NonlocalFK_IsSmallSet
import Definitions.Def_NonlocalFK_IsBoundedSolution

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace NonlocalFK

/-- The nonlocal problem (Dai, Kou, Yang, SSRN 3541591, §1.1, p.2, and §§2.1–2.2, pp.6–8): the local
data together with the boundary data `h`, the jump measures `ν_{t,x}` on `Q`, the discontinuity set
`D` and the point `x′` of (2.8).

**Formalization Note.** Each `ν_{t,x}` lives in `FiniteMeasure ↥Q`, whose topology is the paper's
weak convergence topology on `Q` itself. `ν`, `h` are only constrained on `∂ₚQ`. -/
structure Model (d : ℕ) extends Diffusion d where
  h : ℝ × E d → ℝ
  ν : ℝ × E d → FiniteMeasure ↥toDiffusion.Q
  D : Set (ℝ × E d)
  x' : E d

namespace Model

variable {d : ℕ} (m : Model d)

/-- `ν̄(t, x) := ν_{t,x}(Q)` (SSRN 3541591, p.2). -/
def mass (p : ℝ × E d) : ℝ := ((m.ν p).mass : ℝ≥0)

/-- The nonlocal operator `𝓑W(t, x) = ∬_Q W(s, z) ν_{t,x}(ds, dz)`, (1.3), p.2. -/
def B (W : ℝ × E d → ℝ) (p : ℝ × E d) : ℝ :=
  ∫ q : ↥m.Q, W q ∂(m.ν p : Measure ↥m.Q)

/-- The jump law `ν̃_{v₀,x₀}` of (2.8), p.8: `ν_{v₀,x₀}/ν̄(v₀,x₀)` if `ν̄(v₀,x₀) > 0`, and the Dirac
mass at `(0, x′)` if `ν̄(v₀,x₀) = 0`.

**Formalization Note.** The law is a measure on the ambient `ℝ × ℝᵈ`, carried by `Q`. -/
def jumpLaw (p : ℝ × E d) : Measure (ℝ × E d) :=
  if 0 < m.mass p then
    (ENNReal.ofReal (m.mass p))⁻¹ • (m.ν p : Measure ↥m.Q).map Subtype.val
  else Measure.dirac (0, m.x')

/-- The standing assumptions of §2.1–§2.2 (SSRN 3541591, pp.6–8), Assumption 2.1 included: the
assumptions on the local data; `x′ ∈ 𝒪`; for `(t, x) ∈ ∂ₚQ`, `0 ≤ ν̄(t, x) ≤ 1` and
`ν_{t,x}((t, T) × 𝒪) = 0`; `h` and `(t, x) ↦ ν_{t,x}` are Borel on `∂ₚQ`, the latter for the weak
convergence topology; and `h`, `(t, x) ↦ ν_{t,x}` are continuous on `∂ₚQ ∖ D`, with `D` as in
Assumption 2.1.

**Formalization Note.** Positivity of `ν̄` is automatic for a finite measure. -/
structure Standing : Prop where
  diffusion : m.toDiffusion.Assumptions
  x'_mem : m.x' ∈ m.O
  mass_le_one : ∀ p ∈ m.bdry, m.mass p ≤ 1
  no_future : ∀ p ∈ m.bdry, (m.ν p : Measure ↥m.Q) (Subtype.val ⁻¹' (Ioo p.1 m.T ×ˢ m.O)) = 0
  measurable_h : Measurable (fun p : ↥m.bdry => m.h p)
  measurable_ν : @Measurable _ _ _ (borel _) (fun p : ↥m.bdry => m.ν p)
  small : IsSmallSet m.toDiffusion m.D
  continuousOn_h : ContinuousOn m.h (m.bdry \ m.D)
  continuousOn_ν : ContinuousOn m.ν (m.bdry \ m.D)

/-- `𝒪_δ = {x ∈ 𝒪 : dist(x, ∂𝒪) > δ}` (SSRN 3541591, p.9). -/
def Oδ (δ : ℝ) : Set (E d) := {x | x ∈ m.O ∧ δ < Metric.infDist x (frontier m.O)}

/-- Assumption 2.2 (SSRN 3541591, p.9): there are `t₀ ∈ [0, T)`, `δ > 0` and `0 < p₀ ≤ 1` such that
`ν̃_{v₀,x₀}([0, t₀] × 𝒪) ≥ p₀` if `v₀ = T`, (2.10), and `ν̃_{v₀,x₀}([0, v₀] × 𝒪_δ) ≥ p₀` if `v₀ < T`,
(2.11), for all `(v₀, x₀) ∈ ∂ₚQ`. A corner `(T, x₀)` with `x₀ ∈ ∂𝒪` falls under (2.10). -/
def Assumption22 : Prop :=
  ∃ t₀ ∈ Ico 0 m.T, ∃ δ : ℝ, 0 < δ ∧ ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ p ∈ m.bdry,
    (p.1 = m.T → ENNReal.ofReal p₀ ≤ m.jumpLaw p (Icc 0 t₀ ×ˢ m.O)) ∧
    (p.1 < m.T → ENNReal.ofReal p₀ ≤ m.jumpLaw p (Icc 0 p.1 ×ˢ m.Oδ δ))

/-- The bound on `h`: `Kₕ > 0` and `|h(s, x)| ≤ Kₕ · T` on `∂ₚQ`.

**Formalization Note.** The paper's (2.16), p.10, is `|h(s, x)| ≤ Kₕ · s`. It implies this bound
because `s ≤ T`, and the proofs use only this bound (p.23). -/
def Growth (Kh : ℝ) : Prop := 0 < Kh ∧ ∀ p ∈ m.bdry, |m.h p| ≤ Kh * m.T

/-- `W` is a bounded solution in `C^{1,2}(Q) ∩ C(Q̄ ∖ D)` of the nonlocal problem (1.1)–(1.2), p.1. -/
def IsSolution (W : ℝ × E d → ℝ) : Prop :=
  m.toDiffusion.IsBoundedSolution m.D (fun p => m.h p + m.B W p) W

/-- The iteration of §3, (3.1)–(3.2), p.11: `W₀ = 0`, and `W_{i+1}` is a bounded solution of the
problem with boundary data `h + 𝓑Wᵢ`. -/
def IsIteration (W : ℕ → ℝ × E d → ℝ) : Prop :=
  (∀ p ∈ m.Qbar, W 0 p = 0) ∧
  ∀ i, m.toDiffusion.IsBoundedSolution m.D (fun p => m.h p + m.B (W i) p) (W (i + 1))

end Model

end NonlocalFK


