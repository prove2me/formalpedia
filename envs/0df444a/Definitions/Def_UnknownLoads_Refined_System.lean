-- Prove2me | Definitions.Def_UnknownLoads_Refined_System
-- name    : UnknownLoads_Refined_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:07.799443+00:00
-- url     : https://prove2.me/theorems/589f6f46-c46e-403c-a8a2-ac50b301ee4c
-- title:
--   The coupled sequence of systems (q_n, ℓ_n), its total and tail masses (7), the process δ_n of (16), and the set Ω_T of nice sample paths (Proposition 7)
-- statement:
--   This module packages the coupled sequence of systems and the derived processes used in §5.
--
--   1. **System.** Primitives as in §5.1.1, control parameters $\alpha_n\in(0,1)$, and processes $q_n(\omega,t,i)$, $\ell_n(\omega,t)$ such that, almost surely, for every $n\ge1$ the pair $(q_n(\omega),\ell_n(\omega))$ solves (9a)–(9b) on $[0,T]$. We write $\mathcal A_n:=\mathcal A_n(q_n,\ell_n)$ and $\mathcal D_n:=\mathcal D_n(q_n)$.
--   2. **Masses** (7). $u_n:=\sum_{i\ge1}q_n(i)$ and $v_n(j):=\sum_{i\ge j}q_n(i)$, $j\ge1$.
--   3. **The process** (16). For $j\ge1$,
--   $$
--   \delta_n(t,j):=\frac1n\mathcal N^\lambda_n(t)-\int_0^t\lambda(s)\,ds-\sum_{i=1}^{j}\Big[\mathcal D_n(t,i)-\int_0^t\mu i\,[q_n(s,i)-q_n(s,i+1)]\,ds\Big].
--   $$
--   4. **Relative compactness with Lipschitz limits.** A sequence $x_n:[0,T]\to\mathbb R^{\mathbb N}$ has this property if every subsequence has a further subsequence converging uniformly on $[0,T]$ in every coordinate, and every coordinatewise uniform limit along a subsequence has Lipschitz coordinates on $[0,T]$.
--   5. **Nice sample paths.** For a constant $B_T\in\mathbb N$, an outcome $\omega$ is nice ($\omega\in\Omega_T$) if: the initial-condition assumptions hold at $\omega$; for every $n\ge1$, $(q_n(\omega),\ell_n(\omega))$ solves (9a)–(9b) and, on $(0,T]$, $\mathcal N^\lambda_n$ and the counts $n\mathcal D_n(i)$ jump by at most one and never two at once; $\{\mathcal A_n(\omega)\}$, $\{\mathcal D_n(\omega)\}$, $\{q_n(\omega)\}$ have the property of item 4; there is $n_T(\omega)$ with $q_n(\omega,t,B_T+1)=0$ and $\ell_n(\omega,t)\le B_T$ for all $t\in[0,T]$, $n\ge n_T(\omega)$ (11); and for all $\gamma\in[0,1/2)$,
--   $$
--   \lim_{n\to\infty}q_n(0)=q(0),\quad \lim_{n\to\infty}\sup_{t\in[0,T]}n^\gamma\Big|\frac1n\mathcal N^\lambda_n(t)-\int_0^t\lambda(s)ds\Big|=0,\quad \lim_{n\to\infty}\sup_{t\in[0,\mu iT]}n^\gamma\Big|\frac1n\mathcal N_i(nt)-t\Big|=0\ (i\ge1).
--   $$
--
--   The set $\Omega_T$ of Proposition 7 is the set of nice outcomes; every pathwise result of §5 is stated for its members.
--
--   **Formalization Note** "Relatively compact in $D_{\mathbb R^{\mathbb N}}[0,T]$ for $\varrho$" is rendered sequentially through coordinatewise uniform convergence on $[0,T]$, which the paper states is equivalent to convergence in $\varrho$ (p. 46). $u_n$ and $v_n$ are real series; on nice outcomes they are finite sums for $n\ge n_T(\omega)$, which is all that limits see. A variant of $v_n$ with values in $[0,\infty]$ is used where a series appears in an inequality ((6c), Corollary 11). The simple-events clause and the initial conditions at $\omega$ are probability-one properties the paper's set of probability one implicitly carries (its arguments use that $q_n$ moves in steps of $1/n$ and that no two events coincide; see the footnote on p. 50). Limits of the form $\lim_n\sup_t(\cdot)=0$ are written as: for every $\varepsilon>0$, eventually in $n$, the bound holds for all $t$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, pp. 24–28, §5.1.1, Proposition 4, (7), Proposition 7 (11)–(12c); p. 33, (16); p. 46 (characterization of ϱ-convergence)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction

namespace UnknownLoads.Refined

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The coupled sequence of systems (§5.1.1): the primitives, control parameters `αₙ ∈ (0, 1)`,
and processes `qₙ(ω, t, i)` and `ℓₙ(ω, t)` that, almost surely, solve (9a)–(9b) on `[0, T]` for
every `n ≥ 1`. -/
structure System (D : LoadData) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (α : ℕ → ℝ)
    extends Primitives D Ω P where
  α_mem : ∀ n : ℕ, 1 ≤ n → α n ∈ Ioo (0 : ℝ) 1
  q : ℕ → Ω → ℝ → ℕ → ℝ
  ℓ : ℕ → Ω → ℝ → ℕ
  solves : ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n → toPrimitives.Solves (α n) n ω (q n ω) (ℓ n ω)

/-- A sequence `xₙ : [0, T] → ℝ^ℕ` is relatively compact for the metric `ϱ` of uniform
convergence (equivalently, coordinatewise uniform convergence on `[0, T]`, p. 46) and the limit of
every convergent subsequence has Lipschitz coordinates on `[0, T]`. -/
def IsRelCompactLip (T : ℝ) (x : ℕ → ℝ → ℕ → ℝ) : Prop :=
  (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ y : ℝ → ℕ → ℝ,
      ∀ i, TendstoUniformlyOn (fun k t => x (φ (ψ k)) t i) (fun t => y t i) atTop (Icc 0 T)) ∧
  (∀ φ : ℕ → ℕ, StrictMono φ → ∀ y : ℝ → ℕ → ℝ,
      (∀ i, TendstoUniformlyOn (fun k t => x (φ k) t i) (fun t => y t i) atTop (Icc 0 T)) →
      ∀ i, ∃ K : NNReal, LipschitzOnWith K (fun t => y t i) (Icc 0 T))

/-- The jump `g(t) − g(t⁻)` of a real path at `t`. -/
noncomputable def jumpAt (g : ℝ → ℝ) (t : ℝ) : ℝ := g t - Function.leftLim g t

namespace System

variable {D : LoadData} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
variable (sys : System D Ω P α)

/-- `𝒜ₙ = 𝒜ₙ(qₙ, ℓₙ)`. -/
noncomputable def arr (n : ℕ) (ω : Ω) (t : ℝ) (i : ℕ) : ℝ :=
  sys.arrivalProc n ω (sys.q n ω) (sys.ℓ n ω) t i

/-- `𝒟ₙ = 𝒟ₙ(qₙ)`. -/
noncomputable def dep (n : ℕ) (ω : Ω) (t : ℝ) (i : ℕ) : ℝ :=
  sys.departureProc n ω (sys.q n ω) t i

/-- The total mass `uₙ(t) = ∑_{i ≥ 1} qₙ(t, i)` of (7), as a real series (it is used only where
`qₙ(t, ·)` has finite support). -/
noncomputable def totalMass (n : ℕ) (ω : Ω) (t : ℝ) : ℝ := ∑' i, sys.q n ω t (i + 1)

/-- The tail mass `vₙ(t, j) = ∑_{i ≥ j} qₙ(t, i)` of (7), as a real series (used only where
`qₙ(t, ·)` has finite support). -/
noncomputable def tailMass (n : ℕ) (ω : Ω) (t : ℝ) (j : ℕ) : ℝ := ∑' i, sys.q n ω t (i + j)

/-- The tail mass `vₙ(t, j)` in `[0, ∞]`, `∑_{i ≥ j} qₙ(t, i)` with no summability caveat. -/
noncomputable def tailMassE (n : ℕ) (ω : Ω) (t : ℝ) (j : ℕ) : ENNReal :=
  ∑' i, ENNReal.ofReal (sys.q n ω t (i + j))

/-- The process `δₙ(t, j)` of (16):
`(1/n)𝒩^λ_n(t) − ∫₀ᵗ λ − ∑_{i=1}^{j} [𝒟ₙ(t, i) − ∫₀ᵗ µ i [qₙ(s, i) − qₙ(s, i+1)] ds]`. -/
noncomputable def delta (n : ℕ) (ω : Ω) (t : ℝ) (j : ℕ) : ℝ :=
  (1 / (n : ℝ)) * (sys.arrivals n ω t : ℝ) - D.cumRate t -
    ∑ i ∈ Finset.Icc 1 j, (sys.dep n ω t i -
      ∫ s in (0 : ℝ)..t, D.mu * i * (sys.q n ω s i - sys.q n ω s (i + 1)))

/-- The standing assumptions on the initial conditions, at the outcome `ω`. -/
def InitAt (ω : Ω) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    sys.qInit n ω ∈ OccupancySpace ∧ (∀ i, ∃ k : ℕ, (n : ℝ) * sys.qInit n ω i = k) ∧
      D.Δ ∣ sys.ℓInit n ω ∧ sys.qInit n ω (sys.B + 1) = 0 ∧ sys.ℓInit n ω ≤ sys.B

/-- At `ω`, in the `n`-th system, events on `(0, T]` are simple: the arrival process `𝒩^λ_n` and
the departure counts `n𝒟ₙ(i)` jump by at most one, and no two of them jump at the same time
(a probability-one property of the construction). -/
def SimpleEvents (n : ℕ) (ω : Ω) : Prop :=
  ∀ t ∈ Ioc 0 D.T,
    jumpAt (fun s => (sys.arrivals n ω s : ℝ)) t ≤ 1 ∧
    (∀ i, jumpAt (fun s => (n : ℝ) * sys.dep n ω s i) t ≤ 1) ∧
    (jumpAt (fun s => (sys.arrivals n ω s : ℝ)) t = 0 ∨
      ∀ i, jumpAt (fun s => (n : ℝ) * sys.dep n ω s i) t = 0) ∧
    (∀ i i', i ≠ i' → jumpAt (fun s => (n : ℝ) * sys.dep n ω s i) t = 0 ∨
      jumpAt (fun s => (n : ℝ) * sys.dep n ω s i') t = 0)

/-- `ω ∈ Ω_T` for the constant `B_T`: the outcome is a "nice sample path" in the sense of
Proposition 7 (pp. 27–28). It collects
* the standing initial assumptions and, for every `n ≥ 1`, the equations (9a)–(9b) and simple
  events at `ω` (`ω ∈ Γ₀`);
* the property of Proposition 4 for `𝒜ₙ`, `𝒟ₙ`, `qₙ` (`ω ∈ Γ_T`);
* (11): `qₙ(t, B_T + 1) = 0` and `ℓₙ(t) ≤ B_T` on `[0, T]` for all `n ≥ n_T(ω)`;
* (12a)–(12c) for all `γ ∈ [0, 1/2)`. -/
def IsNicePath (BT : ℕ) (ω : Ω) : Prop :=
  sys.InitAt ω ∧
  (∀ n : ℕ, 1 ≤ n →
    sys.Solves (α n) n ω (sys.q n ω) (sys.ℓ n ω) ∧ sys.SimpleEvents n ω) ∧
  IsRelCompactLip D.T (fun n => sys.arr n ω) ∧
  IsRelCompactLip D.T (fun n => sys.dep n ω) ∧
  IsRelCompactLip D.T (fun n => sys.q n ω) ∧
  (∃ nT : ℕ, ∀ n ≥ nT, ∀ t ∈ Icc 0 D.T, sys.q n ω t (BT + 1) = 0 ∧ sys.ℓ n ω t ≤ BT) ∧
  (∀ i, Tendsto (fun n => sys.q n ω 0 i) atTop (𝓝 (sys.q0 i))) ∧
  (∀ γ ∈ Ico (0 : ℝ) (1 / 2), ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc 0 D.T,
    (n : ℝ) ^ γ * |(1 / (n : ℝ)) * (sys.arrivals n ω t : ℝ) - D.cumRate t| ≤ ε) ∧
  (∀ γ ∈ Ico (0 : ℝ) (1 / 2), ∀ i : ℕ, 1 ≤ i → ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    ∀ t ∈ Icc 0 (D.mu * i * D.T),
      (n : ℝ) ^ γ * |(1 / (n : ℝ)) * ((sys.N i).count ((n : ℝ) * t) ω : ℝ) - t| ≤ ε)

end System

end UnknownLoads.Refined


