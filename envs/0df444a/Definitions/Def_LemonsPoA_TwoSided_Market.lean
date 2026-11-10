-- Prove2me | Definitions.Def_LemonsPoA_TwoSided_Market
-- name    : LemonsPoA_TwoSided_Market
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:10:36.546601+00:00
-- url     : https://prove2.me/theorems/1883cbd9-2207-40f4-88b9-78a805d56c3e
-- title:
--   Market instance with affine interdependent values, finite signals and the news ordering; first-best gains from trade $FB$, belief-robust values $\hat v$ and $R$
-- statement:
--   A **market instance** $I=(v,G,F,\Sigma_S,\Sigma_B)$ (§2): a seller holds an asset and a buyer may buy it.
--
--   * **Types.** A measurable type space $\Theta$ with a probability measure $G$; the seller's type $\theta_S$ and the buyer's type $\theta_B$ are i.i.d. with law $G$.
--   * **Values.** $v(c,\theta)=c\,x(\theta)+y(\theta)$ with $x,y:\Theta\to\mathbb R$ measurable and $x\ge 0$ (12), where $c$ is the realized **common component**.
--   * **Common component and signals.** $(C,\Sigma_S,\Sigma_B)$ takes values in $\mathbb R\times S_S\times S_B$ with $S_S,S_B$ finite, has an arbitrary joint law, and is independent of $(\theta_S,\theta_B)$. The seller observes $\Sigma_S$, the buyer $\Sigma_B$; $F$ is the law of $C$, and $\mu=E[C]$.
--   * $m(\sigma_S,\sigma_B)=E[C\mid\Sigma_S=\sigma_S,\Sigma_B=\sigma_B]$, and the conditional signal probabilities $\Pr[\Sigma_S=\sigma_S\mid\Sigma_B=\sigma_B]$, $\Pr[\Sigma_B=\sigma_B\mid\Sigma_S=\sigma_S]$, and $E[C\mid\Sigma_S=\sigma_S]$.
--   * **News ordering** (13)-(14): for all $\sigma_S,\sigma_S'\in S_S$, $\sigma_B,\sigma_B'\in S_B$,
--   $$m(\sigma_S,\sigma_B)\le m(\sigma_S,\sigma_B')\Rightarrow m(\sigma_S',\sigma_B)\le m(\sigma_S',\sigma_B'),\qquad m(\sigma_S,\sigma_B)\le m(\sigma_S',\sigma_B)\Rightarrow m(\sigma_S,\sigma_B')\le m(\sigma_S',\sigma_B').$$
--   * **Most pessimistic seller signal / most optimistic buyer signal** (41): $\sigma^-_S$ minimizes $m(\cdot,\sigma_B)$ for every buyer signal $\sigma_B$, and $\sigma^+_B$ maximizes $m(\sigma_S,\cdot)$ for every seller signal $\sigma_S$.
--   * **First-best gains from trade** (15): $FB=E[(v(C,\theta_B)-v(C,\theta_S))_+]$.
--   * **Belief-robust values** (42)-(43): for a forecast $d$ (in §5, $d=m(\sigma^-_S,\sigma^+_B)$), $\hat v(\theta)=d\,x(\theta)+y(\theta)$, $\hat v_S=\hat v(\theta_S)$, $\hat v_B=\hat v(\theta_B)$, and $R=E[(\hat v_B-\hat v_S)_+]$, the first-best of this independent-private-values market.
--
--   **Formalization Note** The joint law of $(C,\Sigma_S,\Sigma_B)$ is stored as the finite measures `F σS σB` $:A\mapsto\Pr[C\in A,\Sigma_S=\sigma_S,\Sigma_B=\sigma_B]$ with total mass $1$ (every law on $\mathbb R\times S_S\times S_B$ is uniquely of this form; total mass $1$ forces $S_S,S_B$ nonempty). `lawC` $=\sum F(\sigma_S,\sigma_B)$ is the law of $C$, `meanC` $=\mu$. `expect g` $=\sum_{\sigma_S,\sigma_B}\int g\,d(F(\sigma_S,\sigma_B)\otimes G\otimes G)$ is the expectation under the product law (Bochner integrals: meaningful under the integrability hypotheses of each theorem). Conditional quantities are ratios; they are meaningful only on events of positive probability, so `NewsOrdered`, `IsPessimistic` and `IsOptimistic` compare $m$ only on signal pairs of positive probability. $\sigma^-_S,\sigma^+_B$ are not chosen by the definition: theorems take them as variables with the hypotheses `IsPessimistic`, `IsOptimistic`. In `R`, the pair is $(\theta_S,\theta_B)\sim G\otimes G$.
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), pp. 13-15 and 25, §2, (12)-(15), (41)-(43)

import Mathlib

open MeasureTheory

namespace LemonsPoA.TwoSided

/-- A market instance `(v, G, F, Σ_S, Σ_B)` (§2, pp. 13–14).

* `Θ` is a measurable type space with the type distribution `G` (a probability measure); the
  seller's and the buyer's types are i.i.d. `G`.
* Values are affine in the common component: `v(c, θ) = c x(θ) + y(θ)` with `x, y` measurable
  and `x ≥ 0` (display (12)).
* `SS`, `SB` are the finite seller and buyer signal spaces.
* The joint law of `(C, Σ_S, Σ_B)` on `ℝ × SS × SB` is recorded by its restrictions to the
  finitely many signal events: `F σS σB` is the finite measure `A ↦ Pr[C ∈ A, Σ_S = σS,
  Σ_B = σB]`; these masses sum to `1`. (Every law on `ℝ × SS × SB` is uniquely of this form.)
  The common component and signals are independent of the two types. -/
structure Market (Θ : Type*) [MeasurableSpace Θ] (SS SB : Type*) [Fintype SS] [Fintype SB] where
  /-- the type distribution `G` -/
  G : Measure Θ
  isProbabilityMeasure_G : IsProbabilityMeasure G
  /-- slope of the value in the common component -/
  x : Θ → ℝ
  /-- intercept of the value -/
  y : Θ → ℝ
  measurable_x : Measurable x
  measurable_y : Measurable y
  x_nonneg : ∀ θ, 0 ≤ x θ
  /-- `F σS σB A = Pr[C ∈ A, Σ_S = σS, Σ_B = σB]` -/
  F : SS → SB → Measure ℝ
  isFiniteMeasure_F : ∀ σS σB, IsFiniteMeasure (F σS σB)
  total_mass : ∑ σS, ∑ σB, F σS σB Set.univ = 1

namespace Market

variable {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]
variable (M : Market Θ SS SB)

/-- The value `v(c, θ) = c x(θ) + y(θ)` (12). -/
def v (c : ℝ) (θ : Θ) : ℝ := c * M.x θ + M.y θ

/-- The law `F` of the common component `C`. -/
noncomputable def lawC : Measure ℝ := ∑ σS, ∑ σB, M.F σS σB

/-- `µ = E[C]`. -/
noncomputable def meanC : ℝ := ∫ c, c ∂M.lawC

/-- `Pr[Σ_S = σS, Σ_B = σB]`. -/
noncomputable def jointProb (σS : SS) (σB : SB) : ℝ := (M.F σS σB Set.univ).toReal

/-- `Pr[Σ_S = σS]`. -/
noncomputable def probS (σS : SS) : ℝ := ∑ σB, M.jointProb σS σB

/-- `Pr[Σ_B = σB]`. -/
noncomputable def probB (σB : SB) : ℝ := ∑ σS, M.jointProb σS σB

/-- `Pr[Σ_S = σS | Σ_B = σB]` (meaningful when `Pr[Σ_B = σB] > 0`). -/
noncomputable def condS (σS : SS) (σB : SB) : ℝ := M.jointProb σS σB / M.probB σB

/-- `Pr[Σ_B = σB | Σ_S = σS]` (meaningful when `Pr[Σ_S = σS] > 0`). -/
noncomputable def condB (σS : SS) (σB : SB) : ℝ := M.jointProb σS σB / M.probS σS

/-- `m(σS, σB) = E[C | Σ_S = σS, Σ_B = σB]` (p. 14), meaningful on pairs of positive
probability. -/
noncomputable def m (σS : SS) (σB : SB) : ℝ := (∫ c, c ∂M.F σS σB) / M.jointProb σS σB

/-- `E[C | Σ_S = σS]` (meaningful when `Pr[Σ_S = σS] > 0`). -/
noncomputable def condMeanS (σS : SS) : ℝ :=
  (∑ σB, ∫ c, c ∂M.F σS σB) / M.probS σS

/-- The news ordering (13)–(14), imposed on signal quadruples whose four pairs all have positive
probability (where `m` is defined). -/
def NewsOrdered : Prop :=
  ∀ (σS σS' : SS) (σB σB' : SB),
    0 < M.jointProb σS σB → 0 < M.jointProb σS σB' →
    0 < M.jointProb σS' σB → 0 < M.jointProb σS' σB' →
    (M.m σS σB ≤ M.m σS σB' → M.m σS' σB ≤ M.m σS' σB') ∧
    (M.m σS σB ≤ M.m σS' σB → M.m σS σB' ≤ M.m σS' σB')

/-- `σm` is a most pessimistic seller signal (41): `σm ∈ argmin_{σS} m(σS, σB)` simultaneously for
every buyer signal `σB` (comparisons among pairs of positive probability). -/
def IsPessimistic (σm : SS) : Prop :=
  ∀ (σS : SS) (σB : SB), 0 < M.jointProb σm σB → 0 < M.jointProb σS σB →
    M.m σm σB ≤ M.m σS σB

/-- `σp` is a most optimistic buyer signal (41): `σp ∈ argmax_{σB} m(σS, σB)` simultaneously for
every seller signal `σS` (comparisons among pairs of positive probability). -/
def IsOptimistic (σp : SB) : Prop :=
  ∀ (σS : SS) (σB : SB), 0 < M.jointProb σS σp → 0 < M.jointProb σS σB →
    M.m σS σB ≤ M.m σS σp

/-- The law of `(C, θ_S, θ_B)` on the signal event `{Σ_S = σS, Σ_B = σB}`:
`F σS σB ⊗ G ⊗ G` (types i.i.d. `G`, independent of `(C, Σ_S, Σ_B)`). -/
noncomputable def lawAt (σS : SS) (σB : SB) : Measure (ℝ × Θ × Θ) :=
  (M.F σS σB).prod (M.G.prod M.G)

/-- Expectation `E[g(C, Σ_S, Σ_B, θ_S, θ_B)]` under the product law of the market. -/
noncomputable def expect (g : ℝ → SS → SB → Θ → Θ → ℝ) : ℝ :=
  ∑ σS, ∑ σB, ∫ z, g z.1 σS σB z.2.1 z.2.2 ∂(M.lawAt σS σB)

/-- First-best gains from trade (15): `FB = E[(v(C, θ_B) - v(C, θ_S))_+]`. -/
noncomputable def FB : ℝ :=
  M.expect fun c _ _ θS θB => max (M.v c θB - M.v c θS) 0

/-- Belief-robust value at forecast `d` (42): `v̂(θ) = d x(θ) + y(θ)`. -/
def vhat (d : ℝ) (θ : Θ) : ℝ := d * M.x θ + M.y θ

/-- First-best gains from trade of the belief-robust (IPV) market at forecast `d` (43):
`R = E[(v̂_B - v̂_S)_+]` with `θ_S, θ_B` i.i.d. `G` (the pair is `(θ_S, θ_B)`). -/
noncomputable def R (d : ℝ) : ℝ :=
  ∫ z, max (M.vhat d z.2 - M.vhat d z.1) 0 ∂(M.G.prod M.G)

end Market

end LemonsPoA.TwoSided


