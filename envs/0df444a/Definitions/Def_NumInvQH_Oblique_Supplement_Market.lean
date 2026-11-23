-- Prove2me | Definitions.Def_NumInvQH_Oblique_Supplement_Market
-- name    : NumInvQH_Oblique_Supplement_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:37:33.28818+00:00
-- url     : https://prove2.me/theorems/f0ddbee6-464f-4f69-aceb-6e2843ec2d8a
-- title:
--   Self-financing, tame and admissible strategies, deflators and opportunity
-- statement:
--   For a vector market $S$ and a predictable row strategy $\theta$, wealth is $W_t=\theta_tS_t$. Self-financing means $W-W_0=\theta\mathbin\bullet S$. Tameness bounds $E[W_\sigma^2]$ uniformly over every bounded stopping time $\sigma$. Admissibility is the source closure by tame wealths: convergence in probability at every stopping time, together with terminal $L^2$ convergence. The subinterval versions use $\mathcal F_\tau$-measurable initial holdings, a finite essential conditional second-moment bound and almost sure convergence of the conditional terminal squared errors, as in Definition 3.14.
--
--   A deflator has square-integrable terminal value, makes every zero-initial tame wealth a martingale after deflation, and makes some strictly positive self-financing wealth a martingale after deflation. An optimal hedge belongs to the admissible class with initial wealth $v$ and minimizes
--   $$E[(W_T-H)^2].$$
--   The loss and conditional second moments use extended nonnegative expectations. Niceness requires $N,N_->0$ and deterministic positive finite bounds on $E[N_T^2\mid\mathcal F_t]/N_t^2$. The opportunity process is the greatest measurable almost sure lower bound of conditional terminal second moments of fully invested admissible wealths started at $t$. Discounting, the changed measure, and $E[X_T^2\mid\mathcal F_t]$ (a càdlàg version when one exists, otherwise its conditional-expectation version) are constructed from $S,X,P$, not supplied independently.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 2–3, 6–10, Definitions 3.1, 3.3, 3.5, 3.9, 3.10, 3.14–3.16

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Integration

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace NumInvQH.Oblique.Supplement

attribute [local instance] Classical.propDecidable Classical.decEq

structure BoundedStop {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0) where
  time : Ω → ℝ≥0
  stopping : IsStoppingTime ℱ (fun ω => (time ω : WithTop ℝ≥0))
  bounded : ∀ ω, time ω ≤ T

/-- Value of a row-vector strategy in a column-vector market. -/
def wealth {Ω : Type*} {d : ℕ} (θ S : Process Ω (Fin d → ℝ)) : Process Ω ℝ :=
  fun t ω => θ t ω ⬝ᵥ S t ω

/-- The integral graph, not an arbitrary wealth dynamics, enforces self-financing. -/
def SelfFinancing {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S θ : Process Ω (Fin d → ℝ)) : Prop :=
  HasIntegral P ℱ T θ S (fun t ω => wealth θ S t ω - wealth θ S 0 ω)

noncomputable def after {Ω E : Type*} [Zero E] (τ : Ω → ℝ≥0) (f : Process Ω E) :
    Process Ω E := fun t ω => if τ ω < t then f t ω else 0

/-- Definition 3.3: θ_τ is only F_τ-measurable; no predictability is required at τ. -/
def SelfFinancingFrom {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S θ : Process Ω (Fin d → ℝ)) (τ : BoundedStop ℱ T) : Prop :=
  StronglyMeasurable[τ.stopping.measurableSpace] (fun ω => θ (τ.time ω) ω) ∧
  ∃ I, HasIntegral P ℱ T (after τ.time θ) S I ∧
    ∀ᵐ ω ∂P, ∀ t, τ.time ω ≤ t → t ≤ T →
      wealth θ S t ω = wealth θ S (τ.time ω) ω + I t ω

/-- A uniform second-moment bound over all bounded stopping times; no real supremum defaults. -/
def Tame {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S θ : Process Ω (Fin d → ℝ)) : Prop :=
  SelfFinancing P ℱ T S θ ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ τ : BoundedStop ℱ T, ∫⁻ ω, ENNReal.ofReal (wealth θ S (τ.time ω) ω ^ 2) ∂P ≤ K

/-- Definition 3.9: convergence at every stopping time in probability, and in L² at T. -/
def Admissible {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S θ : Process Ω (Fin d → ℝ)) : Prop :=
  SelfFinancing P ℱ T S θ ∧ ∃ θs : ℕ → Process Ω (Fin d → ℝ),
    (∀ n, Tame P ℱ T S (θs n)) ∧
    (∀ τ : BoundedStop ℱ T, TendstoInMeasure P
      (fun n ω => wealth (θs n) S (τ.time ω) ω) atTop (fun ω => wealth θ S (τ.time ω) ω)) ∧
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal ((wealth (θs n) S T ω - wealth θ S T ω)^2) ∂P)
      atTop (𝓝 0)

/-- Conditional tameness uses the generalized nonnegative conditional expectation.
A measurable finite upper bound is the exact meaning of a finite essential supremum. -/
def TameFrom {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S θ : Process Ω (Fin d → ℝ)) (τ : BoundedStop ℱ T) : Prop :=
  SelfFinancingFrom P ℱ T S θ τ ∧
  ∃ K : Ω → ℝ≥0∞, Measurable[τ.stopping.measurableSpace] K ∧
    (∀ᵐ ω ∂P, K ω < ⊤) ∧
    ∀ σ : BoundedStop ℱ T, (∀ ω, τ.time ω ≤ σ.time ω) →
      ∀ᵐ ω ∂P, condLExp τ.stopping.measurableSpace P
        (fun w => ENNReal.ofReal (wealth θ S (σ.time w) w ^ 2)) ω ≤ K ω

/-- Definition 3.14: the conditional L² error converges almost surely, not just in probability. -/
def AdmissibleFrom {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S θ : Process Ω (Fin d → ℝ)) (τ : BoundedStop ℱ T) : Prop :=
  SelfFinancingFrom P ℱ T S θ τ ∧ ∃ θs : ℕ → Process Ω (Fin d → ℝ),
    (∀ n, TameFrom P ℱ T S (θs n) τ) ∧
    (∀ σ : BoundedStop ℱ T, (∀ ω, τ.time ω ≤ σ.time ω) → TendstoInMeasure P
      (fun n ω => wealth (θs n) S (σ.time ω) ω) atTop (fun ω => wealth θ S (σ.time ω) ω)) ∧
    ∀ᵐ ω ∂P, Tendsto (fun n => condLExp τ.stopping.measurableSpace P
      (fun w => ENNReal.ofReal ((wealth (θs n) S T w - wealth θ S T w)^2)) ω) atTop (𝓝 0)

/-- Definition 3.10, including its nonzero-wealth test strategy. -/
def Deflator {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S : Process Ω (Fin d → ℝ)) (Z : Process Ω ℝ) : Prop :=
  MemLp (Z T) 2 P ∧
  (∀ θ, Tame P ℱ T S θ → (∀ᵐ ω ∂P, wealth θ S 0 ω = 0) →
    Martingale (stop T (fun t ω => Z t ω * wealth θ S t ω)) ℱ P) ∧
  ∃ φ, SelfFinancing P ℱ T S φ ∧ (∀ᵐ ω ∂P, ∀ t ≤ T, 0 < wealth φ S t ω) ∧
    Martingale (stop T (fun t ω => Z t ω * wealth φ S t ω)) ℱ P

/-- Extended nonnegative objective; nonintegrable squared errors are infinite, not zero. -/
noncomputable def loss {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (T : ℝ≥0) (S θ : Process Ω (Fin d → ℝ)) (H : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((wealth θ S T ω - H ω)^2) ∂P

def Optimal {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S θ : Process Ω (Fin d → ℝ)) (v : ℝ) (H : Ω → ℝ) : Prop :=
  Admissible P ℱ T S θ ∧ (∀ᵐ ω ∂P, wealth θ S 0 ω = v) ∧
  ∀ η, Admissible P ℱ T S η → (∀ᵐ ω ∂P, wealth η S 0 ω = v) →
    loss P T S θ H ≤ loss P T S η H

/-- Strict positivity of a process and its left limit on the whole finite horizon. -/
def Positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (N : Process Ω ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t ≤ T, 0 < N t ω ∧ 0 < left N t ω

/-- Definition 3.16, with an extended conditional expectation to exclude Bochner junk values. -/
def Nice {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (N : Process Ω ℝ) : Prop :=
  Positive P T N ∧ ∃ δ Δ : ℝ, 0 < δ ∧ δ ≤ Δ ∧
    ∀ t ≤ T, ∀ᵐ ω ∂P,
      ENNReal.ofReal (δ * N t ω ^ 2) ≤ condLExp (ℱ t) P (fun w => ENNReal.ofReal (N T w ^ 2)) ω ∧
      condLExp (ℱ t) P (fun w => ENNReal.ofReal (N T w ^ 2)) ω ≤ ENNReal.ofReal (Δ * N t ω ^ 2)

noncomputable def discounted {Ω : Type*} {d : ℕ}
    (S : Process Ω (Fin d → ℝ)) (X : Process Ω ℝ) : Process Ω (Fin d → ℝ) :=
  fun t ω i => S t ω i / X t ω

noncomputable def changedMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (X : Process Ω ℝ) : Measure Ω :=
  P.withDensity (fun ω => ENNReal.ofReal (X T ω ^ 2 / ∫ w, X T w ^ 2 ∂P))

/-- A cadlag martingale version of the conditional terminal second moment. -/
def DensityVersion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X Z : Process Ω ℝ) : Prop :=
  ScalarSemi P ℱ T Z ∧ Martingale (stop T Z) ℱ P ∧
    ∀ t ≤ T, Z t =ᵐ[P] P[fun ω => X T ω ^ 2 | ℱ t]

noncomputable def densityNumerator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : Process Ω ℝ) : Process Ω ℝ :=
  if h : ∃ Z, DensityVersion P ℱ T X Z then Classical.choose h
    else fun t => P[fun ω => X T ω ^ 2 | ℱ t]

/-- Definition 3.15 as the greatest measurable a.s. lower bound of conditional second moments. -/
def Opportunity {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S : Process Ω (Fin d → ℝ)) (L : Process Ω ℝ) : Prop :=
  ∀ t (ht : t ≤ T), Measurable[ℱ t] (L t) ∧ (∀ᵐ ω ∂P, 0 ≤ L t ω) ∧
    let τ : BoundedStop ℱ T := ⟨fun _ => t, isStoppingTime_const ℱ t, fun _ => ht⟩
    (∀ θ, AdmissibleFrom P ℱ T S θ τ → (∀ᵐ ω ∂P, wealth θ S t ω = 1) →
      ∀ᵐ ω ∂P, ENNReal.ofReal (L t ω) ≤
        condLExp (ℱ t) P (fun w => ENNReal.ofReal (wealth θ S T w ^ 2)) ω) ∧
    (∀ Y : Ω → ℝ≥0∞, Measurable[ℱ t] Y →
      (∀ θ, AdmissibleFrom P ℱ T S θ τ → (∀ᵐ ω ∂P, wealth θ S t ω = 1) →
        ∀ᵐ ω ∂P, Y ω ≤ condLExp (ℱ t) P (fun w => ENNReal.ofReal (wealth θ S T w ^ 2)) ω) →
      ∀ᵐ ω ∂P, Y ω ≤ ENNReal.ofReal (L t ω))

end NumInvQH.Oblique.Supplement


