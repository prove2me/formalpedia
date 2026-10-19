-- Prove2me | Definitions.Def_MKVLimit_Value_Strong
-- name    : MKVLimit_Value_Strong
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:43.074116+00:00
-- url     : https://prove2.me/theorems/86e9d328-fe81-4b3c-b55d-f9631a7b245a
-- title:
--   Strong common-noise control problem and value $V_S$
-- statement:
--   Fix an initial law $\nu$ on $\mathbb R^n$. The strong canonical space is $\Omega=\mathbb R^n\times C^d\times C^\ell$, with initial state $X_0$, individual Brownian motion $W$, and common Brownian motion $B$. The law $\mathbb P_\nu$ is characterized by $X_0\sim\nu$ and a standard joint Brownian motion relative to the raw canonical filtration. An admissible predictable control $\alpha$ obeys the integrated $p$th-moment condition (2.2). Its continuous adapted solution solves (2.3) with the conditional law of its own stopped path and current control inside the coefficients. The terminal conditional state-path law enters the reward. The strong value is
--
--   $$V_S(\nu)=\sup_{\alpha\in\mathcal A_p(\nu)}\mathbb E^{\mathbb P_\nu}\left[\int_0^T L(t,X^\alpha_{t\wedge\cdot},\bar\mu_t^\alpha,\alpha_t)\,dt+g(X^\alpha,\mu_T^\alpha)\right].$$
--
--   This defines the limiting value in Theorem 3.6.
--
--   **Formalization Note** The supremum ranges over admissible controls together with their actual solutions, using uniqueness cited by the paper. Conditional laws use the raw common-noise filtration and a Fubini reading of time–probability almost everywhere. Solutions are adapted to the completed full filtration and have measurable continuous paths. Scalar Itô integrals are certified entrywise by the published Ethier–Kurtz relation. Rewards use extended-real signed integrals.
-- source:
--   Djete, Possamaï & Tan, McKean–Vlasov optimal control: limit theory and equivalence between different formulations, arXiv:2001.00925v2, pp. 4–5, §2.1, equations (2.2)–(2.4)

import Definitions.Def_MKVLimit_Value_Setting
import Mathlib.Probability.Process.Predictable

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVLimit.Value

variable {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
variable [MetricSpace U] [MeasurableSpace U]

abbrev OmegaS (T : ℝ≥0) (n d ℓ : ℕ) := Rn n × Cpath T d × Cpath T ℓ

private theorem measurable_pathAt {k : ℕ} (s : ℝ≥0) :
    Measurable (fun x : Cpath T k => pathAt x s) :=
  (continuous_eval_const _).measurable

noncomputable def Fs (T : ℝ≥0) (n d ℓ : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (OmegaS T n d ℓ)) where
  seq t := ⨆ s ≤ t, MeasurableSpace.comap
    (fun ω : OmegaS T n d ℓ => (ω.1, pathAt ω.2.1 s, pathAt ω.2.2 s)) inferInstance
  mono' _ _ hst := iSup₂_le fun s hs => le_iSup₂
    (f := fun s (_ : s ≤ _) => MeasurableSpace.comap
      (fun ω : OmegaS T n d ℓ => (ω.1, pathAt ω.2.1 s, pathAt ω.2.2 s)) inferInstance)
    s (hs.trans hst)
  le' _ := iSup₂_le fun s _ =>
    (Measurable.prodMk measurable_fst
      (Measurable.prodMk ((measurable_pathAt s).comp (measurable_fst.comp measurable_snd))
        ((measurable_pathAt s).comp (measurable_snd.comp measurable_snd)))).comap_le

noncomputable def Gs (T : ℝ≥0) (n d ℓ : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (OmegaS T n d ℓ)) where
  seq t := ⨆ s ≤ t, MeasurableSpace.comap
    (fun ω : OmegaS T n d ℓ => pathAt ω.2.2 s) inferInstance
  mono' _ _ hst := iSup₂_le fun s hs => le_iSup₂
    (f := fun s (_ : s ≤ _) => MeasurableSpace.comap
      (fun ω : OmegaS T n d ℓ => pathAt ω.2.2 s) inferInstance)
    s (hs.trans hst)
  le' _ := iSup₂_le fun s _ =>
    ((measurable_pathAt s).comp (measurable_snd.comp measurable_snd)).comap_le

/-- Predictable σ-algebra of the raw full canonical filtration. -/
def predictableOf {Ω : Type*} [MeasurableSpace Ω]
    (H : ℝ≥0 → MeasurableSpace Ω) : MeasurableSpace (ℝ≥0 × Ω) :=
  MeasurableSpace.generateFrom <|
    {S | ∃ A, MeasurableSet[H 0] A ∧ S = {0} ×ˢ A} ∪
    {S | ∃ s A, MeasurableSet[H s] A ∧ S = Set.Ioi s ×ˢ A}

/-- Wiener law on the strong canonical space, characterized by its initial law and
joint Brownian increments relative to the raw canonical filtration. -/
def IsStrongLaw (ν : ProbabilityMeasure (Rn n)) (P : Measure (OmegaS T n d ℓ)) : Prop :=
  IsProbabilityMeasure P ∧
  Measure.map (fun ω : OmegaS T n d ℓ => ω.1) P = (ν : Measure (Rn n)) ∧
  IsFBrownian (Fs T n d ℓ) P T (fun s ω => pathAt ω.2.1 s) ∧
  IsFBrownian (Fs T n d ℓ) P T (fun s ω => pathAt ω.2.2 s) ∧
  IndepFun (fun ω : OmegaS T n d ℓ => ω.2.1) (fun ω => ω.2.2) P ∧
  ∀ s u, s ≤ u → u ≤ T →
    Indep (MeasurableSpace.comap
      (fun ω : OmegaS T n d ℓ =>
        (pathAt ω.2.1 u - pathAt ω.2.1 s, pathAt ω.2.2 u - pathAt ω.2.2 s)) inferInstance)
      (Fs T n d ℓ s) P

/-- The paper's strong admissible controls, equation (2.2). -/
def IsAdmissible (M : Model T n d ℓ U) (p : ℝ) (P : Measure (OmegaS T n d ℓ))
    (α : ℝ≥0 → OmegaS T n d ℓ → U) : Prop :=
  Measurable[predictableOf (Fs T n d ℓ)] (fun z : ℝ≥0 × OmegaS T n d ℓ => α z.1 z.2) ∧
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (T : ℝ),
    edist (α s.toNNReal ω) M.a₀ ^ p ∂volume ∂P < ⊤

/-- Quadratic energy of the actual diffusion integrands. -/
noncomputable def goodDiffusion (M : Model T n d ℓ U)
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → Cpath T n)
    (α : ℝ≥0 → Ω → U)
    (μbar : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)) : Set Ω :=
  {ω | ∫⁻ r in Set.Icc (0 : ℝ) (T : ℝ), ENNReal.ofReal
    (pairNorm (M.σ r.toNNReal (stopPath r.toNNReal (X ω))
      (μbar r.toNNReal ω) (α r.toNNReal ω))
      (M.σ₀ r.toNNReal (stopPath r.toNNReal (X ω))
      (μbar r.toNNReal ω) (α r.toNNReal ω)) ^ 2) ∂volume < ⊤}

/-- Equation (2.3), interpreted entrywise through the published Itô relation. -/
def SDEEquation (M : Model T n d ℓ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (ξ : Ω → Rn n) (X : Ω → Cpath T n)
    (W : Ω → Cpath T d) (B : Ω → Cpath T ℓ)
    (α : ℝ≥0 → Ω → U)
    (μbar : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)) : Prop :=
  P (goodDiffusion M X α μbar)ᶜ = 0 ∧
  (∀ᵐ ω ∂P, IntervalIntegrable
    (fun r : ℝ => M.b r.toNNReal (stopPath r.toNNReal (X ω))
      (μbar r.toNNReal ω) (α r.toNNReal ω)) volume 0 (T : ℝ)) ∧
  ∃ (Jσ : Fin n → Fin d → ℝ≥0 → Ω → ℝ)
    (Jσ₀ : Fin n → Fin ℓ → ℝ≥0 → Ω → ℝ),
    (∀ i j, EthierKurtz.HasBrownianItoIntegral P (EthierKurtz.completedSDEPast P F)
      (fun s ω => pathAt (W ω) s j)
      (fun r ω => if r ≤ T ∧ ω ∈ goodDiffusion M X α μbar then
        M.σ r (stopPath r (X ω)) (μbar r ω) (α r ω) i j else 0)
      (Jσ i j)) ∧
    (∀ i j, EthierKurtz.HasBrownianItoIntegral P (EthierKurtz.completedSDEPast P F)
      (fun s ω => pathAt (B ω) s j)
      (fun r ω => if r ≤ T ∧ ω ∈ goodDiffusion M X α μbar then
        M.σ₀ r (stopPath r (X ω)) (μbar r ω) (α r ω) i j else 0)
      (Jσ₀ i j)) ∧
    ∀ t, t ≤ T → ∀ᵐ ω ∂P, ∀ i : Fin n,
      pathAt (X ω) t i = ξ ω i +
        (∫ r in (0 : ℝ)..(t : ℝ),
          M.b r.toNNReal (stopPath r.toNNReal (X ω))
            (μbar r.toNNReal ω) (α r.toNNReal ω)) i +
        ∑ j : Fin d, Jσ i j t ω +
        ∑ j : Fin ℓ, Jσ₀ i j t ω

/-- The solution's own conditional laws appear in its SDE and reward. -/
def IsStrongSolution (M : Model T n d ℓ U) (p : ℝ)
    (P : Measure (OmegaS T n d ℓ))
    (α : ℝ≥0 → OmegaS T n d ℓ → U)
    (X : OmegaS T n d ℓ → Cpath T n)
    (μbar : ℝ≥0 → OmegaS T n d ℓ → ProbabilityMeasure (Cpath T n × U))
    (μ : ℝ≥0 → OmegaS T n d ℓ → ProbabilityMeasure (Cpath T n)) : Prop :=
  Measurable X ∧
  Measurable (fun z : ℝ≥0 × OmegaS T n d ℓ => μbar z.1 z.2) ∧
  (∀ t, t ≤ T → Measurable[EthierKurtz.completedSDEPast P (Fs T n d ℓ) t]
      (fun ω => pathAt (X ω) t)) ∧
  (∫⁻ ω, ENNReal.ofReal (‖X ω‖ ^ p) ∂P) < ⊤ ∧
  (∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) (T : ℝ)),
    IsCondLaw (Gs T n d ℓ s.toNNReal) P
      (fun ω => (stopPath s.toNNReal (X ω), α s.toNNReal ω)) (μbar s.toNNReal)) ∧
  (∀ t, t ≤ T → IsCondLaw (Gs T n d ℓ t) P
      (fun ω => stopPath t (X ω)) (μ t)) ∧
  SDEEquation M P (Fs T n d ℓ) (fun ω => ω.1) X
    (fun ω => ω.2.1) (fun ω => ω.2.2) α μbar

noncomputable def strongReward (M : Model T n d ℓ U)
    (P : Measure (OmegaS T n d ℓ)) (α : ℝ≥0 → OmegaS T n d ℓ → U)
    (X : OmegaS T n d ℓ → Cpath T n)
    (μbar : ℝ≥0 → OmegaS T n d ℓ → ProbabilityMeasure (Cpath T n × U))
    (μ : ℝ≥0 → OmegaS T n d ℓ → ProbabilityMeasure (Cpath T n)) : EReal :=
  eExp P (fun ω => timeInt 0 T
    (fun t => (M.L t (stopPath t (X ω)) (μbar t ω) (α t ω) : EReal)) +
      (M.g (X ω) (μ T ω) : EReal))

/-- Strong value (2.4), over admissible controls and their solutions. -/
noncomputable def VS (M : Model T n d ℓ U) (p : ℝ)
    (ν : ProbabilityMeasure (Rn n)) (P : Measure (OmegaS T n d ℓ)) : EReal :=
  ⨆ (α : ℝ≥0 → OmegaS T n d ℓ → U), ⨆ (_ : IsAdmissible M p P α),
  ⨆ (X : OmegaS T n d ℓ → Cpath T n),
  ⨆ (μbar : ℝ≥0 → OmegaS T n d ℓ → ProbabilityMeasure (Cpath T n × U)),
  ⨆ (μ : ℝ≥0 → OmegaS T n d ℓ → ProbabilityMeasure (Cpath T n)),
  ⨆ (_ : IsStrongSolution M p P α X μbar μ), strongReward M P α X μbar μ

end MKVLimit.Value


