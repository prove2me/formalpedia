-- Prove2me | Definitions.Def_CondGeoVerif_Supplement_IsSmoothIsoLaw
-- name    : CondGeoVerif_Supplement_IsSmoothIsoLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:10:51.949583+00:00
-- url     : https://prove2.me/theorems/908a1194-5714-4983-97e7-61267192a910
-- title:
--   The smooth feature family $\mathcal D_\tau$, Massart noise relative to a feature law, and one-message soundness and completeness over a marginal family
-- statement:
--   For $0\le\tau<1$, $\mathcal D_\tau$ is the set of **centered isotropic laws** on $\mathbb R^d$ with a positive density $Z^{-1}e^{-V(x)}$, where $V\in C^2(\mathbb R^d)$ and
--   $$(1-\tau)I_d\preceq\nabla^2V(x)\preceq(1+\tau)I_d\qquad\text{for every }x\in\mathbb R^d.\qquad(5.1)/(G.1)$$
--   Massart noise of bound $\eta$ around $h^*$ relative to a feature law $\mu$ means $P(Y\ne h^*(X)\mid X)\le\eta$ almost surely.
--
--   A one-message verifier is **sound over a marginal family** $\mathcal M$ against a class $H$ if, for every law of $(X,Y)$ whose feature marginal lies in $\mathcal M$ (and any conditional label law) and every message, it outputs some $h$ with $R(h)>\mathrm{OPT}(H)+\varepsilon$ with probability at most $\delta$. It is **Massart complete over $\mathcal M$** with an honest prover if, for every such law with Massart noise $\le\eta$ around some member of $H$, the honest run outputs a predictor with $R(h)\le\mathrm{OPT}(H)+\varepsilon$ with probability at least $1-\delta$. With $\mathcal M=\{N(0,I_d)\}$ these are the published `OMSound` and `OMMassartComplete`.
--
--   **Formalization Note** The normalizing constant is absorbed into $V$; the Hessian bound is stated on the quadratic form $u\mapsto D^2V(x)(u,u)$; isotropy is $\int x_ix_j\,d\mu=\delta_{ij}$, with finite second moments (implied by the lower Hessian bound when $\tau<1$). Massart noise is the set inequality $P(X\in B,\,Y\ne h^*(X))\le\eta\,\mu(B)$ for Borel $B$.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), (5.1), p.11 (PDF p.14); §G.1, (G.1), p.57 (PDF p.60); Definition 2.1 and (2.1), p.3

import Mathlib
import Definitions.Def_CondGeoVerif_OneMsgVerifier

set_option autoImplicit false

namespace CondGeoVerif.Supplement

noncomputable section

open MeasureTheory CondGeoVerif
open scoped Matrix

/-- **The smooth feature family** `D_τ` (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, (5.1), p.11 = PDF p.14; (G.1), p.57 =
PDF p.60): `μ` is a centered isotropic law on `ℝᵈ` with a positive density `Z⁻¹e^{−V(x)}` for some
`V ∈ C²(ℝᵈ)` with `(1 − τ)I_d ⪯ ∇²V(x) ⪯ (1 + τ)I_d` for every `x`.

**Formalization Note** The normalizing constant is absorbed into `V` (`Z⁻¹e^{−V} = e^{−(V + log Z)}`
and `V + log Z` has the same Hessian), so `μ` is Lebesgue measure with density `e^{−V}` and is a
probability measure. The Hessian condition is stated on the quadratic form
`u ↦ D²V(x)(u, u)`. Centered means `∫ x dμ = 0` and isotropic means `∫ xᵢxⱼ dμ = δᵢⱼ`; the
second moments are required to be finite, which for `τ < 1` (the paper's range) already follows
from the lower Hessian bound, so the conjunct adds nothing there and keeps the two integrals
honest. -/
def IsSmoothIsoLaw {d : ℕ} (τ : ℝ) (μ : Measure (Vec d)) : Prop :=
  IsProbabilityMeasure μ ∧
  (∃ V : Vec d → ℝ, ContDiff ℝ 2 V ∧
    (∀ x u : Vec d, (1 - τ) * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x u u ∧
      fderiv ℝ (fderiv ℝ V) x u u ≤ (1 + τ) * ‖u‖ ^ 2) ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) ∧
  Integrable (fun x : Vec d => ‖x‖ ^ 2) μ ∧
  ∫ x, x ∂μ = 0 ∧
  ∀ i j : Fin d, ∫ x, x i * x j ∂μ = if i = j then 1 else 0

/-- The family `D_τ` as a set of feature laws on `ℝᵈ`. -/
def smoothFamily (d : ℕ) (τ : ℝ) : Set (Measure (Vec d)) := {μ | IsSmoothIsoLaw τ μ}

/-- **Massart noise relative to a feature law `μ`** (Chen, Oct. 2026, (2.1), p.3; §G.1, p.57):
`P(Y ≠ h*(X) | X) ≤ η` almost surely, stated as the set inequality
`P({X ∈ B, Y ≠ h*(X)}) ≤ η·μ(B)` for every Borel `B`, where `μ` is the feature marginal of `P`.
With `μ = N(0, I_d)` it is the published `IsMassart`. -/
def IsMassartWrt {d : ℕ} (P : Measure (Vec d × Bool)) (μ : Measure (Vec d))
    (hstar : Vec d → Bool) (η : ℝ) : Prop :=
  ∀ B : Set (Vec d), MeasurableSet B →
    P {p | p.1 ∈ B ∧ p.2 ≠ hstar p.1} ≤ ENNReal.ofReal η * μ B

/-- **Arbitrary-label soundness over a family of feature marginals** (Chen, Oct. 2026,
Definition 2.1, p.3; §G.1, p.57: "Both completeness and soundness promise this marginal family.
Soundness permits every measurable labeling"): the published `OMSound` with the Gaussian marginal
replaced by "the feature marginal lies in `Mar`". -/
def OMSoundOn {d : ℕ} {Msg : Type} (V : OneMsgVerifier d Msg) (Mar : Set (Measure (Vec d)))
    (H : Set (Vec d → Bool)) (ε δ : ℝ) : Prop :=
  ∀ P : ProbabilityMeasure (Vec d × Bool), (P : Measure (Vec d × Bool)).map Prod.fst ∈ Mar →
    ∀ msg : Msg,
      ((sampleLaw P V.m).prod (V.coins : Measure V.Ω))
          {sω | ∃ h, V.decide msg sω.1 sω.2 = some h ∧
            risk (P : Measure (Vec d × Bool)) h > opt (P : Measure (Vec d × Bool)) H + ε}
        ≤ ENNReal.ofReal δ

/-- **Full Massart completeness over a family of feature marginals** (Chen, Oct. 2026,
Definition 2.1, p.3; §G.1, p.57: "Completeness permits every Massart labeling with signal floor
a"): the published `OMMassartComplete` with the Gaussian marginal replaced by "the feature marginal
lies in `Mar`" and Massart noise taken relative to that marginal. -/
def OMMassartCompleteOn {d : ℕ} {Msg : Type} (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg)
    (Mar : Set (Measure (Vec d))) (H : Set (Vec d → Bool)) (η ε δ : ℝ) : Prop :=
  (Measurable (fun x : ((Fin Hon.mP → Vec d × Bool) × Hon.Ω) × ((Fin V.m → Vec d × Bool) × V.Ω) =>
      (V.decide (Hon.send x.1.1 x.1.2) x.2.1 x.2.2).isSome) ∧
    Measurable (fun p : (((Fin Hon.mP → Vec d × Bool) × Hon.Ω) ×
        ((Fin V.m → Vec d × Bool) × V.Ω)) × Vec d =>
      (V.decide (Hon.send p.1.1.1 p.1.1.2) p.1.2.1 p.1.2.2).getD (fun _ => false) p.2)) ∧
  ∀ P : ProbabilityMeasure (Vec d × Bool), (P : Measure (Vec d × Bool)).map Prod.fst ∈ Mar →
    ∀ hstar ∈ H,
      IsMassartWrt (P : Measure (Vec d × Bool)) ((P : Measure (Vec d × Bool)).map Prod.fst) hstar η →
      (((sampleLaw P Hon.mP).prod (Hon.coins : Measure Hon.Ω)).prod
          ((sampleLaw P V.m).prod (V.coins : Measure V.Ω)))
          {x | ¬ ∃ h, V.decide (Hon.send x.1.1 x.1.2) x.2.1 x.2.2 = some h ∧
            risk (P : Measure (Vec d × Bool)) h ≤ opt (P : Measure (Vec d × Bool)) H + ε}
        ≤ ENNReal.ofReal δ

end

end CondGeoVerif.Supplement


