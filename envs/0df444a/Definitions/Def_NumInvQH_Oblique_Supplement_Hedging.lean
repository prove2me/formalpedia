-- Prove2me | Definitions.Def_NumInvQH_Oblique_Supplement_Hedging
-- name    : NumInvQH_Oblique_Supplement_Hedging
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:40:05.853968+00:00
-- url     : https://prove2.me/theorems/cd35b1a2-ce28-406a-8d96-8eec09455075
-- title:
--   Full opportunity characterization, feedback hedge and error interface
-- statement:
--   This file supplies named predicates for all clauses of Theorem 4.1, rather than assuming those clauses in the theorem. The characteristic rates are the genuine weighted rates divided by $\rho=1+\Delta B^{\mathcal L(L)}$. The opportunity measure is computed from $L$, its canonical compensator and its stochastic exponential. The pointwise minimizers use the published base definition of the genuine constrained quadratic argmin.
--
--   The characterization includes bounded semimartingale status, positivity of $L,L_-$, $L_T=1$, the positive martingale quotient, the equivalent opportunity measure, actual characteristic identities, nonempty adjustment argmins and both the existence and the universality of the adjustment selection. At each restart time the initial portfolio is explicitly fully invested; after that time it agrees with the displayed strategy of (1)(e).
--
--   The tracking value is the càdlàg semimartingale version of
--   $$V_t=L_t^{-1}E[\mathcal E((-1_{(t,T]}a)\mathbin\bullet S)_T H\mid\mathcal F_t].$$
--   The hedge predicate includes all predictable adjustment and pure-hedge selections, the feedback identity, optimality over the full admissible class, and the conditional residual-error formula. It also provides a common clock dominating all characteristics involved with this payoff: an earlier clock dominating only $S,L$ is not presumed to dominate every possible $V(H)$. The final predicate contains the forward assertion and the converse without a positive-deflator assumption. These predicates are interfaces; no existence or uniqueness fact is built into a hypothesis of the two theorem items.
--
--   Both integrations in the residual error use extended nonnegative integration, and the common-clock witness explicitly preserves the original adjustment selection.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 14–15, Theorem 4.1, (4.1)–(4.11); pp. 35–36, (D.8)–(D.11)

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Numeraire
import Definitions.Def_NumInvQH_Oblique_Basic

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace NumInvQH.Oblique.Supplement

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def rho {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (L : Process Ω ℝ) : Process Ω ℝ :=
  let B := compensator P ℱ T (stochasticLog P ℱ T L)
  fun t ω => 1 + B t ω - left B t ω

noncomputable def opportunityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (L : Process Ω ℝ) : Measure Ω :=
  let E := exponential P ℱ T (compensator P ℱ T (stochasticLog P ℱ T L))
  P.withDensity (fun ω => ENNReal.ofReal (L T ω / ((∫ w, L 0 w ∂P) * E T ω)))

noncomputable def normalizedVector {Ω : Type*} {d : ℕ}
    (r : Process Ω ℝ) (b : Process Ω (Fin d → ℝ)) : Process Ω (Fin d → ℝ) :=
  fun t ω i => b t ω i / r t ω

noncomputable def normalizedMatrix {Ω : Type*} {d : ℕ}
    (r : Process Ω ℝ) (C : Process Ω (Matrix (Fin d) (Fin d) ℝ)) :
    Process Ω (Matrix (Fin d) (Fin d) ℝ) := fun t ω i j => C t ω i j / r t ω

/-- A predictable selection of a genuine quadratic argmin, with the investment
constraint at all times (and the objective optimality in the characteristic-rate sense). -/
def Selection {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (A : Clock P ℱ T) (S : Process Ω (Fin d → ℝ))
    (C : Process Ω (Matrix (Fin d) (Fin d) ℝ)) (b : Process Ω (Fin d → ℝ))
    (c : Process Ω ℝ) (a : Process Ω (Fin d → ℝ)) : Prop :=
  IsStronglyPredictable ℱ (stop T a) ∧ Same P T (fun t ω => a t ω ⬝ᵥ left S t ω) c ∧
    RateAE A (fun t ω => a t ω ∈ NumInvQH.Oblique.hyperArgmin (C t ω) (b t ω) (left S t ω) (c t ω))

/-- The restart strategy uses the displayed integrand after τ, and at τ is
fully invested. This explicit endpoint repairs the zero-wealth endpoint in (1)(e). -/
noncomputable def restartAdjustment {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S a : Process Ω (Fin d → ℝ)) (τ : BoundedStop ℱ T) : Process Ω (Fin d → ℝ) :=
  let E := exponential P ℱ T (integral P ℱ T (after τ.time (-a)) S)
  fun t ω => if t = τ.time ω then
      ((S t ω ⬝ᵥ S t ω)⁻¹) • S t ω
    else if τ.time ω < t then -(left E t ω) • a t ω else 0

def AdjustmentProperty {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (A : Clock P ℱ T) (S : Process Ω (Fin d → ℝ)) (L ℓ : Process Ω ℝ)
    (C : Process Ω (Matrix (Fin d) (Fin d) ℝ)) (b a : Process Ω (Fin d → ℝ)) : Prop :=
  RateAE A (fun t ω => ℓ t ω / rho P ℱ T L t ω =
    -NumInvQH.Oblique.quadraticForm (C t ω) (b t ω) (a t ω)) ∧
  ∀ τ : BoundedStop ℱ T,
    AdmissibleFrom P ℱ T S (restartAdjustment P ℱ T S a τ) τ ∧
    (∀ᵐ ω ∂P, wealth (restartAdjustment P ℱ T S a τ) S (τ.time ω) ω = 1)

/-- Parts (1)(c)–(e), with the raw weighted rates written by the equivalent
compensator formulas (D.8)–(D.9); b/ρ and C/ρ are (4.1)–(4.2). -/
def CharacterData {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (S : Process Ω (Fin d → ℝ)) (L : Process Ω ℝ) (A : Clock P ℱ T)
    (b : Process Ω (Fin d → ℝ)) (C : Process Ω (Matrix (Fin d) (Fin d) ℝ))
    (ℓ : Process Ω ℝ) : Prop :=
  WeightedRates A S L 0 b C 0 0 ∧ DriftRate A (stochasticLog P ℱ T L) ℓ ∧
  let Q := opportunityMeasure P ℱ T L
  let r := rho P ℱ T L
  let bs := normalizedVector r b
  let Cs := normalizedMatrix r C
  IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧ LocallySquareIntegrable Q ℱ T S ∧
  (∀ᵐ ω ∂P, (∀ i, IntegrableOn (fun t => bs t ω i) (Set.Ioc 0 T) (A.measure ω)) ∧
    (∀ i j, IntegrableOn (fun t => Cs t ω i j) (Set.Ioc 0 T) (A.measure ω))) ∧
  (∀ i, Special Q ℱ T (fun t ω => S t ω i) ∧
    Same P T (compensator Q ℱ T (fun t ω => S t ω i)) (clockIntegral A (fun t ω => bs t ω i))) ∧
  (∀ i j, Same P T
    (compensator Q ℱ T (covariation Q ℱ T (fun t ω => S t ω i) (fun t ω => S t ω j)))
    (clockIntegral A (fun t ω => Cs t ω i j))) ∧
  RateAE A (fun t ω => (NumInvQH.Oblique.hyperArgmin (Cs t ω) (bs t ω) (left S t ω) (-1)).Nonempty) ∧
  (∃ a, Selection A S Cs bs (fun _ _ => -1) a ∧ AdjustmentProperty A S L ℓ Cs bs a) ∧
  (∀ a, Selection A S Cs bs (fun _ _ => -1) a → AdjustmentProperty A S L ℓ Cs bs a)

/-- All of Theorem 4.1(1)(a)–(e), including boundedness, existence of a selection,
and both the some/any versions of (e). -/
def Character {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S : Process Ω (Fin d → ℝ)) (L : Process Ω ℝ) : Prop :=
  ScalarSemi P ℱ T L ∧ (∃ K : ℝ, ∀ᵐ ω ∂P, ∀ t ≤ T, |L t ω| ≤ K) ∧
  Positive P T L ∧ (∀ᵐ ω ∂P, L T ω = 1) ∧
  (let E := exponential P ℱ T (compensator P ℱ T (stochasticLog P ℱ T L));
    (∀ᵐ ω ∂P, ∀ t ≤ T, 0 < L t ω / E t ω) ∧
    Martingale (stop T (fun t ω => L t ω / E t ω)) ℱ P) ∧
  ∃ A : Clock P ℱ T, ∃ b C ℓ, CharacterData S L A b C ℓ

/-- Formula (4.6), computed from the data, not an arbitrary tracking process. -/
def MeanValueFormula {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S a : Process Ω (Fin d → ℝ)) (L : Process Ω ℝ) (H : Ω → ℝ)
    (V : Process Ω ℝ) : Prop :=
  ∀ t ≤ T, ∀ᵐ ω ∂P, V t ω = P[fun w => exponential P ℱ T
    (integral P ℱ T (after (fun _ => t) (-a)) S) T w * H w | ℱ t] ω / L t ω

/-- The cadlag semimartingale version of (4.6), rather than unrelated choices at each time. -/
noncomputable def meanValue {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S a : Process Ω (Fin d → ℝ)) (L : Process Ω ℝ) (H : Ω → ℝ) : Process Ω ℝ :=
  if h : ∃ V, ScalarSemi P ℱ T V ∧ MeanValueFormula P ℱ T S a L H V
    then Classical.choose h else 0

/-- Formula (4.9). The nonnegative conditional expectation has no nonintegrable-zero convention. -/
noncomputable def residualError {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (A : Clock P ℱ T) (L : Process Ω ℝ)
    (C : Process Ω (Matrix (Fin d) (Fin d) ℝ))
    (u ξ : Process Ω (Fin d → ℝ)) (γ : Process Ω ℝ) : Process Ω ℝ≥0∞ :=
  fun t => condLExp (ℱ t) P (fun ω =>
    ∫⁻ s in Set.Ioc t T, ENNReal.ofReal (L s ω *
      (γ s ω - 2 * (ξ s ω ⬝ᵥ u s ω) + ξ s ω ⬝ᵥ (C s ω *ᵥ ξ s ω))) ∂A.measure ω)

/-- Parts (2)–(3) in full, for every choice of the two predictable selections. -/
def Hedging {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S : Process Ω (Fin d → ℝ)) (L : Process Ω ℝ) : Prop :=
  ∀ (A : Clock P ℱ T) b C ℓ, CharacterData S L A b C ℓ →
    let r := rho P ℱ T L
    let bs := normalizedVector r b
    let Cs := normalizedMatrix r C
    ∀ a, Selection A S Cs bs (fun _ _ => -1) a →
    ∀ (v : ℝ) (H : Ω → ℝ), MemLp H 2 P →
      let V := meanValue P ℱ T S a L H
      ScalarSemi P ℱ T V ∧ MeanValueFormula P ℱ T S a L H V ∧
      (∀ t ≤ T, Integrable (fun ω => exponential P ℱ T
        (integral P ℱ T (after (fun _ => t) (-a)) S) T ω * H ω) P) ∧
      (∃ A' : Clock P ℱ T, ∃ b' C' ℓ' u γ,
        CharacterData S L A' b' C' ℓ' ∧
        Selection A' S (normalizedMatrix r C') (normalizedVector r b') (fun _ _ => -1) a ∧
        WeightedRates A' S L V b' C' u γ) ∧
      ∀ u γ, WeightedRates A S L V b C u γ →
        let us := normalizedVector r u
        let γs := fun t ω => γ t ω / r t ω
        (∃ ξ, Selection A S Cs us (left V) ξ) ∧
        ∀ ξ, Selection A S Cs us (left V) ξ →
          (∀ᵐ ω ∂P, ∀ t ≤ T, residualError A L Cs us ξ γs t ω < ⊤) ∧
          ∃ φ, Optimal P ℱ T S φ v H ∧
            Same P T φ (fun t ω => ξ t ω + (left V t ω - φ t ω ⬝ᵥ left S t ω) • a t ω) ∧
            (∀ᵐ ω ∂P, loss P T S φ H = ENNReal.ofReal
              (L 0 ω * (v - V 0 ω)^2) + residualError A L Cs us ξ γs 0 ω)

/-- The forward assertion and the converse without a deflator assumption. -/
def QuadraticHedgingTheorem {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S : Process Ω (Fin d → ℝ)) : Prop :=
  ((∃ Z, Deflator P ℱ T S Z ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, 0 < Z t ω) →
    ∃ L, Opportunity P ℱ T S L ∧ Character P ℱ T S L ∧ Hedging P ℱ T S L ∧
      ∀ L', Character P ℱ T S L' → Same P T L' L) ∧
  (∀ L, Character P ℱ T S L → Opportunity P ℱ T S L ∧ Hedging P ℱ T S L)

end NumInvQH.Oblique.Supplement


