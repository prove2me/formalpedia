-- Prove2me | Definitions.Def_NumInvQH_Oblique_Supplement_Characteristics
-- name    : NumInvQH_Oblique_Supplement_Characteristics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:38:10.745783+00:00
-- url     : https://prove2.me/theorems/62c87552-f4f6-4c19-8f75-2b1570eb55b9
-- title:
--   Canonical compensators, common clocks and differential characteristics
-- statement:
--   A special semimartingale has the canonical decomposition $X=X_0+M+B$, where $M$ is a zero-initial càdlàg local martingale and $B$ is predictable, càdlàg, starts at zero and has finite variation. Local square integrability means that the quadratic covariations of the market coordinates are special.
--
--   A common clock $A$ is increasing, predictable and integrable, with its genuine pathwise Stieltjes measures. Differential characteristics $(b,c,F,A)$ use the paper's standing convention $h(x)=x$: $b\mathbin\bullet A=B$, $c\mathbin\bullet A$ is the continuous martingale bracket, and $F\mathbin\bullet A$ is the compensator of the actual jump measure. Continuous and purely discontinuous martingales and the jump compensation tests are explicit predicates.
--
--   The weighted rates in Appendix D are represented by the equivalent canonical-compensator identities
--   $$\bar b^S\mathbin\bullet A=B^{S+[S,\mathcal L(L)]},\qquad \bar c^{SV}\mathbin\bullet A=B^{[S,V]+[[S,V],\mathcal L(L)]}.$$
--   The analogous identities define $\bar c^S,\bar c^V$. These are precisely (D.8)–(D.9), and retain general clocks and jumps. Rate equalities mean $P(d\omega)dA_t(\omega)$-almost everywhere. All drift integrals require actual pathwise integrability.
--
--   WeightedRates includes LogDefined for the logarithm appearing in the source rates. Thus the source requirement that these rates be well-defined cannot be met by an outside-domain zero default.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 5–6, Definition 2.1 and standing h(x)=x convention; pp. 35–36, (D.8)–(D.11)

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Market

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace NumInvQH.Oblique.Supplement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Canonical decomposition of a special semimartingale; the finite-variation part
is predictable and starts at zero. -/
def SpecialDecomposition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X M B : Process Ω ℝ) : Prop :=
  EthierKurtz.IsSourceLocalMartingale P ℱ (stop T M) ∧
  (∀ ω, KurtzProtter91.Integrals.IsCadlag (fun t => stop T M t ω)) ∧
  IsStronglyPredictable ℱ (stop T B) ∧
  (∀ ω, KurtzProtter91.Integrals.IsCadlag (fun t => stop T B t ω)) ∧
  (∀ᵐ ω ∂P, eVariationOn (fun t => B t ω) (Set.Icc 0 T) ≠ ⊤) ∧
  (∀ᵐ ω ∂P, M 0 ω = 0 ∧ B 0 ω = 0) ∧
  Same P T X (fun t ω => X 0 ω + M t ω + B t ω)

def Special {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : Process Ω ℝ) : Prop := ∃ M B, SpecialDecomposition P ℱ T X M B

noncomputable def compensator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : Process Ω ℝ) : Process Ω ℝ :=
  if h : ∃ B, ∃ M, SpecialDecomposition P ℱ T X M B then Classical.choose h else 0

/-- The paper's definition of local square integrability: the quadratic covariations are special. -/
def LocallySquareIntegrable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S : Process Ω (Fin d → ℝ)) : Prop :=
  Semi P ℱ T S ∧ ∀ i j, Special P ℱ T
    (covariation P ℱ T (fun t ω => S t ω i) (fun t ω => S t ω j))

/-- One common increasing predictable integrable clock and its pathwise Stieltjes measures.
The interval equations determine the measures; this does not assume a characteristic identity. -/
structure Clock {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0) where
  value : Process Ω ℝ
  measure : Ω → Measure ℝ≥0
  increasing : ∀ ω, Monotone (fun t => value t ω)
  cadlag : ∀ ω, KurtzProtter91.Integrals.IsCadlag (fun t => value t ω)
  predictable : IsStronglyPredictable ℱ value
  zero : ∀ ω, value 0 ω = 0
  integrable : Integrable (value T) P
  no_zero_atom : ∀ ω, measure ω {0} = 0
  interval : ∀ ω s t, s ≤ t → measure ω (Set.Ioc s t) = ENNReal.ofReal (value t ω - value s ω)

noncomputable def clockIntegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (A : Clock P ℱ T) (f : Process Ω ℝ) : Process Ω ℝ :=
  fun t ω => ∫ u in Set.Ioc 0 t, f u ω ∂A.measure ω

/-- Differential drift with respect to the common clock, i.e. B^X = b^X • A. -/
def DriftRate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (A : Clock P ℱ T) (X b : Process Ω ℝ) : Prop :=
  Special P ℱ T X ∧ IsStronglyPredictable ℱ b ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun t => b t ω) (Set.Ioc 0 T) (A.measure ω)) ∧
  Same P T (compensator P ℱ T X) (clockIntegral A b)

def RateAE {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (A : Clock P ℱ T) (p : ℝ≥0 → Ω → Prop) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ t ∂A.measure ω, t ≤ T → p t ω

/-- The tilted drift/covariation rates of Appendix D, using exactly the
compensator identities (D.8)–(D.9). This retains arbitrary clocks and jumps. -/
def WeightedRates {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (A : Clock P ℱ T) (S : Process Ω (Fin d → ℝ)) (L V : Process Ω ℝ)
    (b : Process Ω (Fin d → ℝ))
    (C : Process Ω (Matrix (Fin d) (Fin d) ℝ)) (u : Process Ω (Fin d → ℝ))
    (γ : Process Ω ℝ) : Prop :=
  LogDefined P ℱ T L ∧
  (∀ i, DriftRate A
    (fun t ω => S t ω i + covariation P ℱ T (fun t ω => S t ω i) (stochasticLog P ℱ T L) t ω)
    (fun t ω => b t ω i)) ∧
  (∀ i j, let Q := covariation P ℱ T (fun t ω => S t ω i) (fun t ω => S t ω j);
    DriftRate A (fun t ω => Q t ω + covariation P ℱ T Q (stochasticLog P ℱ T L) t ω)
      (fun t ω => C t ω i j)) ∧
  (∀ i, let Q := covariation P ℱ T (fun t ω => S t ω i) V;
    DriftRate A (fun t ω => Q t ω + covariation P ℱ T Q (stochasticLog P ℱ T L) t ω)
      (fun t ω => u t ω i)) ∧
  (let Q := covariation P ℱ T V V;
    DriftRate A (fun t ω => Q t ω + covariation P ℱ T Q (stochasticLog P ℱ T L) t ω) γ)

/-- Continuous local martingales starting at zero. -/
def ContinuousLocal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Process Ω ℝ) : Prop :=
  EthierKurtz.IsSourceLocalMartingale P ℱ (stop T M) ∧
  (∀ ω, Continuous (fun t => stop T M t ω)) ∧ (∀ᵐ ω ∂P, M 0 ω = 0)

/-- Pure discontinuity by strong orthogonality to every continuous local martingale. -/
def PureDiscontinuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Process Ω ℝ) : Prop :=
  ScalarSemi P ℱ T M ∧ EthierKurtz.IsSourceLocalMartingale P ℱ (stop T M) ∧
  (∀ᵐ ω ∂P, M 0 ω = 0) ∧ ∀ N, ContinuousLocal P ℱ T N →
    EthierKurtz.IsSourceLocalMartingale P ℱ (stop T (fun t ω => M t ω * N t ω))

/-- Differential characteristics (b,c,F,A), with the paper's standing truncation h(x)=x.
The drift is the canonical predictable FV part, c • A is the continuous bracket,
and F • A is the compensator of the actual jump measure. -/
def DifferentialCharacteristics {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (A : Clock P ℱ T) (S b : Process Ω (Fin d → ℝ))
    (c : Process Ω (Matrix (Fin d) (Fin d) ℝ))
    (F : ℝ≥0 → Ω → Measure (Fin d → ℝ)) : Prop :=
  Semi P ℱ T S ∧
  (∀ i, DriftRate A (fun t ω => S t ω i) (fun t ω => b t ω i)) ∧
  (∀ i j, IsStronglyPredictable ℱ (fun t ω => c t ω i j)) ∧
  (∀ t ω, (c t ω).PosSemidef) ∧
  (∀ G : Set (Fin d → ℝ), MeasurableSet G →
    Measurable[ℱ.predictable] (fun z : ℝ≥0 × Ω => F z.1 z.2 G)) ∧
  (∀ t ω, F t ω {0} = 0) ∧
  (∀ t ω, ∫⁻ x, ENNReal.ofReal (min (x ⬝ᵥ x) 1) ∂F t ω < ⊤) ∧
  (∀ᵐ ω ∂P, (∀ i j, IntegrableOn (fun t => c t ω i j) (Set.Ioc 0 T) (A.measure ω)) ∧
    ∫⁻ t in Set.Ioc 0 T, ∫⁻ x, ENNReal.ofReal (min (x ⬝ᵥ x) 1) ∂F t ω ∂A.measure ω < ⊤) ∧
  (∃ Mc : Process Ω (Fin d → ℝ),
    (∀ i, ContinuousLocal P ℱ T (fun t ω => Mc t ω i)) ∧
    (∀ i, PureDiscontinuous P ℱ T (fun t ω => S t ω i - S 0 ω i -
      clockIntegral A (fun t ω => b t ω i) t ω - Mc t ω i)) ∧
    ∀ i j, HasCovariation P ℱ T (fun t ω => Mc t ω i) (fun t ω => Mc t ω j)
      (clockIntegral A (fun t ω => c t ω i j))) ∧
  (∀ g : (Fin d → ℝ) → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
    (∃ K, ∀ x, g x ≤ K) → (∀ᶠ x in 𝓝 0, g x = 0) →
    (∀ᵐ ω ∂P, IntegrableOn (fun t => ∫ x, g x ∂F t ω) (Set.Ioc 0 T) (A.measure ω)) ∧
    EthierKurtz.IsSourceLocalMartingale P ℱ (stop T (fun t ω =>
      (∑' u : Set.Ioc 0 t, g (S u ω - left S u ω)) -
        clockIntegral A (fun t ω => ∫ x, g x ∂F t ω) t ω)))

end NumInvQH.Oblique.Supplement


