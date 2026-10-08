-- Prove2me | Definitions.Def_DilutedSpin
-- name    : DilutedSpin
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.634019+00:00
-- url     : https://prove2.me/theorems/fc055443-7d99-494c-8d5a-e455a3cea613
-- statement:
--   A diluted spin model of arity p consists of a nonnegative interaction density α, a probability law for samples (θ,a,b,f₀,…,fₚ₋₁), where θ assigns a real energy to each p-tuple of spins ±1 and each fₗ is a real function of one spin, and a real external-field law. Admissibility requires even p≥2, α>0, integrability of maxₛ|θ(s)| and |h|, and almost surely a>0 with exp(θ(s))=a(1+b∏ₗfₗ(sₗ)) and |b∏ₗfₗ(sₗ)|<1 for every spin tuple. The fₗ are independent and identically distributed, b is independent of their joint family, and every positive-integer moment E[(-b)ⁿ] exists and is nonnegative. For N≥1, the pressure F_N is N⁻¹ times the expected logarithm of the partition sum over all N-spin configurations, with log weight ∑ⱼθⱼ(σᵢⱼ₀,…,σᵢⱼ₍ₚ₋₁₎)+∑ᵢhᵢσᵢ: the interaction count is Poisson(αN), samples and fields have independent product laws, and all interaction labels are independently uniform among the N sites, allowing repetitions. Set qₓ(s)=exp(xs)/(2 cosh x). The edge factor is E[exp(θ(s))] under independent spins with laws qₓₗ. A cavity message at distinguished last spin ε is the logarithm of the corresponding average of exp(θ(s,ε)) over the other p−1 spins; the site logarithm is log((∑ε exp(hε+∑ⱼmessageⱼ(ε)))/2). Nested law spaces satisfy H₀=ℝ and Hⱼ₊₁=P(Hⱼ), with weak topologies and their Borel sigma-fields. For a finite family of message labels, define L₀(g,x)=g(x), and recursively Lᵣ₊₁(g,m,η)=m₀⁻¹ log E[exp(m₀Lᵣ(g,(m₁,…),X))], where the coordinates Xᵢ independently have laws ηᵢ. The trial logarithm Tᵣ(g;ζ,m) further averages Lᵣ over independent root laws ηᵢ drawn from ζ∈Hᵣ₊₁; at r=0 this is ordinary averaging over independent real messages. Admissible exponents obey 0<m₀<⋯<mᵣ₋₁<1, vacuously at depth zero. The cavity functional Bᵣ is log 2 plus the physical-disorder expectation of Tᵣ applied to the site logarithm, using Poisson(αp) incident interactions, minus α(p−1) times the disorder expectation of Tᵣ applied to the log edge factor. Physical disorder remains fixed during the nested message averages. Finally φᵣ is the infimum of Bᵣ over ζ and admissible exponents, and the variational value is infᵣ≥₀φᵣ; these are definitions, with no equality to a pressure limit asserted here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DilutedSpin.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DilutedSpin.lean; bytes 16..6529
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace DilutedSpinGlass

abbrev Spin := Bool

def spin (s : Spin) : ℝ := if s then 1 else -1

abbrev Interaction (p : ℕ) := (Fin p → Spin) → ℝ

/-- One interaction together with its factorization witness: theta,a,b,f. -/
abbrev InteractionSample (p : ℕ) :=
  Interaction p × ℝ × ℝ × (Fin p → Spin → ℝ)

structure Model (p : ℕ) where
  alpha : ℝ≥0
  disorder : ProbabilityMeasure (InteractionSample p)
  field : ProbabilityMeasure ℝ

/-- Exactly the standing hypotheses (model:integrability through positivity).
`norm` on the finite function space is max_s |theta(s)|. -/
structure Admissible {p : ℕ} (M : Model p) : Prop where
  arity : 2 ≤ p
  even : Even p
  density : 0 < M.alpha
  interaction_integrable : Integrable (fun z : InteractionSample p => ‖z.1‖)
    M.disorder.toMeasure
  field_integrable : Integrable (fun h : ℝ => |h|) M.field.toMeasure
  factorization : ∀ᵐ z ∂M.disorder.toMeasure,
    0 < z.2.1 ∧ ∀ s : Fin p → Spin,
      Real.exp (z.1 s) = z.2.1 * (1 + z.2.2.1 * ∏ l, z.2.2.2 l (s l)) ∧
      |z.2.2.1 * ∏ l, z.2.2.2 l (s l)| < 1
  independent_f : iIndepFun (fun l (z : InteractionSample p) => z.2.2.2 l)
    M.disorder.toMeasure
  identically_distributed_f : ∀ l j : Fin p,
    IdentDistrib (fun z : InteractionSample p => z.2.2.2 l)
      (fun z : InteractionSample p => z.2.2.2 j)
      M.disorder.toMeasure M.disorder.toMeasure
  independent_b : IndepFun (fun z : InteractionSample p => z.2.2.1)
    (fun z : InteractionSample p => z.2.2.2) M.disorder.toMeasure
  finite_b_moments : ∀ n : ℕ, 1 ≤ n →
    Integrable (fun z : InteractionSample p => (-z.2.2.1) ^ n) M.disorder.toMeasure
  positivity : ∀ n : ℕ, 1 ≤ n →
    0 ≤ ∫ z : InteractionSample p, (-z.2.2.1) ^ n ∂M.disorder.toMeasure

/-- Minus the Hamiltonian, with all index choices including repetitions. -/
noncomputable def logWeight {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin) : ℝ :=
  (∑ j, (theta j).1 (fun l => σ (indices j l))) + ∑ i, h i * spin (σ i)

noncomputable def logPartition {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) : ℝ :=
  Real.log (∑ σ : Fin N → Spin, Real.exp (logWeight theta h indices σ))

/-- F_N, using an explicit uniform average over the independent index labels.
The value at N=0 is irrelevant to the limit; valid system sizes are N>=1. -/
noncomputable def pressure {p : ℕ} (M : Model p) (N : ℕ) : ℝ :=
  (∫ k : ℕ,
    ∫ theta : Fin k → InteractionSample p,
      ∫ h : Fin N → ℝ,
        ((∑ indices : Fin k → Fin p → Fin N, logPartition theta h indices) /
          (Fintype.card (Fin k → Fin p → Fin N) : ℝ))
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)
  ∂poissonMeasure (M.alpha * N)) / N

noncomputable def q (x : ℝ) (s : Spin) : ℝ :=
  Real.exp (x * spin s) / (2 * Real.cosh x)

noncomputable def edge {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) : ℝ :=
  ∑ s : Fin p → Spin, Real.exp (theta s) * ∏ l, q (x l) (s l)

/-- Append the distinguished cavity spin in the last position. -/
def appendSpin {p : ℕ} (s : Fin (p - 1) → Spin) (ε : Spin) (l : Fin p) : Spin :=
  if h : l.val < p - 1 then s ⟨l.val, h⟩ else ε

noncomputable def message {p : ℕ} (theta : Interaction p)
    (x : Fin (p - 1) → ℝ) (ε : Spin) : ℝ :=
  Real.log (∑ s : Fin (p - 1) → Spin,
    Real.exp (theta (appendSpin s ε)) * ∏ l, q (x l) (s l))

noncomputable def siteLog {p k : ℕ} (theta : Fin k → InteractionSample p)
    (h : ℝ) (x : (Fin k × Fin (p - 1)) → ℝ) : ℝ :=
  Real.log ((∑ ε : Spin, Real.exp
    (h * spin ε + ∑ j, message (theta j).1 (fun l => x (j, l)) ε)) / 2)

/-- Use literally the Borel sigma-field of the weak topology at each level,
as stipulated in model.tex. -/
local instance instMeasurableSpaceCarrier_challenge (X : TopCat) : MeasurableSpace X := borel X
local instance instBorelSpaceCarrier_challenge (X : TopCat) : BorelSpace X := ⟨rfl⟩

/-- Nested probability laws: H_0=R and H_{j+1}=P(H_j), with weak topologies. -/
noncomputable def Hierarchy : ℕ → TopCat
  | 0 => TopCat.of ℝ
  | r + 1 => TopCat.of (ProbabilityMeasure (Hierarchy r))

/-- Logarithmic form of the conditional power means T_0 using independent
message labels. The current eta's are held fixed; only their descendants
are integrated. Physical disorder is a fixed argument of g throughout. -/
noncomputable def logMean {ι : Type} [Fintype ι] :
    (r : ℕ) → ((ι → ℝ) → ℝ) → (Fin r → ℝ) → (ι → Hierarchy r) → ℝ
  | 0, g, _, x => g x
  | r + 1, g, m, eta =>
    Real.log (∫ x : ι → Hierarchy r,
      Real.exp (m 0 * logMean r g (fun i => m i.succ) x)
      ∂Measure.pi (fun i => (eta i).toMeasure)) / m 0

/-- Expectation over the root laws eta_0 of each independent message label.
This also gives the r=0 convention (iid real messages, no power means). -/
noncomputable def trialLog {ι : Type} [Fintype ι] (r : ℕ)
    (ζ : Hierarchy (r + 1)) (m : Fin r → ℝ) (g : (ι → ℝ) → ℝ) : ℝ :=
  ∫ eta : ι → Hierarchy r, logMean r g m eta
    ∂Measure.pi (fun _ : ι => ζ.toMeasure)

/-- Admissible exponents 0<m_1<...<m_r<1; vacuous at r=0. -/
def Exponents {r : ℕ} (m : Fin r → ℝ) : Prop :=
  StrictMono m ∧ ∀ i, 0 < m i ∧ m i < 1

/-- The exact finite-depth cavity functional B_r. -/
noncomputable def functional {p : ℕ} (M : Model p) (r : ℕ)
    (ζ : Hierarchy (r + 1)) (m : Fin r → ℝ) : ℝ :=
  Real.log 2 +
    (∫ k : ℕ,
      ∫ theta : Fin k → InteractionSample p,
        ∫ h : ℝ, trialLog r ζ m (siteLog theta h) ∂M.field.toMeasure
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)
    ∂poissonMeasure (M.alpha * p)) -
    (M.alpha : ℝ) * (p - 1 : ℕ) *
      (∫ theta : InteractionSample p,
        trialLog r ζ m (fun x => Real.log (edge theta.1 x)) ∂M.disorder.toMeasure)

noncomputable def phi {p : ℕ} (M : Model p) (r : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ (ζ : Hierarchy (r + 1)) (m : Fin r → ℝ),
    Exponents m ∧ v = functional M r ζ m}

noncomputable def variationalValue {p : ℕ} (M : Model p) : ℝ :=
  ⨅ r : ℕ, phi M r



end DilutedSpinGlass
end OAI


