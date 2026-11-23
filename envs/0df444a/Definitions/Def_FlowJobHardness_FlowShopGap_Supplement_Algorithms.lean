-- Prove2me | Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Algorithms
-- name    : FlowJobHardness_FlowShopGap_Supplement_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:26:19.922896+00:00
-- url     : https://prove2.me/theorems/bbf57d24-d900-4802-9c69-d2351d20bb91
-- title:
--   Approximation schemes, genuine promise reductions and time classes
-- statement:
--   On binary rational shop inputs, a polynomial-time approximation algorithm is a map on finite bit strings implemented by a bounded Cook Turing machine. It returns an encoded feasible schedule whose objective $V$ satisfies
--   $$V\le\rho V'\quad\hbox{for every feasible real-time comparison schedule of value }V'.$$
--   This expresses approximation to the optimum without a default-valued infimum. The two objectives are makespan and the unweighted sum of completion times. For logarithmic approximation the positive multiplier $C$ and positive lower-bound threshold $T$ are arbitrary, with the bound required when $\mathrm{lb}\ge T$; feasible output is required on every input. The logarithm there is totalized as $\log_2(\max\{2,\mathrm{lb}\})$.
--
--   A PTAS is one computable scheme, with a polynomial-time specialization for each fixed positive rational error; its degree can depend on that error. Inputs have no bound on operations per job. Preemptive output is judged against the full real-time preemptive model, not an integer-time optimum.
--
--   NP and polynomial maps are the published Cook definitions. Promise hardness is the published universal many-one definition. In the half-jobs promise, NO excludes YES explicitly, preventing their empty-instance overlap from trivializing hardness. For sufficiently large $K$, the paper's nonempty hard instances already have disjoint cases. The exact gap is $2K\,\mathrm{lb}$ versus $K^{(\log_2 K)/25}\mathrm{lb}/8$; the bound on chain length depends on $K$ alone. Ordinary constant-factor hardness compares optimum at most $b$ with every schedule strictly exceeding $cb$, for a positive rational threshold $b$ in the input.
--
--   Deterministic time is bounded execution of an actual Cook machine. Zero-error time uses the published finite-transition multi-tape fair-coin machine: every halting branch must output the correct membership bit, and its extended-nonnegative expected halting time must satisfy a finite bound. Quasi-polynomial time is the union of $c(n+2)^{a\log_2(n+2)}$ over positive constants. For exponent $p$, zero-error time is the union of $c2^{(\log_2(n+2))^p}$. In the logarithmic theorems $p=A/\min\{\epsilon,1\}$ with one $A>0$ outside $\epsilon$, the objectives and languages. These are computational classes, not oracle assumptions or propositions standing for the desired hardness.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, p. 20:2, footnote 1; pp. 20:5–20:7, Theorems 1.2–1.6; p. 20:14, proof of Theorem 1.3

import Mathlib
import Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Encoding
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_MeanBudgetXC_Supplement_PromiseNPHard
import Definitions.Def_IntQuotHNP_Supplement_LasVegas
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

open JobShopLTAS.Core

/-- Full general job shops, or a fixed machine count; no bound on job chains. -/
def jobDomain (machines : Option ℕ) (S : RationalShop) : Prop :=
  match machines with
  | none => True
  | some m => S.m = m

def flowDomain (S : RationalShop) : Prop := IsGeneralizedFlowShop S.data

/-- The output is an encoded feasible schedule. Its objective is compared with
EVERY feasible real-time schedule, so no attainment or real sInf convention is
assumed. Q is a relation between the returned and comparison objective values. -/
def OutputSpec (S : RationalShop) (o : Objective) (pmtn : Bool)
    (w : List Bool) (Q : ℝ → ℝ → Prop) : Prop :=
  match pmtn with
  | false => ∃ s : S.data.Op → ℚ, w = startCode S s ∧
      S.data.IsFeasibleSchedule Finset.univ (fun k => (s k : ℝ)) ∧
      ∀ t : S.data.Op → ℝ, S.data.IsFeasibleSchedule Finset.univ t →
        Q (value S.data o (fun k => (s k : ℝ))) (value S.data o t)
  | true => ∃ s : PieceSchedule S.data, w = pieceCode S s ∧ s.execution.Feasible ∧
      ∀ t : PreemptiveExecution S.data, t.Feasible →
        Q (preemptiveValue o s.execution) (preemptiveValue o t)

/-- Polynomial time is actual Cook-machine time on the entire binary input,
including machine indices, job chains, rational numerators and denominators. -/
def HasApprox (D : RationalShop → Prop) (o : Objective) (pmtn : Bool) (ρ : ℝ) : Prop :=
  ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
    ∀ S, D S → OutputSpec S o pmtn (f (shopCode S)) (fun v v' => v ≤ ρ * v')

/-- Base-two logarithm, fixed explicitly for the exact exponent in Theorem 1.2. -/
noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Only the logarithmic approximation notation is totalized at lb ≤ 1.
Its positive multiplier and eventual threshold are independently quantified. -/
def HasLogApprox (D : RationalShop → Prop) (o : Objective) (ε : ℝ) : Prop :=
  ∃ (C T : ℝ) (f : List Bool → List Bool), 0 < C ∧ 0 < T ∧
    CookPvsNP.PolyTimeComputable f ∧ ∀ S, D S →
      OutputSpec S o false (f (shopCode S)) (fun v v' =>
        T ≤ lowerBound S.data →
          v ≤ C * (logTwo (max 2 (lowerBound S.data))) ^ (1 - ε) * v')

/-- Computability on all finite bit strings, with no uniform time restriction. -/
def TMComputable (f : List Bool → List Bool) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ) (ι : Bool ↪ Γ) (M : CookPvsNP.TM Γ),
    ∀ x, ∃ t, M.HaltsWithin t (x.map ι) ∧
      M.output (M.run t (M.init (x.map ι))) = (f x).map (some ∘ ι)

/-- A single uniform scheme accepts a rational error and input word. For each
fixed positive error its specialization has polynomial time; the degree may
depend on the error. No polynomial dependence on inverse error is required. -/
def HasPTAS (D : RationalShop → Prop) (pmtn : Bool) : Prop :=
  ∃ F : List Bool → List Bool, TMComputable F ∧
    ∀ ε : ℚ, 0 < ε →
      CookPvsNP.PolyTimeComputable (fun x => F (ratCode ε ++ x)) ∧
      ∀ S, D S → OutputSpec S .makespan pmtn (F (ratCode ε ++ shopCode S))
        (fun v v' => v ≤ (1 + (ε : ℝ)) * v')

/-- Exact YES and NO languages of Theorem 1.2. The bound B on each chain is
outside the instance and will be existentially quantified after K alone. -/
def halfGapYes (K B : ℕ) : Set (List Bool) :=
  {w | ∃ S : RationalShop, w = shopCode S ∧ flowDomain S ∧
    (∀ j, S.data.μ j ≤ B) ∧ ∃ s : S.data.Op → ℝ,
      S.data.IsFeasibleSchedule Finset.univ s ∧
      S.data.makespan Finset.univ s ≤ 2 * (K : ℝ) * lowerBound S.data}

/-- Exclude YES from NO to make the promise disjoint, including at empty
instances. Otherwise a constant map to the empty shop would fake NP-hardness.
For sufficiently large K the source soundness instances are already outside YES. -/
noncomputable def halfGapNo (K B : ℕ) : Set (List Bool) :=
  {w | w ∉ halfGapYes K B ∧ ∃ S : RationalShop, w = shopCode S ∧ flowDomain S ∧
    (∀ j, S.data.μ j ≤ B) ∧ ∀ s : S.data.Op → ℝ,
      S.data.IsFeasibleSchedule Finset.univ s →
      ¬ moreThanHalfBy S.data s
        ((K : ℝ) ^ (logTwo K / 25) / 8 * lowerBound S.data)}

/-- Standard constant-factor optimization promise: optimum ≤ b versus optimum
strictly greater than c b, with the positive rational b part of the input. -/
def objectiveYes (o : Objective) : Set (List Bool) :=
  {w | ∃ (S : RationalShop) (b : ℚ), 0 < b ∧ w = thresholdCode S b ∧
    ∃ s, S.data.IsFeasibleSchedule Finset.univ s ∧ value S.data o s ≤ (b : ℝ)}

def objectiveNo (o : Objective) (c : ℝ) : Set (List Bool) :=
  {w | ∃ (S : RationalShop) (b : ℚ), 0 < b ∧ w = thresholdCode S b ∧
    ∀ s, S.data.IsFeasibleSchedule Finset.univ s → c * (b : ℝ) < value S.data o s}

/-- Deterministic time on bit strings, using the published Cook machine. -/
def DetTime (L : CookPvsNP.Lang Bool) (bound : ℕ → ℝ) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ) (ι : Bool ↪ Γ) (M : CookPvsNP.TM Γ),
    ∀ x, ∃ t : ℕ, (t : ℝ) ≤ bound x.length ∧ M.HaltsWithin t (x.map ι) ∧
      (x ∈ L ↔ (M.run t (M.init (x.map ι))).state = M.qaccept)

/-- Union over positive multipliers and exponents, with n+2 avoiding small-input
logarithms. The machine and constants may depend on the language. -/
def NPInQuasipolynomialTime : Prop :=
  ∀ L : CookPvsNP.Lang Bool, L ∈ CookPvsNP.NP Bool →
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      DetTime L (fun n => c * (n + 2 : ℝ) ^ (a * logTwo (n + 2)))

/-- Embed binary words in the nonblank symbols 1,2 of the published multi-tape
machine. Tape blank is 0; no length-dependent alphabet or machine is used. -/
def bitSymbols (w : List Bool) : List OAI.MatchingFPRAS.Symbol :=
  w.map fun b => if b then 2 else 1

open Classical in
/-- One nonblank symbol is the decision output. -/
noncomputable def verdict (L : CookPvsNP.Lang Bool) (w : List Bool) :
    List OAI.MatchingFPRAS.Symbol := [if w ∈ L then 2 else 1]

/-- Las Vegas decision: EVERY halting run is correct, and the full expected
halting time (an extended-nonnegative Lebesgue integral) is bounded. A positive
probability of divergence therefore cannot satisfy a finite bound. -/
def ZeroErrorTime (L : CookPvsNP.Lang Bool) (bound : ℕ → ℝ) : Prop :=
  ∃ A : IntQuotHNP.Supplement.MTMachine, ∀ w,
    IntQuotHNP.Supplement.AlwaysOutputs A (bitSymbols w) (verdict L w) ∧
    IntQuotHNP.Supplement.expectedTime A (bitSymbols w) ≤ ENNReal.ofReal (bound w.length)

/-- For fixed exponent p, union over constant time multipliers. A is outside
ε and the languages in the theorem, making the O(1/ε) coefficient uniform.
For ε ≥ 1 we use exponent A, equivalent to applying the small-error result.
This does not limit the arbitrary positive ε in the theorem. -/
def NPInZeroErrorTime (p : ℝ) : Prop :=
  ∀ L : CookPvsNP.Lang Bool, L ∈ CookPvsNP.NP Bool →
    ∃ c : ℝ, 0 < c ∧
      ZeroErrorTime L (fun n => c * (2 : ℝ) ^ ((logTwo (n + 2)) ^ p))

end FlowJobHardness.FlowShopGap.Supplement


