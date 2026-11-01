-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P47
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:30:34.159971+00:00
-- url     : https://prove2.me/theorems/01d86c6b-9875-4455-9563-cb3189997264
-- title:
--   Definitions for Device-independent quantum key distribution based on measurement inputs
-- statement:
--   The objects the formalized statements of *Device-independent quantum key distribution based on measurement inputs* (arXiv:1308.6447) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Behavior`: Binary conditional probabilities p(a,b|A,B), with inputs first (PDF pp.2,5).
--   - `IsBehavior`: A nonnegative normalized binary conditional distribution (PDF pp.2,5).
--   - `bipartitePOVMBehavior`: The bipartite Born behavior for two binary local POVMs in arbitrary finite dimensions (PDF pp.3,5). The state and local effects are independent of the other party's input.
--   - `HasFiniteQuantumRealization`: A finite-dimensional quantum realization of the entire binary behavior (PDF pp.3,5). All dimensions are allowed; one shared density and two local binary POVMs produce every input/output probability. No Hardy, purity, product-state or uniqueness premise is built in.
--   - `PairLaw`: A binary pair law; also used for the accepted key and fixed Eve guess (PDF pp.4,8).
--   - `IsPairLaw`: A nonnegative normalized pair law (PDF pp.4,8).
--   - `HardyParameters`: Noncommuting local rank-one bases of (3); party false is Alice (PDF p.3).
--   - `localKet`: The two local measurement bases, including the conjugates and minus in (3) (PDF p.3).
--   - `hardyPhi`: The four ordered product vectors of (2) (PDF pp.2–3).
--   - `gsResidual`: The Gram–Schmidt residual in (4), with the inner product linear in its second slot (PDF p.3).
--   - `gsDenominatorSq`: The squared denominator of (4); used only for the source's unit input vectors (PDF p.3).
--   - `gsStep`: One normalized step of (4); strict denominator positivity is a conclusion below (PDF p.3).
--   - `hardyGS`: The explicitly constructed four vectors of (4), not an arbitrary Hardy witness (PDF p.3).
--   - `psiH`: The source's Hardy state is the last constructed Gram–Schmidt vector (PDF p.3).
--   - `hardySpan`: The forbidden-event span S of II A (PDF p.3).
--   - `hardyBehavior`: The Born probabilities for the specific two-qubit projective bases (3) (PDF pp.2–3). Projectors are constructed from the local vectors; the input/output order is explicit.
--   - `HardyConditions`: All four Hardy conditions (1), including strictly positive success (PDF p.2).
--   - `binarySettingLaw`: The product setting law (5), with each parameter the probability of input zero (PDF p.4).
--   - `biasedInput`: The four independently signed biases in III; true selects plus epsilon (PDF p.4).
--   - `acceptedMass`: Joint probability of the input pair and the event S = {a=b=0} (PDF pp.3,6).
--   - `siftingProbability`: Pr[S], the sifting probability (PDF pp.3,6).
--   - `aliceMass`: The two unnormalized Alice masses sigma and nu in (15a,b) (PDF p.6).
--   - `acceptedLaw`: Input pair law conditioned on S, used only when acceptance is positive (PDF p.6).
--   - `aliceMarginal`: Alice's marginal of any binary pair law (PDF pp.6,8).
--   - `hardyStatistics`: The signed Hardy specialization of (12), in order h1,h2,h3,h4 (PDF p.5).
--   - `noisyHardy`: Visibility family (13); eta=0 is white noise and eta=1 is ideal (PDF p.5).
--   - `guessLaw`: The accepted joint law of Alice's bit A and the fixed Eve guess G (PDF p.8). p0,p1 are accepted-round group masses; zero-mass groups contribute zero.
--   - `balanceRetention`: Independent bit-dependent retention kernel in VI B (PDF p.8).
--   - `retention`: Probability of retention in a normalized pair law (PDF p.8).
--   - `retainedLaw`: Pair law conditioned on the public keep flag; the old fixed guess is unchanged (PDF p.8). It is used only when the retention probability is positive.
--   - `pairEntropy`: Shannon entropy in bits of a finite pair law; zero terms have 0 log 0 = 0 (PDF pp.6,8).
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, https://arxiv.org/abs/1308.6447v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Statements from arXiv:1308.6447v3. Binary labels use false = 0, true = 1.
A behavior is evaluated in the order (Alice input, Bob input, Alice output, Bob output).
Only the algebraic results pinned by the source are stated. Operational security claims
and cited background are inventoried in HARD.md and GAPS.json.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate
open scoped BigOperators

/-- Binary conditional probabilities p(a,b|A,B), with inputs first (PDF pp.2,5). -/
abbrev Behavior := Bool → Bool → Bool → Bool → ℝ

/-- A nonnegative normalized binary conditional distribution (PDF pp.2,5). -/
def IsBehavior (p : Behavior) : Prop :=
  (∀ A B a b, 0 ≤ p A B a b) ∧ (∀ A B, ∑ a, ∑ b, p A B a b = 1)

/-- The bipartite Born behavior for two binary local POVMs in arbitrary finite dimensions
(PDF pp.3,5). The state and local effects are independent of the other party's input. -/
noncomputable def bipartitePOVMBehavior {dA dB : ℕ}
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (M : Bool → Bool → Matrix (Fin dA) (Fin dA) ℂ)
    (N : Bool → Bool → Matrix (Fin dB) (Fin dB) ℂ) : Behavior :=
  fun A B a b => effectProb (Matrix.kronecker (M A a) (N B b)) rho

/-- A finite-dimensional quantum realization of the entire binary behavior (PDF pp.3,5).
All dimensions are allowed; one shared density and two local binary POVMs produce every
input/output probability. No Hardy, purity, product-state or uniqueness premise is built in. -/
def HasFiniteQuantumRealization (p : Behavior) : Prop :=
  ∃ (dA dB : ℕ)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (M : Bool → Bool → Matrix (Fin dA) (Fin dA) ℂ)
    (N : Bool → Bool → Matrix (Fin dB) (Fin dB) ℂ),
    IsDensityMatrix rho ∧ (∀ A, IsPOVM (M A)) ∧ (∀ B, IsPOVM (N B)) ∧
      p = bipartitePOVMBehavior rho M N

/-- A binary pair law; also used for the accepted key and fixed Eve guess (PDF pp.4,8). -/
abbrev PairLaw := Bool → Bool → ℝ

/-- A nonnegative normalized pair law (PDF pp.4,8). -/
def IsPairLaw (w : PairLaw) : Prop :=
  (∀ A B, 0 ≤ w A B) ∧ (∑ A, ∑ B, w A B = 1)

/-- Noncommuting local rank-one bases of (3); party false is Alice (PDF p.3). -/
structure HardyParameters where
  alpha : Bool → ℂ
  beta : Bool → ℂ
  normalized : ∀ P, ‖alpha P‖ ^ 2 + ‖beta P‖ ^ 2 = 1
  alpha_pos : ∀ P, 0 < ‖alpha P‖
  alpha_lt_one : ∀ P, ‖alpha P‖ < 1

/-- The two local measurement bases, including the conjugates and minus in (3) (PDF p.3). -/
noncomputable def localKet (d : HardyParameters) (P X a : Bool) :
    EuclideanSpace ℂ Bool :=
  if X then
    if a then conj (d.beta P) • ket false - conj (d.alpha P) • ket true
    else d.alpha P • ket false + d.beta P • ket true
  else ket a

/-- The four ordered product vectors of (2) (PDF pp.2–3). -/
noncomputable def hardyPhi (d : HardyParameters) : Fin 4 → EuclideanSpace ℂ (Bool × Bool) :=
  ![tensorVec (localKet d false true true) (localKet d true true true),
    tensorVec (ket false) (localKet d true true false),
    tensorVec (localKet d false true false) (ket false),
    tensorVec (ket false) (ket false)]

/-- The Gram–Schmidt residual in (4), with the inner product linear in its second slot (PDF p.3). -/
noncomputable def gsResidual (us : List (EuclideanSpace ℂ (Bool × Bool)))
    (v : EuclideanSpace ℂ (Bool × Bool)) : EuclideanSpace ℂ (Bool × Bool) :=
  v - (us.map (fun u => (inner ℂ u v) • u)).sum

/-- The squared denominator of (4); used only for the source's unit input vectors (PDF p.3). -/
noncomputable def gsDenominatorSq (us : List (EuclideanSpace ℂ (Bool × Bool)))
    (v : EuclideanSpace ℂ (Bool × Bool)) : ℝ :=
  1 - (us.map (fun u => ‖inner ℂ u v‖ ^ 2)).sum

/-- One normalized step of (4); strict denominator positivity is a conclusion below (PDF p.3). -/
noncomputable def gsStep (us : List (EuclideanSpace ℂ (Bool × Bool)))
    (v : EuclideanSpace ℂ (Bool × Bool)) : EuclideanSpace ℂ (Bool × Bool) :=
  ((Real.sqrt (gsDenominatorSq us v) : ℂ)⁻¹) • gsResidual us v

/-- The explicitly constructed four vectors of (4), not an arbitrary Hardy witness (PDF p.3). -/
noncomputable def hardyGS (d : HardyParameters) : Fin 4 → EuclideanSpace ℂ (Bool × Bool) :=
  let v0 := hardyPhi d 0
  let v1 := gsStep [v0] (hardyPhi d 1)
  let v2 := gsStep [v0, v1] (hardyPhi d 2)
  let v3 := gsStep [v0, v1, v2] (hardyPhi d 3)
  ![v0, v1, v2, v3]

/-- The source's Hardy state is the last constructed Gram–Schmidt vector (PDF p.3). -/
noncomputable def psiH (d : HardyParameters) : EuclideanSpace ℂ (Bool × Bool) :=
  hardyGS d 3

/-- The forbidden-event span S of II A (PDF p.3). -/
noncomputable def hardySpan (d : HardyParameters) :
    Submodule ℂ (EuclideanSpace ℂ (Bool × Bool)) :=
  Submodule.span ℂ (Set.range (fun i : Fin 3 => hardyPhi d (Fin.castSucc i)))

/-- The Born probabilities for the specific two-qubit projective bases (3) (PDF pp.2–3).
Projectors are constructed from the local vectors; the input/output order is explicit. -/
noncomputable def hardyBehavior (d : HardyParameters)
    (rho : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Behavior :=
  fun A B a b => effectProb
    (pureDensity (tensorVec (localKet d false A a) (localKet d true B b))) rho

/-- All four Hardy conditions (1), including strictly positive success (PDF p.2). -/
def HardyConditions (p : Behavior) : Prop :=
  0 < p false false false false ∧ p true false false false = 0 ∧
    p false true false false = 0 ∧ p true true true true = 0

/-- The product setting law (5), with each parameter the probability of input zero (PDF p.4). -/
def binarySettingLaw (pA pB : ℝ) : PairLaw :=
  fun A B => (if A then 1 - pA else pA) * (if B then 1 - pB else pB)

/-- The four independently signed biases in III; true selects plus epsilon (PDF p.4). -/
def biasedInput (pA pB epsilon : ℝ) (e : Bool × Bool) : PairLaw :=
  binarySettingLaw (pA + (if e.1 then epsilon else -epsilon))
    (pB + (if e.2 then epsilon else -epsilon))

/-- Joint probability of the input pair and the event S = {a=b=0} (PDF pp.3,6). -/
def acceptedMass (p : Behavior) (w : PairLaw) : PairLaw :=
  fun A B => w A B * p A B false false

/-- Pr[S], the sifting probability (PDF pp.3,6). -/
noncomputable def siftingProbability (p : Behavior) (w : PairLaw) : ℝ :=
  ∑ A, ∑ B, acceptedMass p w A B

/-- The two unnormalized Alice masses sigma and nu in (15a,b) (PDF p.6). -/
noncomputable def aliceMass (p : Behavior) (w : PairLaw) (A : Bool) : ℝ :=
  ∑ B, acceptedMass p w A B

/-- Input pair law conditioned on S, used only when acceptance is positive (PDF p.6). -/
noncomputable def acceptedLaw (p : Behavior) (w : PairLaw) : PairLaw :=
  fun A B => acceptedMass p w A B / siftingProbability p w

/-- Alice's marginal of any binary pair law (PDF pp.6,8). -/
noncomputable def aliceMarginal (j : PairLaw) (A : Bool) : ℝ := ∑ B, j A B

/-- The signed Hardy specialization of (12), in order h1,h2,h3,h4 (PDF p.5). -/
def hardyStatistics (p : Behavior) : Fin 4 → ℝ :=
  ![p false false false false, -p true false false false,
    -p false true false false, -p true true true true]

/-- Visibility family (13); eta=0 is white noise and eta=1 is ideal (PDF p.5). -/
noncomputable def noisyHardy (d : HardyParameters) (eta : ℝ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (((1 - eta) / 4 : ℝ) : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) +
    (eta : ℂ) • pureDensity (psiH d)

/-- The accepted joint law of Alice's bit A and the fixed Eve guess G (PDF p.8).
p0,p1 are accepted-round group masses; zero-mass groups contribute zero. -/
def guessLaw (p0 p1 P0 P1 : ℝ) : PairLaw :=
  fun A G => if G then (if A then p1 * P1 else p1 * (1 - P1))
    else (if A then p0 * (1 - P0) else p0 * P0)

/-- Independent bit-dependent retention kernel in VI B (PDF p.8). -/
noncomputable def balanceRetention (j : PairLaw) (A : Bool) : ℝ :=
  min (aliceMarginal j false) (aliceMarginal j true) / aliceMarginal j A

/-- Probability of retention in a normalized pair law (PDF p.8). -/
noncomputable def retention (j : PairLaw) (k : Bool → ℝ) : ℝ :=
  ∑ A, ∑ B, j A B * k A

/-- Pair law conditioned on the public keep flag; the old fixed guess is unchanged (PDF p.8).
It is used only when the retention probability is positive. -/
noncomputable def retainedLaw (j : PairLaw) (k : Bool → ℝ) : PairLaw :=
  fun A B => j A B * k A / retention j k

/-- Shannon entropy in bits of a finite pair law; zero terms have 0 log 0 = 0 (PDF pp.6,8). -/
noncomputable def pairEntropy (j : PairLaw) : ℝ :=
  -(∑ A, ∑ B, j A B * (Real.log (j A B) / Real.log 2))

/-! Sanity examples pin definitions and conventions; no headline proofs are supplied. -/

example : IsBehavior (fun _ _ _ _ => 1 / 4) := by
  norm_num [IsBehavior]

/-- A zero input matrix produces zero Born mass, rather than a normalized law. -/
example {dA dB : ℕ}
    (M : Bool → Bool → Matrix (Fin dA) (Fin dA) ℂ)
    (N : Bool → Bool → Matrix (Fin dB) (Fin dB) ℂ) :
    bipartitePOVMBehavior (0 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) M N =
      (fun _ _ _ _ => 0) := by
  funext A B a b
  simp [bipartitePOVMBehavior, effectProb]

/-- A normalized one-dimensional system with identity effects has unit (0,0) mass. -/
example :
    bipartitePOVMBehavior (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)
      (fun _ a => if a then 0 else 1) (fun _ b => if b then 0 else 1)
      false false false false = 1 := by
  norm_num [bipartitePOVMBehavior, effectProb, Matrix.kronecker,
    Matrix.kroneckerMap, Matrix.trace, Matrix.mul_apply]

/-- Supplying one normalized state and local POVMs certifies their computed behavior. -/
example {dA dB : ℕ}
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (M : Bool → Bool → Matrix (Fin dA) (Fin dA) ℂ)
    (N : Bool → Bool → Matrix (Fin dB) (Fin dB) ℂ)
    (hrho : IsDensityMatrix rho) (hM : ∀ A, IsPOVM (M A)) (hN : ∀ B, IsPOVM (N B)) :
    HasFiniteQuantumRealization (bipartitePOVMBehavior rho M N) := by
  exact ⟨dA, dB, rho, M, N, hrho, hM, hN, rfl⟩

example : IsPairLaw (fun _ _ => 1 / 4) := by
  norm_num [IsPairLaw]

example (d : HardyParameters) (P a : Bool) : localKet d P false a = ket a := by
  rfl

example (d : HardyParameters) :
    localKet d false true true =
      conj (d.beta false) • ket false - conj (d.alpha false) • ket true := by
  rfl

example (d : HardyParameters) : hardyPhi d 3 = tensorVec (ket false) (ket false) := by
  rfl

example (v : EuclideanSpace ℂ (Bool × Bool)) :
    gsResidual [] v = v ∧ gsDenominatorSq [] v = 1 := by
  simp [gsResidual, gsDenominatorSq]

example (v : EuclideanSpace ℂ (Bool × Bool)) : gsStep [] v = v := by
  simp [gsStep, gsDenominatorSq, gsResidual]

example (d : HardyParameters) : hardyGS d 0 = hardyPhi d 0 ∧ psiH d = hardyGS d 3 := by
  exact ⟨rfl, rfl⟩

example (d : HardyParameters) : hardyPhi d 0 ∈ hardySpan d := by
  exact Submodule.subset_span ⟨(0 : Fin 3), rfl⟩

example (d : HardyParameters) (rho : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    hardyBehavior d rho false false false false =
      effectProb (pureDensity (tensorVec (ket false) (ket false))) rho := by
  rfl

example : ¬ HardyConditions (fun _ _ _ _ => 0) := by
  simp [HardyConditions]

example : binarySettingLaw (1 / 2) (1 / 2) false true = 1 / 4 := by
  norm_num [binarySettingLaw]

example (pA pB : ℝ) (e : Bool × Bool) : biasedInput pA pB 0 e = binarySettingLaw pA pB := by
  simp [biasedInput]

example (p : Behavior) (w : PairLaw) :
    acceptedMass p w false true = w false true * p false true false false := by
  rfl

example (p : Behavior) (w : PairLaw) :
    siftingProbability p w = ∑ A, aliceMass p w A := by
  rfl

example (p : Behavior) (w : PairLaw) (A : Bool) :
    aliceMarginal (acceptedLaw p w) A =
      ∑ B, acceptedMass p w A B / siftingProbability p w := by
  rfl

example (p : Behavior) : hardyStatistics p 2 = -p false true false false := by
  rfl

example (d : HardyParameters) : noisyHardy d 1 = pureDensity (psiH d) := by
  simp [noisyHardy]

example (p0 p1 P0 P1 : ℝ) : guessLaw p0 p1 P0 P1 true false = p0 * (1 - P0) := by
  rfl

example (j : PairLaw) (A : Bool) : balanceRetention j A =
    min (aliceMarginal j false) (aliceMarginal j true) / aliceMarginal j A := by
  rfl

example (j : PairLaw) : retention j (fun _ => 0) = 0 := by
  simp [retention]

example (j : PairLaw) (k : Bool → ℝ) (A B : Bool) :
    retainedLaw j k A B = j A B * k A / retention j k := by
  rfl

example : pairEntropy (fun _ _ => 0) = 0 := by
  simp [pairEntropy]

end QAlgorithms.Papers.Independent.Intakethird100.P47


