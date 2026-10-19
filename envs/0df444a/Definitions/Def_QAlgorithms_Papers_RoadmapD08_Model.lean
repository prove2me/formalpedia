-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapD08_Model
-- name    : QAlgorithms_Papers_RoadmapD08_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:40:09.573864+00:00
-- url     : https://prove2.me/theorems/f2846272-106e-488a-a554-fde5d9ca8113
-- title:
--   Efficient Exact Quantum Sampling from the Sun-Wootters Distribution for Optimal Polynomial Intersection: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Efficient Exact Quantum Sampling from the Sun-Wootters Distribution for Optimal Polynomial Intersection, arXiv:2607.16541v2, https://arxiv.org/abs/2607.16541v2. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_SunWoottersAsymptotics
noncomputable section

attribute [local instance] Classical.propDecidable

open Filter
open scoped Matrix ENNReal

namespace QAlgorithms.Papers.RoadmapD08

open QAlgorithms.SunWootters

/-! Chunk-local contracts combine all three clauses of Theorem 1.1, retaining failure.
The finite arbitrary-list identity makes no unpriced efficiency assertion. -/

/-- Known common d08Density and the domain of (8), PDF p.7. -/
def d08Density (P : OPI.PrimePublicData) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(P.c : ℝ) / P.p, by
    constructor
    · exact div_pos (Nat.cast_pos.mpr P.c_pos) (Nat.cast_pos.mpr P.prime.pos)
    · exact (div_lt_one (Nat.cast_pos.mpr P.prime.pos)).mpr (by exact_mod_cast P.c_lt)⟩

/-- Discrepancies constructed from the actual sets, equation (8). -/
def d08Discrepancies (P : OPI.PrimePublicData) (sets : Fin P.m → Finset (ZMod P.p)) :
    Fin P.m → ZMod P.p → ℝ :=
  fun i => discrepancy (sets i) (d08Density P).val (d08Density P).property

/-- Denominator of (13); positivity is required before normalization. -/
def d08TargetDenominator (P : OPI.PrimePublicData) (ell : ℕ) (h3 : 3 ≤ ell) (hm : ell ≤ P.m)
    (sets : Fin P.m → Finset (ZMod P.p)) : ℝ :=
  letI : Fact P.p.Prime := ⟨P.prime⟩
  letI : NeZero P.p := ⟨P.prime.ne_zero⟩
  ∑ x : Fin P.n → ZMod P.p,
    targetAmplitude (OPI.vandermondeEncoder P.alpha P.n) (d08Discrepancies P sets)
      (⟨ell, h3, hm⟩ : ShellDomain P.m) x ^ 2

/-- Equations (8),(10)--(13), with signed shell subtraction. -/
def d08Target (P : OPI.PrimePublicData) (ell : ℕ) (h3 : 3 ≤ ell) (hm : ell ≤ P.m)
    (sets : Fin P.m → Finset (ZMod P.p))
    (positive : 0 < d08TargetDenominator P ell h3 hm sets) :
    (Fin P.n → ZMod P.p) → ℝ :=
  letI : Fact P.p.Prime := ⟨P.prime⟩
  letI : NeZero P.p := ⟨P.prime.ne_zero⟩
  targetLaw (OPI.vandermondeEncoder P.alpha P.n) (d08Discrepancies P sets)
    (⟨ell, h3, hm⟩ : ShellDomain P.m) positive

/-- Complete duplicate-free lists in lexicographic field-value order (PDF pp.11--12). -/
def d08IsCanonicalList {p m n : ℕ} [NeZero p]
    (H : Matrix (Fin n) (Fin m) (ZMod p)) (D : ShellDomain m)
    (lists : (Fin n → ZMod p) → List (Fin m → ZMod p)) : Prop :=
  ∀ s, (lists s).Nodup ∧ (lists s).toFinset = shellFiber H D s ∧
    (lists s).Pairwise (fun y z =>
      List.Lex (· < ·) (List.ofFn fun i => (y i).val) (List.ofFn fun i => (z i).val))

/-- Exact ideal attempt: common padding L=2^q, joint (J,Q)=(0^q,1), positive-character
final Fourier transform. Both constructed norms are positive (PDF pp.9--13). -/
def d08FiniteExactClause : Prop :=
  ∀ (P : OPI.PrimePublicData) (ell : ℕ) (h3 : 3 ≤ ell) (hm : ell ≤ P.m)
    (sets : Fin P.m → Finset (ZMod P.p)), (∀ i, (sets i).card = P.c) →
    letI : Fact P.p.Prime := ⟨P.prime⟩
    letI : NeZero P.p := ⟨P.prime.ne_zero⟩
    let B := OPI.vandermondeEncoder P.alpha P.n
    let H := B.transpose
    let D : ShellDomain P.m := ⟨ell, h3, hm⟩
    let g := fun i => localFourier (d08Discrepancies P sets i)
    ∀ (positive : 0 < d08TargetDenominator P ell h3 hm sets)
      (pos0 : 0 < errorNormSq g D) (q : ℕ)
      (lists : (Fin P.n → ZMod P.p) → List (Fin P.m → ZMod P.p))
      (canonical : d08IsCanonicalList H D lists) (fits : ∀ s, (lists s).length ≤ 2 ^ q),
      syndromeNormSq H g D = d08TargetDenominator P ell h3 hm sets / (P.p : ℝ) ^ P.n ∧
      0 < syndromeNormSq H g D ∧
      let attempt := idealAttempt H g D pos0 q lists
        (fun s => (canonical s).1) fits (fun s => (canonical s).2.1)
      1 - attempt none = syndromeNormSq H g D / ((2 : ℝ) ^ q * errorNormSq g D) ∧
      ∀ x, attempt (some x) / (1 - attempt none) = d08Target P ell h3 hm sets positive x

/-- Full encoded-register errors include leakage; Corollary 6.6, PDF p.16. -/
def d08PrecisionClause : Prop :=
  ∀ (I X : Type) [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (ideal implemented : EuclideanSpace ℂ I) (Pi : Matrix I I ℂ)
    (Qideal Qimplemented : Matrix I I ℂ) (decode : I → X) (L : ℕ) (eta : ℝ),
    0 < L → 0 < eta → eta < 1 → IsState ideal → IsState implemented →
    Pi.IsHermitian → Pi * Pi = Pi →
    Qideal ∈ Matrix.unitaryGroup I ℂ → Qimplemented ∈ Matrix.unitaryGroup I ℂ →
    1 / (2 * (L : ℝ)) ≤ ‖act Pi ideal‖ ^ 2 →
    ‖implemented - ideal‖ ≤ min (1 / (8 * (L : ℝ))) (eta / (4 * Real.sqrt (2 * (L : ℝ)))) →
    specNorm (Qimplemented - Qideal) ≤ eta / 2 →
    SuccessfulBranchAccuracy ideal implemented Pi Qideal Qimplemented decode L eta

/-- Public integer precision requests have logarithmic length (PDF pp.7,17). -/
def d08PrecisionBits (eta : ℝ) : ℕ :=
  max 2 ⌈Real.logb 2 eta⁻¹⌉₊

/-- The supplied XOR oracle (41); its full unitary extension on invalid encodings is free. -/
def d08IsMembershipOracle (P : OPI.PrimePublicData)
    (sets : Fin P.m → Finset (ZMod P.p))
    (O : Matrix (Qubits (Nat.clog 2 P.m + Nat.clog 2 P.p + 1))
      (Qubits (Nat.clog 2 P.m + Nat.clog 2 P.p + 1)) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧ ∀ (i : Fin P.m) (a : ZMod P.p) (b : Bool),
    act O (ket (Fin.snoc (Fin.append (natToBits (Nat.clog 2 P.m) i)
      (natToBits (Nat.clog 2 P.p) a.val)) b)) =
    ket (Fin.snoc (Fin.append (natToBits (Nat.clog 2 P.m) i)
      (natToBits (Nat.clog 2 P.p) a.val)) (xor b (decide (a ∈ sets i))))

/-- Reindex the same supplied oracle to the declared circuit arity. -/
def d08SuppliedOracles (S : UniformPrimeSampler) (Q : SamplingRequest)
    (O : Matrix (Qubits (Nat.clog 2 Q.parameters.m + Nat.clog 2 Q.parameters.p + 1))
      (Qubits (Nat.clog 2 Q.parameters.m + Nat.clog 2 Q.parameters.p + 1)) ℂ) :
    (k : Fin (S.family.construct Q).oracles) →
      Matrix (Qubits ((S.family.construct Q).arity k)) (Qubits ((S.family.construct Q).arity k)) ℂ :=
  fun k => O.submatrix (fun z => z ∘ Fin.cast (S.arity Q k).symm)
    (fun z => z ∘ Fin.cast (S.arity Q k).symm)

/-- Actual circuit law with a separate failure symbol; no invalid output mass is discarded. -/
def d08OutputLaw (S : UniformPrimeSampler) (Q : SamplingRequest)
    (O : Matrix (Qubits (Nat.clog 2 Q.parameters.m + Nat.clog 2 Q.parameters.p + 1))
      (Qubits (Nat.clog 2 Q.parameters.m + Nat.clog 2 Q.parameters.p + 1)) ℂ)
    (event : Option (Fin Q.parameters.n → ZMod Q.parameters.p) → Prop) : ℝ :=
  OPI.membershipOutputLaw (S.family.construct Q).program (d08SuppliedOracles S Q O)
    (fun result => event (result.map (samplerCoefficients S Q)))

/-- Failure replaced by any specified fixed default. -/
def d08DefaultLaw (S : UniformPrimeSampler) (Q : SamplingRequest)
    (O : Matrix (Qubits (Nat.clog 2 Q.parameters.m + Nat.clog 2 Q.parameters.p + 1))
      (Qubits (Nat.clog 2 Q.parameters.m + Nat.clog 2 Q.parameters.p + 1)) ℂ)
    (x0 x : Fin Q.parameters.n → ZMod Q.parameters.p) : ℝ :=
  d08OutputLaw S Q O (fun result => result.getD x0 = x)

/-- Uniform charged runtime, PDF pp.7,15--17: gates, oracle calls, classical bit operations,
preparations, measurements and restarts. The frozen family's public preprocessor also has
its own polynomial bound. Density in [1/4,3/4] holds eventually for every balanced family. -/
def d08PolynomialRuntime (S : UniformPrimeSampler) : Prop :=
  (∀ Q k, (S.family.construct Q).control k = false) ∧
  ∃ work : Polynomial ℕ, ∀ Q : SamplingRequest,
    1 / 4 ≤ (d08Density Q.parameters).val → (d08Density Q.parameters).val ≤ 3 / 4 →
    ∀ sets : Fin Q.parameters.m → Finset (ZMod Q.parameters.p),
    (∀ i, (sets i).card = Q.parameters.c) →
    ∀ O, d08IsMembershipOracle Q.parameters sets O →
      OPI.membershipResources (S.family.construct Q).program (d08SuppliedOracles S Q O) +
        Q.parameters.n * (Nat.clog 2 Q.parameters.p + 1) ^ 2 ≤ work.eval (samplingRequestScale Q)

/-- Fixed-slack sampler, Theorem 7.1 (PDF p.17). Positivity and polynomial complete
lists are conclusions. The printed all-member scope is clarified to the proof's eventual
scope; this discrepancy requires independent moderation. -/
def d08FixedSlackClause : Prop :=
  ∀ (mu : ℝ) (delta : ℚ) (lam : ℝ), 0 < mu → mu < 1 / 2 →
    ∀ hdelta : 0 < delta, (delta : ℝ) ≤ 1 / 2 - mu →
    ∀ domain : ExponentDomain mu delta lam,
    (feasibilityExponents mu delta lam domain).1 +
      (feasibilityExponents mu delta lam domain).2 < 0 →
    mu + delta < 1 - Real.sqrt (1 - 2 * mu) →
    ∃ S : UniformPrimeSampler, d08PolynomialRuntime S ∧
    ∀ F : ParameterFamily, F.limitingRate = 2 * mu →
    ∃ rem : ℕ → ℝ, (∀ j, 0 ≤ rem j) ∧ Tendsto rem atTop (nhds 0) ∧
    ∃ j0 : ℕ, ∀ j ≥ j0,
      let P := F.parameters j
      let ell := rationalCutoff P.m P.n delta hdelta
      ∃ (h3 : 3 ≤ ell) (hm : ell ≤ P.m),
      (P.m : ℝ) - ell > Real.sqrt (((P.m : ℝ) - P.n - 1) * P.m) ∧
      ∀ sets : Fin P.m → Finset (ZMod P.p), (∀ i, (sets i).card = P.c) →
      ∃ positive : 0 < d08TargetDenominator P ell h3 hm sets,
      letI : Fact P.p.Prime := ⟨P.prime⟩
      letI : NeZero P.p := ⟨P.prime.ne_zero⟩
      let H := (OPI.vandermondeEncoder P.alpha P.n).transpose
      let D : ShellDomain P.m := ⟨ell, h3, hm⟩
      let g := fun i => localFourier (d08Discrepancies P sets i)
      ∃ (q : ℕ) (lists : (Fin P.n → ZMod P.p) → List (Fin P.m → ZMod P.p)),
        d08IsCanonicalList H D lists ∧ (∀ s, (lists s).length ≤ 2 ^ q) ∧
        (2 ^ q : ℕ) < 2 * P.m ^ 2 ∧ 0 < errorNormSq g D ∧
        1 / (2 * (2 : ℝ) ^ q) ≤ syndromeNormSq H g D / ((2 : ℝ) ^ q * errorNormSq g D) ∧
        ∀ eta beta : ℝ, 0 < eta → eta < 1 / 2 → 0 < beta → beta < 1 / 2 →
        let Q : SamplingRequest := ⟨P, 0, d08PrecisionBits eta, d08PrecisionBits beta⟩
        ∀ O, d08IsMembershipOracle P sets O →
        d08OutputLaw S Q O (fun result => result = none) ≤ beta ∧
        tvDist (fun x => d08OutputLaw S Q O (fun result => result = some x) /
          (1 - d08OutputLaw S Q O (fun result => result = none)))
          (d08Target P ell h3 hm sets positive) ≤ eta ∧
        ∀ x0 : Fin P.n → ZMod P.p,
          tvDist (d08DefaultLaw S Q O x0) (d08Target P ell h3 hm sets positive) ≤ eta + beta ∧
          (∑ x : Fin P.n → ZMod P.p, d08DefaultLaw S Q O x0 x *
            OPI.score (by have := P.n_pos; have := P.n_lt; omega) P.alpha sets x) ≥
              semicircleValue (mu + delta) (1 / 2) - rem j - eta - beta

/-- Corollary 8.6, PDF p.21; rate-only gap and algorithm precede the public family and sets. -/
def d08StrictImprovementClause : Prop :=
  ∀ r : ℝ, 249 / 400 ≤ r → r < 1 →
    ∃ gap : ℝ, 0 < gap ∧ ∃ S : UniformPrimeSampler, d08PolynomialRuntime S ∧
    ∀ F : ParameterFamily, F.limitingRate = r →
      (∃ j0 : ℕ, ∀ j ≥ j0,
        let P := F.parameters j
        let Q : SamplingRequest := ⟨P, 0, 2 * Nat.clog 2 P.m, 2 * Nat.clog 2 P.m⟩
        letI : Fact P.p.Prime := ⟨P.prime⟩
        letI : NeZero P.p := ⟨P.prime.ne_zero⟩
        ∀ sets : Fin P.m → Finset (ZMod P.p), (∀ i, (sets i).card = P.c) →
        ∀ O, d08IsMembershipOracle P sets O →
          (∑ x : Fin P.n → ZMod P.p, d08DefaultLaw S Q O 0 x *
            OPI.score (by have := P.n_pos; have := P.n_lt; omega) P.alpha sets x) ≥
            semicircleValue (r / 2) (1 / 2) + gap) ∧
      ∀ eps beta : ℝ, 0 < eps → 0 < beta → beta < 1 →
        ∃ accuracy confidence j0 : ℕ, ∀ j ≥ j0,
          let P := F.parameters j
          let Q : SamplingRequest := ⟨P, 1, accuracy, confidence⟩
          letI : Fact P.p.Prime := ⟨P.prime⟩
          letI : NeZero P.p := ⟨P.prime.ne_zero⟩
          ∀ sets : Fin P.m → Finset (ZMod P.p), (∀ i, (sets i).card = P.c) →
          ∀ O, d08IsMembershipOracle P sets O →
            d08OutputLaw S Q O (fun result =>
              semicircleValue (r / 2) (1 / 2) + gap - eps ≤
                OPI.score (by have := P.n_pos; have := P.n_lt; omega) P.alpha sets
                  (result.getD 0)) ≥ 1 - beta

/-- Reduced public subproblem for the endpoint construction, PDF p.22. -/
def d08ReducedData (P : OPI.PrimePublicData) (hn : 0 < min P.n (3 * P.m / 4)) :
    OPI.PrimePublicData where
  p := P.p
  prime := P.prime
  m := P.m
  n := min P.n (3 * P.m / 4)
  n_pos := hn
  n_lt := lt_of_le_of_lt (min_le_left _ _) P.n_lt
  m_le := P.m_le
  alpha := P.alpha
  distinct := P.distinct
  c := P.c
  c_pos := P.c_pos
  c_lt := P.c_lt

/-- Padding reduced coefficients by zeros, preserving the original degree bound. -/
def d08PadCoefficients (P : OPI.PrimePublicData)
    (x : Fin (min P.n (3 * P.m / 4)) → ZMod P.p) : Fin P.n → ZMod P.p :=
  fun i => if h : i.val < min P.n (3 * P.m / 4) then x ⟨i.val, h⟩ else 0

/-- Corollary 8.8, PDF pp.22--23. Finite Johnson cutoff, polynomial common L,
errors eta=beta=m^-2, and zero padding; includes limiting r=3/4 and r=1. -/
def d08EndpointClause : Prop :=
  ∃ S : UniformPrimeSampler, d08PolynomialRuntime S ∧
    ∀ F : ParameterFamily, 3 / 4 ≤ F.limitingRate →
      ∃ deficit failure : ℕ → ℝ,
        (∀ j, 0 ≤ deficit j ∧ 0 ≤ failure j) ∧
        Tendsto deficit atTop (nhds 0) ∧ Tendsto failure atTop (nhds 0) ∧
        ∃ j0 : ℕ, ∀ j ≥ j0,
          let P := F.parameters j
          ∃ hn : 0 < min P.n (3 * P.m / 4),
          let Pred := d08ReducedData P hn
          letI : Fact Pred.p.Prime := ⟨Pred.prime⟩
          let ell := (johnsonEndpoint P.m P.n
            ⟨hn, lt_of_le_of_lt (min_le_left _ _) P.n_lt⟩).2
          ∃ (h3 : 3 ≤ ell) (hm : ell ≤ P.m),
          (P.m : ℝ) - ell > Real.sqrt (((P.m : ℝ) - Pred.n - 1) * P.m) ∧
          let Q : SamplingRequest := ⟨P, 2, d08PrecisionBits ((P.m : ℝ)⁻¹ ^ 2),
            d08PrecisionBits ((P.m : ℝ)⁻¹ ^ 2)⟩
          letI : Fact P.p.Prime := ⟨P.prime⟩
          letI : NeZero P.p := ⟨P.prime.ne_zero⟩
          ∀ sets : Fin P.m → Finset (ZMod P.p), (∀ i, (sets i).card = P.c) →
          ∃ positive : 0 < d08TargetDenominator Pred ell h3 hm sets,
          let H := (OPI.vandermondeEncoder Pred.alpha Pred.n).transpose
          let D : ShellDomain P.m := ⟨ell, h3, hm⟩
          let g := fun i => localFourier (d08Discrepancies P sets i)
          ∃ (q : ℕ) (lists : (Fin Pred.n → ZMod P.p) → List (Fin P.m → ZMod P.p)),
            d08IsCanonicalList H D lists ∧ (∀ s, (lists s).length ≤ 2 ^ q) ∧
            (2 ^ q : ℕ) < 2 * P.m ^ 2 ∧ 0 < errorNormSq g D ∧
            1 / (2 * (2 : ℝ) ^ q) ≤ syndromeNormSq H g D / ((2 : ℝ) ^ q * errorNormSq g D) ∧
            ∀ O, d08IsMembershipOracle P sets O →
              d08OutputLaw S Q O (fun result => result = none) ≤ (P.m : ℝ)⁻¹ ^ 2 ∧
              d08OutputLaw S Q O (fun result =>
                ∀ i : Fin P.n, Pred.n ≤ i.val → (result.getD 0) i = 0) = 1 ∧
              tvDist (fun x => d08OutputLaw S Q O (fun result => result = some x) /
                (1 - d08OutputLaw S Q O (fun result => result = none)))
                (fun x => ∑ y : Fin Pred.n → ZMod P.p,
                  if d08PadCoefficients P y = x then d08Target Pred ell h3 hm sets positive y else 0)
                ≤ (P.m : ℝ)⁻¹ ^ 2 ∧
              d08OutputLaw S Q O (fun result =>
                1 - deficit j ≤ OPI.score (by have := P.n_pos; have := P.n_lt; omega)
                  P.alpha sets (result.getD 0)) ≥ 1 - failure j


end QAlgorithms.Papers.RoadmapD08


