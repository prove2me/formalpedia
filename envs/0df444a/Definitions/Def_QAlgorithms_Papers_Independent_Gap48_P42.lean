-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
-- name    : QAlgorithms_Papers_Independent_Gap48_P42
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:34:25.267542+00:00
-- url     : https://prove2.me/theorems/d15555cc-c381-4e6c-9f54-44543ed3dc2f
-- title:
--   Definitions for Quantum states representing perfectly secure bits are always distillable
-- statement:
--   The objects the formalized statements of *Quantum states representing perfectly secure bits are always distillable* (arXiv:quant-ph/0602176) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PartyBasis`: PDF pp.2--3: party k owns a register of dimension D k.
--   - `localIndex`: Fixed local basis relabeling; used identically on bras and kets.
--   - `partyPower`: PDF pp.2--4: independent copies, grouped by the original owners. The local copy enumeration is the accepted fixed enumeration.
--   - `indexedPrivateDit`: PDF p.2, multipartite private dit, after a fixed local basis relabeling. The accepted constructor includes the full joint-shield twists.
--   - `CanConvert`: PDF pp.2--3: deterministic conversion by a complete finite adaptive LOCC tree, including arbitrary local ancillary dimensions and disposal. Density proofs are existentially certified, never assumptions deleting a result.
--   - `CanSelect`: PDF pp.2--3,4: a positive-probability selected outcome of a complete LOCC tree; its other outcomes are retained in the underlying tree.
--   - `twoLabelGHZVector`: PDF p.3: normalized GHZ plus/minus kets on distinct local labels i,j. All uses have N>=2 and i<j.
--   - `twoPhaseGHZMixture`: PDF p.3, Eq.(2.6): the two-phase GHZ mixture, with p in [0,1] in uses.
--   - `ghzCopies`: PDF pp.2--3: m N-party qubit GHZ states, keeping all m qubits per party.
--   - `GHZAchievable`: PDF pp.2--3 and note [19], p.5: operational asymptotic GHZ yield. For every error/rate tolerance, every sufficiently large positive input length has a deterministic LOCC output of full trace-norm error at most epsilon. This is the vanishing-error, liminf-yield formulation; preprocessing success probabilities cannot be discarded.
--   - `distillableGHZ`: PDF pp.2--3: Bell-pair rate for N=2, GHZ rate for N>=2. Extended suprema avoid default values of unbounded real suprema.
--   - `ProductVectors`: PDF pp.2--3: one vector in each local shield, with norms checked separately.
--   - `UnitFactors`: PDF p.2, Eq.(2.2), carried to Eq.(2.5): all local factors are unit vectors.
--   - `productElement`: PDF pp.2--3: conjugate-linear bra, linear ket, on the whole shield.
--   - `productOverlap`: PDF pp.2--3, Eqs.(2.2),(2.5): supremum over exactly normalized product vectors. For positive finite shields this set is nonempty, compact and bounded; the rate theorems assert attainment instead of presupposing a maximizing pair.
--   - `Maximizes`: A maximizing normalized pair; existence is a conclusion below.
--   - `shieldBlock`: PDF pp.2--3: the computed joint-shield block U_i rho U_j^dagger.
--   - `privateDiagonalWeight`: PDF pp.2--3: a_s is computed from the same maximizing vector as eta.
--   - `filterSuccess`: Corrected branch probability and normalized phase parameter, PDF pp.2--3. Theorems establish a,b>0 and 0<eta<=sqrt(a*b) before using these quantities.
--   - `phaseParameter`: PDF pp.2--3: probability of the plus-phase GHZ component.
--   - `filterYield`: Corrected probability-weighted hashing yield, not a conditional branch rate.
--   - `localFilter`: Explicit balanced success operator, PDF pp.2--3. Party 0 balances the weights and removes the coherence phase; other parties project their shields. This rectangular operator alone is trace decreasing, not a TP protocol.
--   - `jointFilter`: Tensor product of precisely the local success operators.
--   - `filteredBranch`: The actual unnormalized all-success output, not an arbitrary output state.
--   - `PairConclusion`: Data and exact success identity used by both quantitative conclusions. Every positivity, probability domain and Cauchy--Schwarz bound is a conclusion.
--   - `KeyPair`: Distinct ordered key pairs; the domain is nonempty at d>=2.
--   - `bestPairYield`: PDF p.3: the finite maximum over all key pairs for the chosen maximizing vectors. The finite nonempty domain at d>=2 guards the real supremum.
--   - `bipartitePrivateRaw`: Bipartite private constructor, with the accepted exact block formula. Only the parentheses and the two fixed local bases are changed; each shield stays with its owner. Raw twists allow the explicitly computed tensor twists below to be checked for unitarity in the tensor-closure conclusion.
--   - `bipartitePrivate`: PDF pp.1,4: the physical bipartite private state; rho is normalized in uses.
--   - `asTwoParties`: Fixed bipartite-to-partywise adapter, with party 0 Alice and party 1 Bob.
--   - `bipartiteDistillable`: PDF pp.2,4: ordinary Bell-pair distillability, the two-party specialization.
--   - `KeyAchievable`: PDF p.4: private-key rate, using deterministic accepted finite LOCC maps, full trace norm and arbitrary positive finite output shields at every n. The denominator counts input copies and the numerator counts only key bits. All sufficiently large positive n are covered; no optimal sequence is assumed.
--   - `distillableKey`: PDF pp.3--4: operational distillable key, including rate zero.
--   - `regroupIndex`: PDF p.4: regroup key and shield copy tuples without changing either owner.
--   - `tensorTwists`: PDF p.4: the computed twist for a key tuple, not an existential new twist.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, https://arxiv.org/abs/quant-ph/0602176v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Horodecki--Augusiak, arXiv:quant-ph/0602176v2, PDF pp.1--5.
All new objects are paper-local adapters or explicit operational definitions.
Rates are nonnegative extended suprema, in bits per input copy. LOCC uses
complete adaptive instruments and unconditional outputs. No optimal protocol
or attainment of an asymptotic rate is assumed. Compilation is pending.
-/

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--3: party k owns a register of dimension D k. -/
abbrev PartyBasis {N : ℕ} (D : Fin N → ℕ) :=
  Claimed50.P33.RegisterBasis (fun k => Fin (D k))

/-- Fixed local basis relabeling; used identically on bras and kets. -/
def localIndex (a b : ℕ) : (Fin a × Fin b) ≃ Fin (a * b) :=
  Fintype.equivFinOfCardEq (by simp)

/-- PDF pp.2--4: independent copies, grouped by the original owners.
The local copy enumeration is the accepted fixed enumeration. -/
def partyPower {N : ℕ} {D : Fin N → ℕ}
    (rho : Matrix (PartyBasis D) (PartyBasis D) ℂ) (n : ℕ) :
    Matrix (PartyBasis (fun k => D k ^ n)) (PartyBasis (fun k => D k ^ n)) ℂ :=
  fun x y => ∏ t : Fin n, rho
    (fun k => (Dependency50.P42.copyIndex (D k) n).symm (x k) t)
    (fun k => (Dependency50.P42.copyIndex (D k) n).symm (y k) t)

/-- PDF p.2, multipartite private dit, after a fixed local basis relabeling.
The accepted constructor includes the full joint-shield twists. -/
def indexedPrivateDit {N d : ℕ} {S : Fin N → ℕ}
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ)
    (U : Fin d → Matrix.unitaryGroup (PartyBasis S) ℂ) :
    Matrix (PartyBasis (fun k => d * S k)) (PartyBasis (fun k => d * S k)) ℂ :=
  fun x y => Claimed50.P33.privateDit (m := N) (H := fun k => Fin (S k)) d rho
    (fun i => ⟨(U i : Matrix (PartyBasis S) (PartyBasis S) ℂ), by
      constructor
      · ext a b
        have hab := congrFun (congrFun (U i).property.1 a) b
        by_cases heq : a = b <;>
          simpa only [Matrix.one_apply, heq, if_true, if_false] using hab
      · ext a b
        have hab := congrFun (congrFun (U i).property.2 a) b
        by_cases heq : a = b <;>
          simpa only [Matrix.one_apply, heq, if_true, if_false] using hab⟩)
    (fun k => (localIndex d (S k)).symm (x k))
    (fun k => (localIndex d (S k)).symm (y k))

/-- PDF pp.2--3: deterministic conversion by a complete finite adaptive
LOCC tree, including arbitrary local ancillary dimensions and disposal.
Density proofs are existentially certified, never assumptions deleting a result. -/
def CanConvert {N : ℕ} (D E : Fin N → ℕ)
    (rho : Matrix (PartyBasis D) (PartyBasis D) ℂ)
    (sigma : Matrix (PartyBasis E) (PartyBasis E) ℂ) : Prop :=
  ∃ hD : ∀ k, 0 < D k, ∃ hE : ∀ k, 0 < E k,
  ∃ hrho : IsDensityMatrix rho, ∃ hsigma : IsDensityMatrix sigma,
    Claimed50.P33.LOCC ⟨D, hD, rho, hrho⟩ [(1, ⟨E, hE, sigma, hsigma⟩)]

/-- PDF pp.2--3,4: a positive-probability selected outcome of a complete
LOCC tree; its other outcomes are retained in the underlying tree. -/
def CanSelect {N : ℕ} (D E : Fin N → ℕ)
    (rho : Matrix (PartyBasis D) (PartyBasis D) ℂ)
    (sigma : Matrix (PartyBasis E) (PartyBasis E) ℂ) : Prop :=
  ∃ hD : ∀ k, 0 < D k, ∃ hE : ∀ k, 0 < E k,
  ∃ hrho : IsDensityMatrix rho, ∃ hsigma : IsDensityMatrix sigma,
  ∃ out : List (ℝ × Claimed50.P33.FiniteState N),
    Claimed50.P33.LOCC ⟨D, hD, rho, hrho⟩ out ∧
    ∃ p : ℝ, 0 < p ∧ (p, ⟨E, hE, sigma, hsigma⟩) ∈ out

/-- PDF p.3: normalized GHZ plus/minus kets on distinct local labels i,j.
All uses have N>=2 and i<j. -/
def twoLabelGHZVector (N d : ℕ) (i j : Fin d) (minus : Bool) :
    EuclideanSpace ℂ (Fin N → Fin d) :=
  WithLp.toLp 2 fun x => (Real.sqrt 2 : ℂ)⁻¹ *
    ((if ∀ k, x k = i then 1 else 0) +
      (if ∀ k, x k = j then (if minus then -1 else 1) else 0))

/-- PDF p.3, Eq.(2.6): the two-phase GHZ mixture, with p in [0,1] in uses. -/
def twoPhaseGHZMixture (N d : ℕ) (i j : Fin d) (p : ℝ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (p : ℂ) • pureDensity (twoLabelGHZVector N d i j false) +
    ((1 - p : ℝ) : ℂ) • pureDensity (twoLabelGHZVector N d i j true)

/-- PDF pp.2--3: m N-party qubit GHZ states, keeping all m qubits per party. -/
def ghzCopies (N m : ℕ) :
    Matrix (Fin N → Fin (2 ^ m)) (Fin N → Fin (2 ^ m)) ℂ :=
  partyPower (pureDensity (twoLabelGHZVector N 2 0 1 false)) m

/-- PDF pp.2--3 and note [19], p.5: operational asymptotic GHZ yield.
For every error/rate tolerance, every sufficiently large positive input length
has a deterministic LOCC output of full trace-norm error at most epsilon.
This is the vanishing-error, liminf-yield formulation; preprocessing success
probabilities cannot be discarded. -/
def GHZAchievable {N : ℕ} (D : Fin N → ℕ)
    (rho : Matrix (PartyBasis D) (PartyBasis D) ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ,
    ∀ n : ℕ, n0 ≤ n → 0 < n → ∃ m : ℕ,
    ∃ sigma : Matrix (Fin N → Fin (2 ^ m)) (Fin N → Fin (2 ^ m)) ℂ,
      CanConvert (fun k => D k ^ n) (fun _ => 2 ^ m) (partyPower rho n) sigma ∧
      traceNorm (sigma - ghzCopies N m) ≤ epsilon ∧ r - delta ≤ (m : ℝ) / n

/-- PDF pp.2--3: Bell-pair rate for N=2, GHZ rate for N>=2. Extended
suprema avoid default values of unbounded real suprema. -/
def distillableGHZ {N : ℕ} (D : Fin N → ℕ)
    (rho : Matrix (PartyBasis D) (PartyBasis D) ℂ) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // GHZAchievable D rho r}, ENNReal.ofReal r.val

/-- PDF pp.2--3: one vector in each local shield, with norms checked separately. -/
abbrev ProductVectors {N : ℕ} (S : Fin N → ℕ) :=
  (k : Fin N) → EuclideanSpace ℂ (Fin (S k))

/-- PDF p.2, Eq.(2.2), carried to Eq.(2.5): all local factors are unit vectors. -/
def UnitFactors {N : ℕ} {S : Fin N → ℕ} (f : ProductVectors S) : Prop :=
  ∀ k, ‖f k‖ = 1

/-- PDF pp.2--3: conjugate-linear bra, linear ket, on the whole shield. -/
def productElement {N : ℕ} {S : Fin N → ℕ}
    (X : Matrix (PartyBasis S) (PartyBasis S) ℂ) (f g : ProductVectors S) : ℂ :=
  ∑ x : PartyBasis S, ∑ y : PartyBasis S,
    conj (∏ k, f k (x k)) * X x y * (∏ k, g k (y k))

/-- PDF pp.2--3, Eqs.(2.2),(2.5): supremum over exactly normalized product
vectors. For positive finite shields this set is nonempty, compact and bounded;
the rate theorems assert attainment instead of presupposing a maximizing pair. -/
def productOverlap {N : ℕ} {S : Fin N → ℕ}
    (X : Matrix (PartyBasis S) (PartyBasis S) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ f g : ProductVectors S,
    UnitFactors f ∧ UnitFactors g ∧ r = ‖productElement X f g‖}

/-- A maximizing normalized pair; existence is a conclusion below. -/
def Maximizes {N : ℕ} {S : Fin N → ℕ}
    (X : Matrix (PartyBasis S) (PartyBasis S) ℂ) (f g : ProductVectors S) : Prop :=
  UnitFactors f ∧ UnitFactors g ∧ ‖productElement X f g‖ = productOverlap X

/-- PDF pp.2--3: the computed joint-shield block U_i rho U_j^dagger. -/
def shieldBlock {N d : ℕ} {S : Fin N → ℕ}
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ)
    (U : Fin d → Matrix.unitaryGroup (PartyBasis S) ℂ) (i j : Fin d) :
    Matrix (PartyBasis S) (PartyBasis S) ℂ :=
  (U i : Matrix (PartyBasis S) (PartyBasis S) ℂ) * rho *
    (U j : Matrix (PartyBasis S) (PartyBasis S) ℂ)ᴴ

/-- PDF pp.2--3: a_s is computed from the same maximizing vector as eta. -/
def privateDiagonalWeight {N d : ℕ} {S : Fin N → ℕ}
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ)
    (U : Fin d → Matrix.unitaryGroup (PartyBasis S) ℂ) (i : Fin d)
    (f : ProductVectors S) : ℝ := (productElement (shieldBlock rho U i i) f f).re

/-- Corrected branch probability and normalized phase parameter, PDF pp.2--3.
Theorems establish a,b>0 and 0<eta<=sqrt(a*b) before using these quantities. -/
def filterSuccess (d : ℕ) (a b : ℝ) : ℝ := 2 * min a b / d

/-- PDF pp.2--3: probability of the plus-phase GHZ component. -/
def phaseParameter (eta a b : ℝ) : ℝ := 1 / 2 + eta / (2 * Real.sqrt (a * b))

/-- Corrected probability-weighted hashing yield, not a conditional branch rate. -/
def filterYield (d : ℕ) (eta a b : ℝ) : ℝ :=
  filterSuccess d a b * (1 - QAlgorithms.binEntropy2 (phaseParameter eta a b))

/-- Explicit balanced success operator, PDF pp.2--3. Party 0 balances the
weights and removes the coherence phase; other parties project their shields.
This rectangular operator alone is trace decreasing, not a TP protocol. -/
def localFilter {N d : ℕ} {S : Fin N → ℕ} (i j : Fin d)
    (f g : ProductVectors S) (a b : ℝ) (c : ℂ) (k : Fin N) :
    Matrix (Fin d) (Fin (d * S k)) ℂ :=
  fun x y =>
    let z := (localIndex d (S k)).symm y
    (if x = i ∧ z.1 = i then
      (if k.val = 0 then (Real.sqrt (min a b / a) : ℂ) else 1) * conj (f k z.2)
      else 0) +
    (if x = j ∧ z.1 = j then
      (if k.val = 0 then (Real.sqrt (min a b / b) : ℂ) * (c / (‖c‖ : ℂ)) else 1) *
        conj (g k z.2) else 0)

/-- Tensor product of precisely the local success operators. -/
def jointFilter {N d : ℕ} {S : Fin N → ℕ} (i j : Fin d)
    (f g : ProductVectors S) (a b : ℝ) (c : ℂ) :
    Matrix (Fin N → Fin d) (PartyBasis (fun k => d * S k)) ℂ :=
  fun x y => ∏ k, localFilter i j f g a b c k (x k) (y k)

/-- The actual unnormalized all-success output, not an arbitrary output state. -/
def filteredBranch {N d : ℕ} {S : Fin N → ℕ}
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ)
    (U : Fin d → Matrix.unitaryGroup (PartyBasis S) ℂ) (i j : Fin d)
    (f g : ProductVectors S) : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  let K := jointFilter i j f g (privateDiagonalWeight rho U i f) (privateDiagonalWeight rho U j g)
    (productElement (shieldBlock rho U i j) f g)
  K * indexedPrivateDit rho U * Kᴴ

/-- Data and exact success identity used by both quantitative conclusions.
Every positivity, probability domain and Cauchy--Schwarz bound is a conclusion. -/
def PairConclusion {N d : ℕ} {S : Fin N → ℕ}
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ)
    (U : Fin d → Matrix.unitaryGroup (PartyBasis S) ℂ) (i j : Fin d)
    (f g : ProductVectors S) : Prop :=
  let eta := productOverlap (shieldBlock rho U i j)
  let a := privateDiagonalWeight rho U i f
  let b := privateDiagonalWeight rho U j g
  let p := phaseParameter eta a b
  let q := filterSuccess d a b
  0 < eta ∧ 0 < a ∧ 0 < b ∧ eta ≤ Real.sqrt (a * b) ∧
  0 < q ∧ q ≤ 1 ∧ 1 / 2 < p ∧ p ≤ 1 ∧
  (∀ k, (1 - (localFilter i j f g a b
    (productElement (shieldBlock rho U i j) f g) k)ᴴ *
      localFilter i j f g a b (productElement (shieldBlock rho U i j) f g) k).PosSemidef) ∧
  filteredBranch rho U i j f g = (q : ℂ) • twoPhaseGHZMixture N d i j p ∧
  (filteredBranch rho U i j f g).trace.re = q ∧
  0 < filterYield d eta a b ∧
  ENNReal.ofReal (filterYield d eta a b) ≤
    distillableGHZ (fun k => d * S k) (indexedPrivateDit rho U)

/-- Distinct ordered key pairs; the domain is nonempty at d>=2. -/
abbrev KeyPair (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}

/-- PDF p.3: the finite maximum over all key pairs for the chosen maximizing
vectors. The finite nonempty domain at d>=2 guards the real supremum. -/
def bestPairYield {N d : ℕ} {S : Fin N → ℕ}
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ)
    (U : Fin d → Matrix.unitaryGroup (PartyBasis S) ℂ)
    (v : KeyPair d → ProductVectors S × ProductVectors S) : ℝ :=
  sSup (Set.range fun p : KeyPair d => filterYield d
    (productOverlap (shieldBlock rho U p.val.1 p.val.2))
    (privateDiagonalWeight rho U p.val.1 (v p).1)
    (privateDiagonalWeight rho U p.val.2 (v p).2))

/-- Bipartite private constructor, with the accepted exact block formula.
Only the parentheses and the two fixed local bases are changed; each shield
stays with its owner. Raw twists allow the explicitly computed tensor twists
below to be checked for unitarity in the tensor-closure conclusion. -/
def bipartitePrivateRaw {d a b : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (U : Fin d → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Matrix (Fin (d * a) × Fin (d * b)) (Fin (d * a) × Fin (d * b)) ℂ :=
  fun x y =>
    let xa := (localIndex d a).symm x.1
    let xb := (localIndex d b).symm x.2
    let ya := (localIndex d a).symm y.1
    let yb := (localIndex d b).symm y.2
    Information100.P67.privateState U rho
      (xa.1, (xa.2, (xb.1, xb.2))) (ya.1, (ya.2, (yb.1, yb.2)))

/-- PDF pp.1,4: the physical bipartite private state; rho is normalized in uses. -/
def bipartitePrivate {d a b : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (U : Fin d → Matrix.unitaryGroup (Fin a × Fin b) ℂ) :=
  bipartitePrivateRaw rho (fun i => (U i : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ))

/-- Fixed bipartite-to-partywise adapter, with party 0 Alice and party 1 Bob. -/
def asTwoParties {a b : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Matrix (PartyBasis ![a, b]) (PartyBasis ![a, b]) ℂ :=
  fun x y => rho (x 0, x 1) (y 0, y 1)

/-- PDF pp.2,4: ordinary Bell-pair distillability, the two-party specialization. -/
def bipartiteDistillable {a b : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ≥0∞ :=
  distillableGHZ ![a, b] (asTwoParties rho)

/-- PDF p.4: private-key rate, using deterministic accepted finite LOCC maps,
full trace norm and arbitrary positive finite output shields at every n.
The denominator counts input copies and the numerator counts only key bits.
All sufficiently large positive n are covered; no optimal sequence is assumed. -/
def KeyAchievable {a b : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ,
  ∀ n : ℕ, n0 ≤ n → 0 < n →
  ∃ d s t : ℕ, 0 < d ∧ 0 < s ∧ 0 < t ∧
  ∃ tau : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ, IsDensityMatrix tau ∧
  ∃ U : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ,
  ∃ L : Superop (Fin (a ^ n) × Fin (b ^ n)) (Fin (d * s) × Fin (d * t)),
    Information100.P21.FiniteLOCC L ∧
    traceNorm (L (Dependency50.P42.dimensionedPower rho n) - bipartitePrivate tau U) ≤ epsilon ∧
    r - delta ≤ Real.logb 2 d / n

/-- PDF pp.3--4: operational distillable key, including rate zero. -/
def distillableKey {a b : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // KeyAchievable rho r}, ENNReal.ofReal r.val

/-- PDF p.4: regroup key and shield copy tuples without changing either owner. -/
def regroupIndex (d a m : ℕ) : Fin (d ^ m * a ^ m) → Fin ((d * a) ^ m) :=
  fun x =>
    let z := (localIndex (d ^ m) (a ^ m)).symm x
    Dependency50.P42.copyIndex (d * a) m (fun t => localIndex d a
      ((Dependency50.P42.copyIndex d m).symm z.1 t,
       (Dependency50.P42.copyIndex a m).symm z.2 t))

/-- PDF p.4: the computed twist for a key tuple, not an existential new twist. -/
def tensorTwists {d a b : ℕ}
    (U : Fin d → Matrix.unitaryGroup (Fin a × Fin b) ℂ) (m : ℕ) :
    Fin (d ^ m) → Matrix (Fin (a ^ m) × Fin (b ^ m)) (Fin (a ^ m) × Fin (b ^ m)) ℂ :=
  fun key x y => ∏ t : Fin m,
    (U ((Dependency50.P42.copyIndex d m).symm key t) :
      Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
      ((Dependency50.P42.copyIndex a m).symm x.1 t,
       (Dependency50.P42.copyIndex b m).symm x.2 t)
      ((Dependency50.P42.copyIndex a m).symm y.1 t,
       (Dependency50.P42.copyIndex b m).symm y.2 t)

/-- Sanity: no-copy party power is the scalar-one entry. -/
example {N : ℕ} {D : Fin N → ℕ} (rho : Matrix (PartyBasis D) (PartyBasis D) ℂ)
    (x y : PartyBasis (fun k => D k ^ 0)) : partyPower rho 0 x y = 1 := by
  simp [partyPower]

/-- Sanity: the bipartite adapter keeps the off-diagonal entries on the same cut. -/
example {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (x y : PartyBasis ![a, b]) : asTwoParties rho x y = rho (x 0, x 1) (y 0, y 1) := rfl

/-- Sanity: vanishing coherence gives the unbiased phase mixture. -/
example (a b : ℝ) : phaseParameter 0 a b = 1 / 2 := by
  simp [phaseParameter]

/-- Sanity: unit diagonal weights yield success 2/d, including d=2. -/
example (d : ℕ) : filterSuccess d 1 1 = 2 / (d : ℝ) := by
  simp [filterSuccess]

/-- Sanity: the plus endpoint is the pure GHZ target. -/
example (N d : ℕ) (i j : Fin d) :
    twoPhaseGHZMixture N d i j 1 = pureDensity (twoLabelGHZVector N d i j false) := by
  simp [twoPhaseGHZMixture]

/-- Sanity: the computed tensor twist is the empty product at zero copies. -/
example {d a b : ℕ} (U : Fin d → Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (key : Fin (d ^ 0)) (x y : Fin (a ^ 0) × Fin (b ^ 0)) :
    tensorTwists U 0 key x y = 1 := by
  simp [tensorTwists]

/-- Sanity: a deterministic LOCC conversion is already a positive selected branch. -/
example {N : ℕ} (D E : Fin N → ℕ)
    (rho : Matrix (PartyBasis D) (PartyBasis D) ℂ)
    (sigma : Matrix (PartyBasis E) (PartyBasis E) ℂ) (h : CanConvert D E rho sigma) :
    CanSelect D E rho sigma := by
  rcases h with ⟨hD, hE, hrho, hsigma, hL⟩
  exact ⟨hD, hE, hrho, hsigma, [(1, ⟨E, hE, sigma, hsigma⟩)], hL,
    1, by norm_num, by simp⟩

end

end QAlgorithms.Papers.Independent.Gap48.P42


