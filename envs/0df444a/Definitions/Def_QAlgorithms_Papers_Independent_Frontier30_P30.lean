-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30
-- name    : QAlgorithms_Papers_Independent_Frontier30_P30
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:29:50.931321+00:00
-- url     : https://prove2.me/theorems/6ea73c6f-9782-46ad-97b2-545c01f62bc6
-- title:
--   Definitions for Locking entanglement measures with a single qubit
-- statement:
--   The objects the formalized statements of *Locking entanglement measures with a single qubit* (arXiv:quant-ph/0404096) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `densityMix`: PDF p.3: binary density-operator mixing, with p multiplying the first state. This is distinct from the accepted mixture of whole POVMs.
--   - `eraseFlag`: PDF p.2: erase Alice's qubit in the cut (flag,A'):B.
--   - `dephaseFlag`: PDF p.1: complete computational measurement of Alice's flag, outcome forgotten.
--   - `measureFlag`: PDF p.2, Proposition 1: columns of U give every orthonormal qubit basis. The corresponding two rank-one projectors act only on Alice's flag.
--   - `flaggedLogNegativity`: PDF pp.1--2: reuse the accepted logarithmic negativity after undoing partyCut's coordinate permutation. The physical bipartition remains Alice's flag+shield versus Bob's flag+shield; the imported definition transposes Bob.
--   - `relativeE`: PDF p.2: the accepted base-two relative entropy of entanglement, projected to a real. On density states in positive finite dimensions its value is finite: the full-rank product maximally mixed state is a feasible comparison state.
--   - `dimensioned`: PDF pp.1--2: fixed local relabeling to accepted LOCC's natural dimensions.
--   - `operationalEc`: PDF pp.1--2: operational asymptotic singlet formation cost. The imported alternativeCost is the infimum of eventually achievable rates: every positive error/rate tolerance admits evaluated finite LOCC preparation for every sufficiently large independent-copy block from m singlets with m/n near the rate. The distance here is full trace norm. Feasible rates are nonempty and nonnegative for density states in positive finite local dimensions; only those arguments are used.
--   - `flower`: PDF p.1, (1)--(2): accepted Hadamard flower across flag+shield:flag+shield. Purification (2) fixes local dimension 2d, correcting the printed d+2.
--   - `Functional`: PDF p.3: one functional family over all finite dimensions.
--   - `ApproximateAffinity`: PDF p.3, Proposition 2: the same defect bound for every dimension and weight.
--   - `Subextensive`: PDF p.3: absolute subextensivity, with M uniform over all systems and states.
--   - `NonAsymptoticallyContinuous`: PDF p.3, (17): a subsequential witness, with growing dimensions, vanishing full trace norm, and a fixed positive normalized gap. Requiring d>=2 discards only an initial segment of a growing witness and avoids division by log 1.
--   - `EntanglementFunctional`: PDF pp.3--4: a bipartite resource on all finite local dimensions.
--   - `instrumentBranchMean`: PDF p.4: mean resource in an unnormalized instrument branch. Zero-probability branches contribute zero, without evaluating E on a purported normalized zero state.
--   - `IsLOCCMonotone`: PDF pp.3--4: nonnegative selective LOCC monotonicity. Arbitrary complete rectangular local Kraus instruments may change local dimension. With convexity, resolved Kraus outcomes also cover coarse instruments; iteration covers adaptive communication. Local pure ancillas and disposal are included. Flagged affinity (19) is a consequence to prove, never a field of this definition.
--   - `IsConvex`: PDF p.4: convexity under every binary density-state mixture.
--   - `EntanglementSubextensive`: PDF pp.3--4: uniform subextensivity in total bipartite Hilbert dimension.
--   - `EntanglementNoncontinuous`: PDF p.3, (17): noncontinuity witnessed on one common cut at each index.
--   - `flagEquiv`: PDF p.4: fixed coordinate identification for Alice's added qubit.
--   - `flagged`: PDF p.4, (20): a classical local flag, p on the first state.
--   - `eraseDimensionedFlag`: PDF p.4, (21): evaluated partial trace over Alice's added flag.
--   - `AdmitsLocking`: PDF p.4, (20)--(22): arbitrarily large loss on erasing one local classical flag, without requiring zero post-erasure entanglement.
--   - `renyiRoof`: PDF p.4: convex roof of one pure-state marginal's Renyi entropy over every finite normalized pure ensemble. The accepted entropy uses support rank at zero.
--   - `qubitProbability`: PDF p.4: explicit nonuniform spectrum realizing the typical-state example.
--   - `qubitCopies`: PDF p.4: independent copies, with original ambient dimension 2^n.
--   - `witnessEntropy`: PDF p.4: entropy in bits of the fixed nonuniform spectral witness. This constant is distinct from the accepted two-parameter qubit entropy function.
--   - `keptWeight`: PDF p.4: retain the shrinking per-copy surprisal window n^(-1/4). At n=0 retain the single empty-product eigenvalue.
--   - `typicalCopies`: PDF p.4: normalized spectral truncation in the same ambient space. Empty retained support falls back to the original state; this does not affect limits.
-- source:
--   Locking entanglement measures with a single qubit, arXiv:quant-ph/0404096v1, https://arxiv.org/abs/quant-ph/0404096v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

/-! Statements from arXiv:quant-ph/0404096v1. All citations are PDF pages.
The incompatible, nonpositive printed Werner family (4)--(6) is deferred.
Only pinned accepted modules are imported; every new definition is paper-local. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate
open Filter
open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

/- Reuse the accepted finite complex operator alias. -/
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/- PDF pp.1--4: reuse the accepted logarithm in bits. -/
open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- PDF p.3: binary density-operator mixing, with p multiplying the first state.
This is distinct from the accepted mixture of whole POVMs. -/
def densityMix {I : Type} (p : ℝ) (rho sigma : Op I) : Op I :=
  (p : ℂ) • rho + ((1-p : ℝ) : ℂ) • sigma

/-- PDF p.2: erase Alice's qubit in the cut (flag,A'):B. -/
def eraseFlag {A B : Type} (rho : Op ((Fin 2 × A) × B)) : Op (A × B) :=
  fun x y => ∑ q : Fin 2, rho ((q,x.1),x.2) ((q,y.1),y.2)

/-- PDF p.1: complete computational measurement of Alice's flag, outcome forgotten. -/
def dephaseFlag {A B : Type} (rho : Op ((Fin 2 × A) × B)) : Op ((Fin 2 × A) × B) :=
  fun x y => if x.1.1 = y.1.1 then rho x y else 0

/-- PDF p.2, Proposition 1: columns of U give every orthonormal qubit basis.
The corresponding two rank-one projectors act only on Alice's flag. -/
def measureFlag {A B : Type} [Fintype A] [Fintype B]
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (rho : Op ((Fin 2 × A) × B)) :
    Op ((Fin 2 × A) × B) :=
  ∑ q : Fin 2,
    let P : Op (Fin 2) := fun i j => (U : Op (Fin 2)) i q * conj ((U : Op (Fin 2)) j q)
    let L := Matrix.kronecker (Matrix.kronecker P (1 : Op A)) (1 : Op B)
    L * rho * Lᴴ

/-- PDF pp.1--2: reuse the accepted logarithmic negativity after undoing
partyCut's coordinate permutation. The physical bipartition remains Alice's
flag+shield versus Bob's flag+shield; the imported definition transposes Bob. -/
def flaggedLogNegativity {A B : Type} [Fintype A] [Fintype B]
    (rho : Op ((Fin 2 × A) × (Fin 2 × B))) : ℝ :=
  Dependency50.P24.logNegativity (d := 2) (S := A) (T := B) (fun x y =>
    rho ((x.1.1,x.2.1),(x.1.2,x.2.2)) ((y.1.1,y.2.1),(y.1.2,y.2.2)))

/-- PDF p.2: the accepted base-two relative entropy of entanglement, projected
to a real. On density states in positive finite dimensions its value is finite:
the full-rank product maximally mixed state is a feasible comparison state. -/
def relativeE {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) : ℝ :=
  (Information100.P54.relativeEntanglement rho).toReal

/-- PDF pp.1--2: fixed local relabeling to accepted LOCC's natural dimensions. -/
def dimensioned {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) :
    Op (Fin (Fintype.card A) × Fin (Fintype.card B)) :=
  fun x y => rho ((Fintype.equivFin A).symm x.1,(Fintype.equivFin B).symm x.2)
    ((Fintype.equivFin A).symm y.1,(Fintype.equivFin B).symm y.2)

/-- PDF pp.1--2: operational asymptotic singlet formation cost. The imported
alternativeCost is the infimum of eventually achievable rates: every positive
error/rate tolerance admits evaluated finite LOCC preparation for every sufficiently
large independent-copy block from m singlets with m/n near the rate. The distance
here is full trace norm. Feasible rates are nonempty and nonnegative for density
states in positive finite local dimensions; only those arguments are used. -/
def operationalEc {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  Dependency50.P42.alternativeCost (fun _ _ X Y => traceNorm (X-Y)) (dimensioned rho)

/-- PDF p.1, (1)--(2): accepted Hadamard flower across flag+shield:flag+shield.
Purification (2) fixes local dimension 2d, correcting the printed d+2. -/
def flower (ell : ℕ) : Op ((Fin 2 × Fin (2^ell)) × (Fin 2 × Fin (2^ell))) :=
  Dependency50.P24.partyCut (Dependency50.P24.flowerPrivate ell)

/-- PDF p.3: one functional family over all finite dimensions. -/
abbrev Functional := (d : ℕ) → Op (Fin d) → ℝ

/-- PDF p.3, Proposition 2: the same defect bound for every dimension and weight. -/
def ApproximateAffinity (f : Functional) (c : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ rho sigma : Op (Fin d),
    IsDensityMatrix rho → IsDensityMatrix sigma → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    |p*f d rho + (1-p)*f d sigma - f d (densityMix p rho sigma)| ≤ c

/-- PDF p.3: absolute subextensivity, with M uniform over all systems and states. -/
def Subextensive (f : Functional) (M : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ rho : Op (Fin d), IsDensityMatrix rho → |f d rho| ≤ M * log2 d

/-- PDF p.3, (17): a subsequential witness, with growing dimensions, vanishing
full trace norm, and a fixed positive normalized gap. Requiring d>=2 discards
only an initial segment of a growing witness and avoids division by log 1. -/
def NonAsymptoticallyContinuous (f : Functional) : Prop :=
  ∃ d : ℕ → ℕ, ∃ rho sigma : (n : ℕ) → Op (Fin (d n)), ∃ gap : ℝ,
    0 < gap ∧ (∀ n, 2 ≤ d n ∧ IsDensityMatrix (rho n) ∧ IsDensityMatrix (sigma n)) ∧
    Tendsto (fun n => (d n : ℝ)) atTop atTop ∧
    Tendsto (fun n => traceNorm (rho n-sigma n)) atTop (nhds 0) ∧
    ∀ n, gap * log2 (d n) ≤ |f (d n) (rho n)-f (d n) (sigma n)|

/-- PDF pp.3--4: a bipartite resource on all finite local dimensions. -/
abbrev EntanglementFunctional := (a b : ℕ) → Op (Fin a × Fin b) → ℝ

/-- PDF p.4: mean resource in an unnormalized instrument branch. Zero-probability branches
contribute zero, without evaluating E on a purported normalized zero state. -/
def instrumentBranchMean (E : EntanglementFunctional) {a b : ℕ} (X : Op (Fin a × Fin b)) : ℝ :=
  let p := X.trace.re
  if 0 < p then p * E a b (((p⁻¹ : ℝ) : ℂ) • X) else 0

/-- PDF pp.3--4: nonnegative selective LOCC monotonicity. Arbitrary complete
rectangular local Kraus instruments may change local dimension. With convexity,
resolved Kraus outcomes also cover coarse instruments; iteration covers adaptive
communication. Local pure ancillas and disposal are included. Flagged affinity
(19) is a consequence to prove, never a field of this definition. -/
def IsLOCCMonotone (E : EntanglementFunctional) : Prop :=
  (∀ a b : ℕ, 0 < a → 0 < b → ∀ rho : Op (Fin a × Fin b),
    IsDensityMatrix rho → 0 ≤ E a b rho) ∧
  (∀ a b h k : ℕ, 0 < a → 0 < b → 0 < h →
    ∀ K : Fin k → Matrix (Fin h) (Fin a) ℂ, IsKrausFamily K →
    ∀ rho : Op (Fin a × Fin b), IsDensityMatrix rho →
      (∑ i, instrumentBranchMean E ((Matrix.kronecker (K i) (1 : Op (Fin b)) * rho) *
        (Matrix.kronecker (K i) (1 : Op (Fin b)))ᴴ)) ≤ E a b rho) ∧
  (∀ a b h k : ℕ, 0 < a → 0 < b → 0 < h →
    ∀ K : Fin k → Matrix (Fin h) (Fin b) ℂ, IsKrausFamily K →
    ∀ rho : Op (Fin a × Fin b), IsDensityMatrix rho →
      (∑ i, instrumentBranchMean E ((Matrix.kronecker (1 : Op (Fin a)) (K i) * rho) *
        (Matrix.kronecker (1 : Op (Fin a)) (K i))ᴴ)) ≤ E a b rho)

/-- PDF p.4: convexity under every binary density-state mixture. -/
def IsConvex (E : EntanglementFunctional) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → ∀ rho sigma : Op (Fin a × Fin b),
    IsDensityMatrix rho → IsDensityMatrix sigma → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    E a b (densityMix p rho sigma) ≤ p*E a b rho + (1-p)*E a b sigma

/-- PDF pp.3--4: uniform subextensivity in total bipartite Hilbert dimension. -/
def EntanglementSubextensive (E : EntanglementFunctional) (M : ℝ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → ∀ rho : Op (Fin a × Fin b),
    IsDensityMatrix rho → E a b rho ≤ M * log2 ((a : ℝ)*b)

/-- PDF p.3, (17): noncontinuity witnessed on one common cut at each index. -/
def EntanglementNoncontinuous (E : EntanglementFunctional) : Prop :=
  ∃ a b : ℕ → ℕ, ∃ rho sigma : (n : ℕ) → Op (Fin (a n) × Fin (b n)),
    ∃ gap : ℝ, 0 < gap ∧
    (∀ n, 0 < a n ∧ 0 < b n ∧ 2 ≤ a n*b n ∧
      IsDensityMatrix (rho n) ∧ IsDensityMatrix (sigma n)) ∧
    Tendsto (fun n => (a n : ℝ)*(b n : ℝ)) atTop atTop ∧
    Tendsto (fun n => traceNorm (rho n-sigma n)) atTop (nhds 0) ∧
    ∀ n, gap * log2 ((a n : ℝ)*b n) ≤ |E (a n) (b n) (rho n)-E (a n) (b n) (sigma n)|

/-- PDF p.4: fixed coordinate identification for Alice's added qubit. -/
def flagEquiv (a : ℕ) : (Fin 2 × Fin a) ≃ Fin (2*a) :=
  Fintype.equivFinOfCardEq (by simp)

/-- PDF p.4, (20): a classical local flag, p on the first state. -/
def flagged {a b : ℕ} (p : ℝ) (rho sigma : Op (Fin a × Fin b)) : Op (Fin (2*a) × Fin b) :=
  fun x y =>
    let u := (flagEquiv a).symm x.1
    let v := (flagEquiv a).symm y.1
    if u.1 = v.1 then
      if u.1 = 0 then (p : ℂ)*rho (u.2,x.2) (v.2,y.2)
      else ((1-p : ℝ) : ℂ)*sigma (u.2,x.2) (v.2,y.2)
    else 0

/-- PDF p.4, (21): evaluated partial trace over Alice's added flag. -/
def eraseDimensionedFlag {a b : ℕ} (X : Op (Fin (2*a) × Fin b)) : Op (Fin a × Fin b) :=
  fun x y => ∑ q : Fin 2, X (flagEquiv a (q,x.1),x.2) (flagEquiv a (q,y.1),y.2)

/-- PDF p.4, (20)--(22): arbitrarily large loss on erasing one local classical
flag, without requiring zero post-erasure entanglement. -/
def AdmitsLocking (E : EntanglementFunctional) : Prop :=
  ∀ loss : ℝ, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    ∃ rho sigma : Op (Fin a × Fin b), IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ IsDensityMatrix (flagged p rho sigma) ∧
      loss < E (2*a) b (flagged p rho sigma) - E a b (eraseDimensionedFlag (flagged p rho sigma))

/-- PDF p.4: convex roof of one pure-state marginal's Renyi entropy over every
finite normalized pure ensemble. The accepted entropy uses support rank at zero. -/
def renyiRoof (alpha : ℝ) : EntanglementFunctional :=
  fun _ _ rho => Information100.P03.convexRoof
    (fun v => Dependency50.P05.renyiEntropy alpha (traceRight (pureDensity v))) rho

/-- PDF p.4: explicit nonuniform spectrum realizing the typical-state example. -/
def qubitProbability (i : Fin 2) : ℝ := if i = 0 then 1/4 else 3/4

/-- PDF p.4: independent copies, with original ambient dimension 2^n. -/
def qubitCopies (n : ℕ) : Op (Fin n → Fin 2) :=
  Matrix.diagonal fun x => ((∏ i, qubitProbability (x i) : ℝ) : ℂ)

/-- PDF p.4: entropy in bits of the fixed nonuniform spectral witness.
This constant is distinct from the accepted two-parameter qubit entropy function. -/
def witnessEntropy : ℝ := -∑ i : Fin 2, qubitProbability i * log2 (qubitProbability i)

/-- PDF p.4: retain the shrinking per-copy surprisal window n^(-1/4).
At n=0 retain the single empty-product eigenvalue. -/
def keptWeight (n : ℕ) (x : Fin n → Fin 2) : ℝ :=
  let w := ∏ i, qubitProbability (x i)
  if n = 0 ∨ |(-log2 w)/(n : ℝ)-witnessEntropy| ≤ (n : ℝ)^(-(1/4 : ℝ)) then w else 0

/-- PDF p.4: normalized spectral truncation in the same ambient space. Empty
retained support falls back to the original state; this does not affect limits. -/
def typicalCopies (n : ℕ) : Op (Fin n → Fin 2) :=
  let mass := ∑ x, keptWeight n x
  if mass = 0 then qubitCopies n
  else Matrix.diagonal fun x => ((keptWeight n x / mass : ℝ) : ℂ)

/-- Sanity: p=0 selects the second density. -/
example {I : Type} (rho sigma : Op I) : densityMix 0 rho sigma = sigma := by simp [densityMix]

/-- Sanity: an off-diagonal flag block is removed, without postselection. -/
example {A B : Type} (X : Op ((Fin 2 × A) × B)) (a a2 : A) (b b2 : B) :
    dephaseFlag X ((0,a),b) ((1,a2),b2) = 0 := by simp [dephaseFlag]

/-- Sanity: an impossible branch has zero contribution. -/
example (E : EntanglementFunctional) {a b : ℕ} : instrumentBranchMean E (0 : Op (Fin a × Fin b)) = 0 := by
  simp [instrumentBranchMean]

/-- Sanity: adding the local coordinate identification preserves its indices. -/
example (a : ℕ) (q : Fin 2) (i : Fin a) : (flagEquiv a).symm (flagEquiv a (q,i)) = (q,i) :=
  (flagEquiv a).symm_apply_apply (q,i)

/-- Sanity: the zero-copy scalar eigenvalue survives truncation. -/
example (x : Fin 0 → Fin 2) : keptWeight 0 x = 1 := by simp [keptWeight]

end QAlgorithms.Papers.Independent.Frontier30.P30


