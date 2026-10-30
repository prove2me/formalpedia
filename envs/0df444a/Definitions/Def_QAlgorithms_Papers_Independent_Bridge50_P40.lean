-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40
-- name    : QAlgorithms_Papers_Independent_Bridge50_P40
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:54:08.728011+00:00
-- url     : https://prove2.me/theorems/574f1875-4662-480a-a506-fc4d1ed78082
-- title:
--   Definitions for A strong converse for the quantum state merging protocol
-- statement:
--   The objects the formalized statements of *A strong converse for the quantum state merging protocol* (arXiv:1404.5940) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `entropyInfinity`: PDF p.6, (23): infinite-order entropy is minus log of the largest eigenvalue. For densities on nonempty finite registers the range is nonempty and bounded. The value on non-Hermitian matrices is unused.
--   - `reciprocalEntropy`: PDF pp.7--9: the order 1/(2-a), with the infinite-order endpoint at a=2.
--   - `rree`: PDF p.4, (8): finite-valued RREE, as the infimum of finite real upper bounds on Petz divergence over separable density matrices. For normalized inputs and 0 <= a <= 2 this set is nonempty (the full-rank maximally mixed product comparison has finite divergence) and bounded below by zero. This formulation neither totalizes an infinite divergence to zero nor assumes an attained minimizer.
--   - `TypedLocalInstrument`: PDF p.5, Lemma 3: the frozen finite Kraus instrument, in arbitrary register bases and with its outcome count fixed to the flag alphabet's cardinality. Completeness and the private Kraus index are imported, not redeclared.
--   - `TypedLocalInstrument.kraus`: PDF p.5: basis transport of the imported Kraus matrices and outcome label. This changes no matrix block and communicates no private Kraus index.
--   - `TypedLocalInstrument.branch`: PDF p.5: the unnormalized branch acts on every spectator-B matrix block.
--   - `TypedLocalInstrument.weight`: PDF p.5: outcome probability is the trace of the computed branch.
--   - `TypedLocalInstrument.normalized`: PDF p.5: normalize a positive-probability branch. At zero probability use a fixed pure density, whose weighted RREE contribution is zero.
--   - `TypedLocalInstrument.flagged`: PDF p.5, (10): the actual flag on Alice's side, grouped as (X C):B. No division by the branch probability enters this density.
--   - `cqCoherentConditional`: PDF p.13, (65), using p.3 (5): S_a(R|X)=-I_a(X coherent-to R). Trace R (the first physical register), retaining X, after powering the joint state. This is not a difference of joint and marginal Renyi entropies.
--   - `rankMergingInput`: PDF pp.8--9: a single-copy source is in R:(A B) order; its n-copy input contains the supplied arbitrary-Schmidt-rank Bell resource.
--   - `rankMergingTarget`: PDF p.8, (36): the complete pure target retains R and the final Bell pair; Bob holds the reconstructed A register and his original B register.
--   - `mergingFidelity`: PDF p.8, Definition 1: actual complete-output root fidelity. The physical operation is extended by identity on every off-diagonal reference block.
--   - `RankMergingCode`: PDF p.8: an adaptive LOCC protocol. K and L are ranks, not qubit counts. The pinned LOCC definition has arbitrary finite outcome-dependent local rounds, rectangular Kraus operators, ancillas and disposal.
--   - `RankMergingCode.rate`: PDF p.8: signed REAL ebit consumption per input copy.
--   - `OneWayMergingCode`: PDF pp.9--10: one-way Alice-to-Bob merging, with a classical outcome and an uncharged private Kraus environment. Arbitrary positive resource ranks.
--   - `OneWayMergingCode.operation`: PDF p.9, (46), Definition 1: sum over the same classical outcome at both parties. Unlike the bookkeeping omission in (47), the fidelity input below still contains Phi_K. The source and target formulas are unchanged.
--   - `OneWayMergingCode.rate`: PDF p.9, (45): logarithm of alphabet size divided by block length.
--   - `concentrationInput`: PDF p.11: n independent copies, regrouped by laboratory, without an additional supplied entanglement resource.
--   - `compressionInput`: PDF pp.11--12, Definition 3: tensor copies of the same purification, grouped R:A before the physical compression channel.
--   - `compressionFidelity`: PDF p.12, (60): reference-entangled root fidelity of arbitrary CPTP compression/decompression, with A1 identified by its specified basis with A.
--   - `SourceProtocolAchievable`: PDF pp.8,11: a rate is achievable when actual positive-block protocols have rates tending to it and complete-output root fidelities tending to one. The zero-copy entry is immaterial; no supremum or empty-set default is used.
--   - `MergingRateFidelity`: PDF p.8, Definition 1: rate and fidelity must be computed from the SAME actual arbitrary-rank LOCC merging protocol on the fixed source.
--   - `ConcentrationRateFidelity`: PDF p.11, Definition 2: actual concentration on the fixed pure source; no initial resource, arbitrary positive target rank, and root fidelity.
--   - `CompressionRateFidelity`: PDF pp.11--12, Definition 3: arbitrary CPTP encoder and decoder through an arbitrary positive dimension d. Fin d is only a basis choice.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, https://arxiv.org/abs/1404.5940v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

/-!
Naresh Sharma, arXiv:1404.5940v1. All citations use PDF pages.
The independent-paper override permits the pinned accepted-paper imports.
Only their definitions are reused. No background theorem is assumed.
Renyi entropy, cq matrices, and finite Kraus instruments use pinned definitions.
The arbitrary-rank merging models differ from the frozen qubit-count models.
All logarithms are base two and fidelity is root fidelity.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Information100.P22 (bell)
open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)
open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)
open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, (23): infinite-order entropy is minus log of the largest eigenvalue.
For densities on nonempty finite registers the range is nonempty and bounded.
The value on non-Hermitian matrices is unused. -/
def entropyInfinity {I : Type} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) : ℝ :=
  if h : rho.IsHermitian then -Real.logb 2 (sSup (Set.range h.eigenvalues)) else 0

/-- PDF pp.7--9: the order 1/(2-a), with the infinite-order endpoint at a=2. -/
def reciprocalEntropy {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho : Matrix I I ℂ) : ℝ :=
  if a = 2 then entropyInfinity rho else renyiEntropy (1 / (2 - a)) rho

/-- PDF p.4, (8): finite-valued RREE, as the infimum of finite real upper
bounds on Petz divergence over separable density matrices. For normalized inputs
and 0 <= a <= 2 this set is nonempty (the full-rank maximally mixed product
comparison has finite divergence) and bounded below by zero. This formulation
neither totalizes an infinite divergence to zero nor assumes an attained minimizer. -/
def rree {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (a : ℝ) (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {r : ℝ | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    Entanglement.IsSeparableDensity sigma ∧
      (if a = 1 then QAlgorithms.Papers.Independent.Dependency50.P09.relativeD rho sigma
       else QAlgorithms.Papers.Independent.Dependency50.P09.petzD a rho sigma) ≤ (r : EReal)}

/-- PDF p.5, Lemma 3: the frozen finite Kraus instrument, in arbitrary
register bases and with its outcome count fixed to the flag alphabet's cardinality.
Completeness and the private Kraus index are imported, not redeclared. -/
def TypedLocalInstrument (A C X : Type) [Fintype A] [Fintype C] [Fintype X] :=
  {E : QAlgorithms.Papers.Independent.Information100.P08.Instrument
    (Fintype.card A) (Fintype.card C) // E.outcomes = Fintype.card X}

/-- PDF p.5: basis transport of the imported Kraus matrices and outcome label.
This changes no matrix block and communicates no private Kraus index. -/
def TypedLocalInstrument.kraus {A C X : Type} [Fintype A] [Fintype C] [Fintype X]
    (E : TypedLocalInstrument A C X) (x : X) (e : Fin E.val.rank) : Matrix C A ℂ :=
  fun c a => E.val.kraus (Fin.cast E.property.symm (Fintype.equivFin X x)) e
    (Fintype.equivFin C c) (Fintype.equivFin A a)

/-- PDF p.5: the unnormalized branch acts on every spectator-B matrix block. -/
def TypedLocalInstrument.branch {A C X B : Type} [Fintype A] [Fintype C] [Fintype X]
    (E : TypedLocalInstrument A C X) (x : X) : Superop (A × B) (C × B) :=
  fun rho p q => krausApply (E.kraus x)
    (fun a b => rho (a, p.2) (b, q.2)) p.1 q.1

/-- PDF p.5: outcome probability is the trace of the computed branch. -/
def TypedLocalInstrument.weight {A C X B : Type} [Fintype A] [Fintype C] [Fintype X]
    [Fintype B] (E : TypedLocalInstrument A C X) (rho : Matrix (A × B) (A × B) ℂ)
    (x : X) : ℝ := (E.branch x rho).trace.re

/-- PDF p.5: normalize a positive-probability branch. At zero probability use a
fixed pure density, whose weighted RREE contribution is zero. -/
def TypedLocalInstrument.normalized {A C X B : Type} [Fintype A] [Fintype C] [Fintype X]
    [Fintype B] [Nonempty C] [Nonempty B] (E : TypedLocalInstrument A C X)
    (rho : Matrix (A × B) (A × B) ℂ) (x : X) : Matrix (C × B) (C × B) ℂ :=
  if E.weight rho x = 0 then pureDensity (ket (Classical.choice (inferInstance : Nonempty (C × B))))
  else ((E.weight rho x)⁻¹ : ℂ) • E.branch x rho

/-- PDF p.5, (10): the actual flag on Alice's side, grouped as (X C):B.
No division by the branch probability enters this density. -/
def TypedLocalInstrument.flagged {A C X B : Type} [Fintype A] [Fintype C] [Fintype X]
    (E : TypedLocalInstrument A C X) (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix ((X × C) × B) ((X × C) × B) ℂ :=
  fun p q => if p.1.1 = q.1.1 then
    E.branch p.1.1 rho (p.1.2, p.2) (q.1.2, q.2) else 0

/-- PDF p.13, (65), using p.3 (5): S_a(R|X)=-I_a(X coherent-to R).
Trace R (the first physical register), retaining X, after powering the joint
state. This is not a difference of joint and marginal Renyi entropies. -/
def cqCoherentConditional {R X : Type} [Fintype R] [Fintype X]
    (a : ℝ) (omega : Matrix (R × X) (R × X) ℂ) : ℝ :=
  -(a / (a - 1) * Real.logb 2
    (supportPower (traceLeft (supportPower omega a)) (1 / a)).trace.re)

/-- PDF pp.8--9: a single-copy source is in R:(A B) order; its n-copy
input contains the supplied arbitrary-Schmidt-rank Bell resource. -/
def rankMergingInput {A B R : Type} (psi : EuclideanSpace ℂ (R × (A × B)))
    (n K : ℕ) : EuclideanSpace ℂ
      ((Fin n → R) × (((Fin n → A) × Fin K) × ((Fin n → B) × Fin K))) :=
  WithLp.toLp 2 fun p =>
    tensorPow n psi (fun i => (p.1 i, (p.2.1.1 i, p.2.2.1 i))) *
      bell (Fin K) (p.2.1.2, p.2.2.2)

/-- PDF p.8, (36): the complete pure target retains R and the final Bell pair;
Bob holds the reconstructed A register and his original B register. -/
def rankMergingTarget {A B R : Type} (psi : EuclideanSpace ℂ (R × (A × B)))
    (n L : ℕ) : EuclideanSpace ℂ
      ((Fin n → R) × (Fin L × (((Fin n → A) × (Fin n → B)) × Fin L))) :=
  WithLp.toLp 2 fun p =>
    tensorPow n psi (fun i => (p.1 i, (p.2.2.1.1 i, p.2.2.1.2 i))) *
      bell (Fin L) (p.2.1, p.2.2.2)

/-- PDF p.8, Definition 1: actual complete-output root fidelity. The physical
operation is extended by identity on every off-diagonal reference block. -/
def mergingFidelity {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (n K L : ℕ)
    (M : Superop (((Fin n → A) × Fin K) × ((Fin n → B) × Fin K))
      (Fin L × (((Fin n → A) × (Fin n → B)) × Fin L))) : ℝ :=
  rootFidelity (idTensorSuperop M (pureDensity (rankMergingInput psi n K)))
    (pureDensity (rankMergingTarget psi n L))

/-- PDF p.8: an adaptive LOCC protocol. K and L are ranks, not qubit counts.
The pinned LOCC definition has arbitrary finite outcome-dependent local rounds,
rectangular Kraus operators, ancillas and disposal. -/
structure RankMergingCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  K : ℕ
  L : ℕ
  K_pos : 0 < K
  L_pos : 0 < L
  operation : Superop (((Fin n → A) × Fin K) × ((Fin n → B) × Fin K))
    (Fin L × (((Fin n → A) × (Fin n → B)) × Fin L))
  locc : IsLOCC operation

/-- PDF p.8: signed REAL ebit consumption per input copy. -/
def RankMergingCode.rate {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : RankMergingCode A B n) : ℝ :=
  (Real.logb 2 P.K - Real.logb 2 P.L) / (n : ℝ)

/-- PDF pp.9--10: one-way Alice-to-Bob merging, with a classical outcome and
an uncharged private Kraus environment. Arbitrary positive resource ranks. -/
structure OneWayMergingCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  K : ℕ
  L : ℕ
  K_pos : 0 < K
  L_pos : 0 < L
  messages : ℕ
  messages_pos : 0 < messages
  alice : TypedLocalInstrument ((Fin n → A) × Fin K) (Fin L) (Fin messages)
  bob : Fin messages → Superop ((Fin n → B) × Fin K)
    (((Fin n → A) × (Fin n → B)) × Fin L)
  bob_channel : ∀ x, IsChannel (bob x)

/-- PDF p.9, (46), Definition 1: sum over the same classical outcome at both
parties. Unlike the bookkeeping omission in (47), the fidelity input below still
contains Phi_K. The source and target formulas are unchanged. -/
def OneWayMergingCode.operation {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : OneWayMergingCode A B n) :
    Superop (((Fin n → A) × Fin P.K) × ((Fin n → B) × Fin P.K))
      (Fin P.L × (((Fin n → A) × (Fin n → B)) × Fin P.L)) :=
  fun rho => ∑ x, productApply (krausApply (P.alice.kraus x)) (P.bob x) rho

/-- PDF p.9, (45): logarithm of alphabet size divided by block length. -/
def OneWayMergingCode.rate {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : OneWayMergingCode A B n) : ℝ := Real.logb 2 P.messages / (n : ℝ)

/-- PDF p.11: n independent copies, regrouped by laboratory, without an
additional supplied entanglement resource. -/
def concentrationInput {A B : Type} (psi : EuclideanSpace ℂ (A × B)) (n : ℕ) :
    EuclideanSpace ℂ ((Fin n → A) × (Fin n → B)) :=
  WithLp.toLp 2 fun p => tensorPow n psi (fun i => (p.1 i, p.2 i))

/-- PDF pp.11--12, Definition 3: tensor copies of the same purification,
grouped R:A before the physical compression channel. -/
def compressionInput {A R : Type} (psi : EuclideanSpace ℂ (R × A)) (n : ℕ) :
    EuclideanSpace ℂ ((Fin n → R) × (Fin n → A)) :=
  WithLp.toLp 2 fun p => tensorPow n psi (fun i => (p.1 i, p.2 i))

/-- PDF p.12, (60): reference-entangled root fidelity of arbitrary CPTP
compression/decompression, with A1 identified by its specified basis with A. -/
def compressionFidelity {A R B : Type} [Fintype A] [Fintype R] [Fintype B]
    (psi : EuclideanSpace ℂ (R × A)) (n : ℕ)
    (C : Superop (Fin n → A) B) (D : Superop B (Fin n → A)) : ℝ :=
  rootFidelity (idTensorSuperop (D ∘ C) (pureDensity (compressionInput psi n)))
    (pureDensity (compressionInput psi n))

/-- PDF pp.8,11: a rate is achievable when actual positive-block protocols
have rates tending to it and complete-output root fidelities tending to one.
The zero-copy entry is immaterial; no supremum or empty-set default is used. -/
def SourceProtocolAchievable (feasible : ℕ → ℝ → ℝ → Prop) (rate : ℝ) : Prop :=
  ∃ rates fidelities : ℕ → ℝ,
    (∀ n, 0 < n → feasible n (rates n) (fidelities n)) ∧
    Filter.Tendsto rates Filter.atTop (nhds rate) ∧
    Filter.Tendsto fidelities Filter.atTop (nhds 1)

/-- PDF p.8, Definition 1: rate and fidelity must be computed from the SAME
actual arbitrary-rank LOCC merging protocol on the fixed source. -/
def MergingRateFidelity {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (n : ℕ) (rate fidelity : ℝ) : Prop :=
  ∃ P : RankMergingCode A B n, rate = P.rate ∧
    fidelity = mergingFidelity psi n P.K P.L P.operation

/-- PDF p.11, Definition 2: actual concentration on the fixed pure source;
no initial resource, arbitrary positive target rank, and root fidelity. -/
def ConcentrationRateFidelity {A B : Type} [Fintype A] [Fintype B]
    (psi : EuclideanSpace ℂ (A × B)) (n : ℕ) (rate fidelity : ℝ) : Prop :=
  ∃ L : ℕ, 0 < L ∧
    ∃ M : Superop ((Fin n → A) × (Fin n → B)) (Fin L × Fin L),
      IsLOCC M ∧ rate = Real.logb 2 L / (n : ℝ) ∧
      fidelity = rootFidelity (M (pureDensity (concentrationInput psi n)))
        (pureDensity (bell (Fin L)))

/-- PDF pp.11--12, Definition 3: arbitrary CPTP encoder and decoder through
an arbitrary positive dimension d. Fin d is only a basis choice. -/
def CompressionRateFidelity {A R : Type} [Fintype A] [Fintype R]
    (psi : EuclideanSpace ℂ (R × A)) (n : ℕ) (rate fidelity : ℝ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∃ C : Superop (Fin n → A) (Fin d),
    ∃ D : Superop (Fin d) (Fin n → A),
      IsChannel C ∧ IsChannel D ∧ rate = Real.logb 2 d / (n : ℝ) ∧
      fidelity = compressionFidelity psi n C D

/-- Sanity: exact unit fidelity at a constant rate is an achievable family;
this pins the limit direction and the positive-block convention. -/
example (feasible : ℕ → ℝ → ℝ → Prop) (rate : ℝ)
    (h : ∀ n, 0 < n → feasible n rate 1) : SourceProtocolAchievable feasible rate := by
  exact ⟨fun _ => rate, fun _ => 1, h,
    tendsto_const_nhds, tendsto_const_nhds⟩

/-- Sanity: the endpoint dispatch never evaluates the reciprocal at zero. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    reciprocalEntropy 2 rho = entropyInfinity rho := by simp [reciprocalEntropy]

/-- Sanity: order one is the imported von Neumann entropy in bits. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    renyiEntropy 1 rho = vnEntropy rho := by simp [renyiEntropy, vnEntropy]

/-- Sanity: a zero-weight cq letter contributes the zero block. -/
example {R X : Type} (p : X → ℝ) (rho : X → Matrix R R ℂ)
    (x : X) (h : p x = 0) (i j : R) : cq p rho (i,x) (j,x) = 0 := by
  simp [cq, h]

/-- Sanity: rank one means a one-dimensional Bell resource of amplitude one. -/
example : bell (Fin 1) (0,0) = 1 := by simp [bell]

/-- Sanity: signed consumption allows negative values. -/
example : (Real.logb 2 (1 : ℝ) - Real.logb 2 (2 : ℝ)) / (1 : ℝ) = -1 := by
  norm_num

/-- Sanity: an unobserved reference coherence is retained by the identity channel. -/
example {R I : Type} (rho : Matrix (R × I) (R × I) ℂ) :
    idTensorSuperop (fun X : Matrix I I ℂ => X) rho = rho := by
  ext p q
  rfl

/-- Sanity: concentration has one scalar amplitude on the zero-copy register.
The block converse itself explicitly excludes this length. -/
example {A B : Type} (psi : EuclideanSpace ℂ (A × B))
    (p : (Fin 0 → A) × (Fin 0 → B)) : concentrationInput psi 0 p = 1 := by
  simp [concentrationInput, tensorPow]

/-- Sanity: the same tensor convention is used for compression and its reference. -/
example {A R : Type} (psi : EuclideanSpace ℂ (R × A))
    (p : (Fin 0 → R) × (Fin 0 → A)) : compressionInput psi 0 p = 1 := by
  simp [compressionInput, tensorPow]

/-- Sanity: distinct outcome flags have no coherence. -/
example {A C X B : Type} [Fintype A] [Fintype C] [Fintype X]
    (E : TypedLocalInstrument A C X) (rho : Matrix (A × B) (A × B) ℂ)
    (x y : X) (h : x ≠ y) (c d : C) (b e : B) :
    E.flagged rho ((x,c),b) ((y,d),e) = 0 := by
  simp [TypedLocalInstrument.flagged, h]

end QAlgorithms.Papers.Independent.Bridge50.P40


