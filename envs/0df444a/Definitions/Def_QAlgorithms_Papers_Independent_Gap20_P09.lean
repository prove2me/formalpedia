-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P09
-- name    : QAlgorithms_Papers_Independent_Gap20_P09
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T23:17:39.401009+00:00
-- url     : https://prove2.me/theorems/6068071b-c945-4556-9343-da12b5673279
-- title:
--   Definitions for Multipartite quantum correlations and local recoverability
-- statement:
--   The objects the formalized statements of *Multipartite quantum correlations and local recoverability* (arXiv:1412.0333) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `multipartiteInformationNats`: PDF p.2,(1.3): total correlation in nats; the accepted formula is in bits.
--   - `informationGap`: PDF pp.4–5,(2.1),(3.1): both marginals come from this same paired state.
--   - `multipartiteTensorAction`: PDF pp.4,6: heterogeneous tensor channel, expanded on matrix units. Both indices of every input register are retained, including entangled inputs.
--   - `recover`: PDF p.4,(2.1): the tensor of local recovery maps acts on the primed marginal.
--   - `traceRecover`: PDF p.6,(3.13): a local trace-out followed by recovery, on all operators.
--   - `subsetRecovery`: PDF p.6, Remark 2: retain identity on precisely the unselected pairs.
--   - `subsetWeight`: PDF p.6,(3.13): all-zero strings use one, avoiding division by zero.
--   - `selectUnprimed`: PDF p.5: partial trace of unselected unprimed factors, keeping ALL primed factors and both indices on every retained factor.
--   - `chainTerm`: PDF p.5,(3.1): CMI I(A_i; A_pre A'_others | A'_i), written as the four entropies H(A_i A'_i)-H(A'_i)-H(A_i A_pre A'_all)+H(A_pre A'_all). The permutation orders PAIRS, not independent permutations of their factors.
--   - `cemi`: PDF p.9,(5.1): half the infimum over every positive finite local ancillary dimension and every normalized extension. No optimizer or dimension cap is assumed.
--   - `multipartiteSquashedNats`: PDF p.12,(5.24): unrestricted-extension squashed entanglement, half-infimum of TOTAL conditional correlation, converted from the accepted bits to nats.
--   - `LocalMeasurement`: PDF p.7,(4.3): finite POVMs with arbitrary positive outcome dimension.
--   - `povmChannelAction`: PDF p.7,(4.3): complex trace on arbitrary operators, hence correct on reference off-diagonal blocks. The output basis is X, correcting the printed Ai label.
--   - `msqDiscord`: PDF p.6,(4.1): the SUPREMUM over all local finite POVMs; no attainment premise.
--   - `IsEBChannel`: PDF pp.4,7–9: finite-dimensional EB channels, equivalently a finite POVM followed by preparation of normalized states. The CPTP property is retained explicitly.
--   - `fullySeparableTraceDistance`: PDF p.20,(A.3): distance to all fully separable states on these SAME factors. The accepted predicate uses arbitrary finite mixtures of all-party mixed products.
--   - `pairedCopies`: PDF p.18,(7.1): n copies, grouped by party rather than interleaved by copy.
--   - `recoveryRelativeEntropy`: PDF p.18,(7.1): exact infimum at each blocklength; +infinity survives support failure. Minima and finite limiting value are conclusions of Proposition 7.
--   - `replicaHead`: PDF p.20,(A.2): retain the first replica of each register in the accepted replica basis. Its first party has multiplicity one; all others have k+1.
--   - `replicaMarginal`: PDF p.20,(A.2): reuse the accepted full partial trace, selecting copy zero on every party and retaining both matrix indices on the surviving registers.
--   - `IsMultipartiteExtendible`: PDF p.20,(A.2): independently permutation-INVARIANT mixed extensions. No symmetric-subspace (bosonic) support restriction is imposed.
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, https://arxiv.org/abs/1412.0333v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

/-! Wilde, arXiv:1412.0333v3. Finite, nonzero local dimensions; natural
logarithms and the full trace norm. All new definitions are paper local.
The operational nodes and three source-level obstacles are inventoried in HARD.md.
Compilation is pending the authorized batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology
open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

-- Exact accepted heterogeneous and selected-register bases; no local aliases.
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)
open QAlgorithms.Papers.Independent.Gap48.P22
  (ReplicaBasis partyCopyMultiplicity selectedReplicaMarginal)

/-- PDF p.2,(1.3): total correlation in nats; the accepted formula is in bits. -/
def multipartiteInformationNats {l : ℕ} {D : Fin l → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  Real.log 2 * QAlgorithms.Papers.Independent.Claimed50.P33.info .total rho
    (QAlgorithms.Papers.Independent.Claimed50.P33.singleParties l) ∅

/-- PDF pp.4–5,(2.1),(3.1): both marginals come from this same paired state. -/
def informationGap {l : ℕ} {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) : ℝ :=
  multipartiteInformationNats rho - multipartiteInformationNats
    (QAlgorithms.Papers.Independent.Claimed50.P33.primedMarginal rho)

/-- PDF pp.4,6: heterogeneous tensor channel, expanded on matrix units.
Both indices of every input register are retained, including entangled inputs. -/
def multipartiteTensorAction {l : ℕ} {D F : Fin l → Type} [∀ i, Fintype (D i)]
    (Phi : (i : Fin l) → Superop (D i) (F i)) : Superop (RegisterBasis D) (RegisterBasis F) :=
  fun rho a b => ∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
    rho x y * ∏ i, Phi i (Matrix.single (x i) (y i) 1) (a i) (b i)

/-- PDF p.4,(2.1): the tensor of local recovery maps acts on the primed marginal. -/
def recover {l : ℕ} {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (R : (i : Fin l) → Superop (F i) (D i × F i))
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :=
  multipartiteTensorAction R (QAlgorithms.Papers.Independent.Claimed50.P33.primedMarginal rho)

/-- PDF p.6,(3.13): a local trace-out followed by recovery, on all operators. -/
def traceRecover {A B : Type} [Fintype A]
    (R : Superop B (A × B)) : Superop (A × B) (A × B) :=
  fun X => R (traceLeft X)

/-- PDF p.6, Remark 2: retain identity on precisely the unselected pairs. -/
def subsetRecovery {l : ℕ} {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (R : (i : Fin l) → Superop (F i) (D i × F i)) (j : Fin l → Bool) :=
  multipartiteTensorAction (fun i => if j i then traceRecover (R i) else id)

/-- PDF p.6,(3.13): all-zero strings use one, avoiding division by zero. -/
def subsetWeight {l : ℕ} (j : Fin l → Bool) : ℕ :=
  max 1 ((Finset.univ.filter fun i => j i = true).card)

/-- PDF p.5: partial trace of unselected unprimed factors, keeping ALL primed
factors and both indices on every retained factor. -/
def selectUnprimed {l : ℕ} {D F : Fin l → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (s : Finset (Fin l)) : Matrix (SubBasis D s × RegisterBasis F) (SubBasis D s × RegisterBasis F) ℂ :=
  fun a b => ∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
    if (∀ i (hi : i ∈ s), x i = a.1 ⟨i,hi⟩ ∧ y i = b.1 ⟨i,hi⟩) ∧
        (∀ i, i ∉ s → x i = y i)
    then rho (fun i => (x i,a.2 i)) (fun i => (y i,b.2 i)) else 0

/-- PDF p.5,(3.1): CMI I(A_i; A_pre A'_others | A'_i), written as the
four entropies H(A_i A'_i)-H(A'_i)-H(A_i A_pre A'_all)+H(A_pre A'_all).
The permutation orders PAIRS, not independent permutations of their factors. -/
def chainTerm {l : ℕ} {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (order : Equiv.Perm (Fin l)) (k : Fin l) : ℝ :=
  let i := order k
  let pre := (Finset.univ.filter fun r : Fin l => r.val < k.val).image order
  let pair := QAlgorithms.Papers.Independent.Claimed50.P33.registerMarginal
    (QAlgorithms.Papers.Independent.Claimed50.P33.trivialExtension rho) {i}
  let primed := QAlgorithms.Papers.Independent.Claimed50.P33.registerMarginal
    (QAlgorithms.Papers.Independent.Claimed50.P33.trivialExtension
      (QAlgorithms.Papers.Independent.Claimed50.P33.primedMarginal rho)) {i}
  entropy pair - entropy primed - entropy (selectUnprimed rho (insert i pre)) +
    entropy (selectUnprimed rho pre)

/-- PDF p.9,(5.1): half the infimum over every positive finite local ancillary
dimension and every normalized extension. No optimizer or dimension cap is assumed. -/
def cemi {l : ℕ} {D : Fin l → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  (1 / 2 : ℝ) * sInf {v : ℝ | ∃ d : Fin l → ℕ, (∀ i, 0 < d i) ∧
    ∃ sigma : Matrix (RegisterBasis (fun i => D i × Fin (d i)))
      (RegisterBasis (fun i => D i × Fin (d i))) ℂ,
    IsDensityMatrix sigma ∧
    QAlgorithms.Papers.Independent.Claimed50.P33.unprimedMarginal sigma = rho ∧
    v = informationGap sigma}

/-- PDF p.12,(5.24): unrestricted-extension squashed entanglement, half-infimum
of TOTAL conditional correlation, converted from the accepted bits to nats. -/
def multipartiteSquashedNats {l : ℕ} {D : Fin l → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  Real.log 2 * QAlgorithms.Papers.Independent.Claimed50.P33.halfExtensionSquashed .total rho

/-- PDF p.7,(4.3): finite POVMs with arbitrary positive outcome dimension. -/
structure LocalMeasurement (A : Type) [Fintype A] where
  outcomes : ℕ
  positive : 0 < outcomes
  effects : Fin outcomes → Matrix A A ℂ
  povm : IsPOVM effects

/-- PDF p.7,(4.3): complex trace on arbitrary operators, hence correct on
reference off-diagonal blocks. The output basis is X, correcting the printed Ai label. -/
def povmChannelAction {A : Type} [Fintype A] (M : LocalMeasurement A) :
    Superop A (Fin M.outcomes) :=
  fun X x y => if x = y then ((M.effects x) * X).trace else 0

/-- PDF p.6,(4.1): the SUPREMUM over all local finite POVMs; no attainment premise. -/
def msqDiscord {l : ℕ} {D : Fin l → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  multipartiteInformationNats rho - sSup {v : ℝ | ∃ M : (i : Fin l) → LocalMeasurement (D i),
    v = multipartiteInformationNats (multipartiteTensorAction (fun i => povmChannelAction (M i)) rho)}

/-- PDF pp.4,7–9: finite-dimensional EB channels, equivalently a finite POVM
followed by preparation of normalized states. The CPTP property is retained explicitly. -/
def IsEBChannel {A : Type} [Fintype A] (E : Superop A A) : Prop :=
  IsChannel E ∧ ∃ M : LocalMeasurement A,
    ∃ tau : Fin M.outcomes → Matrix A A ℂ,
    (∀ x, IsDensityMatrix (tau x)) ∧
    ∀ X, E X = ∑ x, (((M.effects x) * X).trace) • tau x

/-- PDF p.20,(A.3): distance to all fully separable states on these SAME factors.
The accepted predicate uses arbitrary finite mixtures of all-party mixed products. -/
def fullySeparableTraceDistance {l : ℕ} (s : QAlgorithms.Papers.Independent.Claimed50.P33.FiniteState l) : ℝ :=
  sInf {v : ℝ | ∃ sigma : Matrix (RegisterBasis (fun i => Fin (s.dims i)))
      (RegisterBasis (fun i => Fin (s.dims i))) ℂ,
    ∃ h : IsDensityMatrix sigma,
    QAlgorithms.Papers.Independent.Claimed50.P33.IsMixedFullySeparable
      ⟨s.dims,s.positive,sigma,h⟩ ∧ v = traceNorm (s.rho - sigma)}

/-- PDF p.18,(7.1): n copies, grouped by party rather than interleaved by copy. -/
def pairedCopies {l : ℕ} {D F : Fin l → Type}
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (n : ℕ) : Matrix (RegisterBasis (fun i => (Fin n → D i) × (Fin n → F i)))
      (RegisterBasis (fun i => (Fin n → D i) × (Fin n → F i))) ℂ :=
  fun x y => ∏ t, rho (fun i => ((x i).1 t,(x i).2 t))
    (fun i => ((y i).1 t,(y i).2 t))

/-- PDF p.18,(7.1): exact infimum at each blocklength; +infinity survives
support failure. Minima and finite limiting value are conclusions of Proposition 7. -/
def recoveryRelativeEntropy {l : ℕ} {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (n : ℕ) : EReal :=
  sInf {v : EReal | ∃ R : (i : Fin l) →
      Superop (Fin n → F i) ((Fin n → D i) × (Fin n → F i)),
    (∀ i, IsChannel (R i)) ∧ v =
    QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
      (pairedCopies rho n) (recover R (pairedCopies rho n))}

/-- PDF p.20,(A.2): retain the first replica of each register in the accepted
replica basis. Its first party has multiplicity one; all others have k+1. -/
def replicaHead {m k : ℕ} {d : Fin (m+1) → ℕ}
    (x : ReplicaBasis (fun i => Fin (d i)) (k+1)) : RegisterBasis (fun i => Fin (d i)) :=
  fun i => x i ⟨0, by
    dsimp [partyCopyMultiplicity]
    split <;> exact Nat.zero_lt_succ _⟩

/-- PDF p.20,(A.2): reuse the accepted full partial trace, selecting copy zero
on every party and retaining both matrix indices on the surviving registers. -/
def replicaMarginal {m k : ℕ} {d : Fin (m+1) → ℕ}
    (omega : Matrix (ReplicaBasis (fun i => Fin (d i)) (k+1))
      (ReplicaBasis (fun i => Fin (d i)) (k+1)) ℂ) :
    Matrix (RegisterBasis (fun i => Fin (d i))) (RegisterBasis (fun i => Fin (d i))) ℂ :=
  selectedReplicaMarginal omega (fun i => ⟨0, by
    dsimp [partyCopyMultiplicity]
    split <;> exact Nat.zero_lt_succ _⟩)

/-- PDF p.20,(A.2): independently permutation-INVARIANT mixed extensions.
No symmetric-subspace (bosonic) support restriction is imposed. -/
def IsMultipartiteExtendible {m : ℕ}
    (s : QAlgorithms.Papers.Independent.Claimed50.P33.FiniteState (m+1)) (k : ℕ) : Prop :=
  ∃ omega : Matrix (ReplicaBasis (fun i => Fin (s.dims i)) (k+1))
      (ReplicaBasis (fun i => Fin (s.dims i)) (k+1)) ℂ,
    IsDensityMatrix omega ∧ replicaMarginal (m := m) (k := k) (d := s.dims) omega = s.rho ∧
    ∀ (pi : (i : Fin (m+1)) → Equiv.Perm (Fin (partyCopyMultiplicity i (k+1)))) x y,
      omega (fun i r => x i (pi i r)) (fun i r => y i (pi i r)) = omega x y

/-- Empty selected string, PDF p.6: the denominator is exactly two. -/
example {l : ℕ} : subsetWeight (fun _ : Fin l => false) = 1 := by
  simp [subsetWeight]

/-- At zero copies the tensor power is the scalar identity, PDF p.18.
No reciprocal zero occurs in the theorem, which uses positive blocklengths. -/
example {l : ℕ} {D F : Fin l → Type}
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (x y : RegisterBasis (fun i => (Fin 0 → D i) × (Fin 0 → F i))) :
    pairedCopies rho 0 x y = 1 := by
  simp [pairedCopies]

/-- The measurement map retains the COMPLEX trace even on arbitrary
operator blocks, PDF p.7,(4.3); it does not take a real part prematurely. -/
example {A : Type} [Fintype A] (M : LocalMeasurement A)
    (X : Matrix A A ℂ) (x : Fin M.outcomes) :
    povmChannelAction M X x x = ((M.effects x) * X).trace := by
  simp [povmChannelAction]

/-- Positive extension order one is represented by k=0, PDF p.20,(A.2). -/
example {m : ℕ} {d : Fin (m+1) → ℕ} (x : ReplicaBasis (fun i => Fin (d i)) 1) :
    replicaHead (m := m) (k := 0) (d := d) x 0 =
      x 0 ⟨0, by simp [partyCopyMultiplicity]⟩ := rfl

end QAlgorithms.Papers.Independent.Gap20.P09


