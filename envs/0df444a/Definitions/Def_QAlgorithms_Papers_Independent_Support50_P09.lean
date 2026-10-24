-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09
-- name    : QAlgorithms_Papers_Independent_Support50_P09
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T18:49:14.20599+00:00
-- url     : https://prove2.me/theorems/e7d2a613-4f85-4cdd-a240-46443fc41aa9
-- title:
--   Definitions for Distributed Compression and Multiparty Squashed Entanglement
-- statement:
--   The objects the formalized statements of *Distributed Compression and Multiparty Squashed Entanglement* (arXiv:0707.2792) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SenderBlock`: PDF pp.2–3: sender blocks, with arbitrary finite local dimensions.
--   - `blockInput`: PDF p.3, (1): n independent copies, ordered as reference then sender blocks.
--   - `independentEncoders`: PDF pp.2–3: tensor product of independent local encoders, on matrix units. Each encoder acts on its sender's entire n-copy block; no shared ancilla is supplied.
--   - `MultipartyCompressionCode`: Definition II.1, PDF p.3: one compression code, with the reference untouched. log2(c_i) <= n Q_i expresses an available dimension budget; smaller outputs can be padded. Integer dimensions avoid the printed idealization 2^(n Q_i).
--   - `multipartyAchievable`: Definition II.1, PDF p.3: all sufficiently large positive blocklengths, with no rate slack inside this set; success is squared pure-state fidelity.
--   - `multipartyCompressionRegion`: Definition II.1, PDF p.3: the closed operational rate region.
--   - `entropyThreshold`: PDF p.7, (7): C_K, with the factor 1/2 on the entire entropy expression.
--   - `SelectedDims`: PDF pp.6,15: local dimensions of the actual selected marginal, in increasing order.
--   - `selectedState`: PDF p.6, (6): trace out the reference and all senders outside K, then reindex. No independently chosen extension or entropy property is assumed.
--   - `subsetSquashed`: PDF p.6, (6), and Definition V.1, pp.15–16: the half-infimum over ALL finite extension dimensions of the actual A_K marginal. The empty-party measure is zero; nonempty one-party inputs use the entropy definition itself.
--   - `entropyPolyhedron`: PDF p.9, (15): the entropy halfspace polyhedron P_H.
--   - `outerPolyhedron`: PDF p.6, (6): the outer family; E_sq is outside the factor 1/2.
--   - `senderSuffix`: PDF pp.7–9: last l senders of one fixed permutation, including l=0.
--   - `compressionCorner`: Definition III.1, PDF p.7: the rate at pi(j) is half its mutual information with R and the STRICTLY LATER senders.
--   - `compressionCorners`: Definition III.1, PDF p.7: set of corner rates; coincidences are allowed.
--   - `positiveCone`: PDF p.9, (13): the resource-wasting cone.
--   - `vertexPolyhedron`: PDF p.9, (14): convex combinations of corners plus arbitrary resource wasting.
--   - `rateRecession`: PDF p.13, Step 3: recession directions, at every feasible point and all t>=0.
--   - `IsMaximalChain`: PDF p.12, (28): m strict inclusions from empty to the full sender set.
--   - `chainEquations`: PDF p.12, (27): the m NONEMPTY chain equations.
--   - `localMarginal`: PDF pp.13–14: single-party partial trace in the original local basis.
--   - `productOfMarginals`: PDF p.14: product of rho's OWN marginals, not a freely chosen product state.
--   - `stateMixture`: PDF p.17, (53): the specified convex mixture.
--   - `continuityModulus`: PDF p.19, (67): the printed modulus, using FULL trace norm (p.2,(66)). The theorem restricts 2 sqrt(eps)<=1; no extension dimension appears.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, https://arxiv.org/abs/0707.2792v2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

/-! Avis, Hayden and Savov, arXiv:0707.2792v2.
All systems are finite and nonzero, and entropies are in bits.
The imported halfExtensionSquashed .total is exactly Definition V.1.
Compilation is pending the separately scheduled mechanical compilation stage. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2–3: sender blocks, with arbitrary finite local dimensions. -/
abbrev SenderBlock {m : ℕ} (D : Fin m → Type) (n : ℕ) :=
  (i : Fin m) → Fin n → D i

/-- PDF p.3, (1): n independent copies, ordered as reference then sender blocks. -/
def blockInput {m : ℕ} {D : Fin m → Type} {R : Type}
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) (n : ℕ) :
    Matrix ((Fin n → R) × SenderBlock D n) ((Fin n → R) × SenderBlock D n) ℂ :=
  fun a b => ∏ t, rho ((fun i => a.2 i t),a.1 t) ((fun i => b.2 i t),b.1 t)

/-- PDF pp.2–3: tensor product of independent local encoders, on matrix units.
Each encoder acts on its sender's entire n-copy block; no shared ancilla is supplied. -/
def independentEncoders {m n : ℕ} {D C : Fin m → Type} [∀ i, Fintype (D i)]
    (enc : (i : Fin m) → Superop (Fin n → D i) (C i)) :
    Superop (SenderBlock D n) (RegisterBasis C) :=
  fun M a b => ∑ x : SenderBlock D n, ∑ y : SenderBlock D n,
    M x y * ∏ i, enc i (Matrix.single (x i) (y i) 1) (a i) (b i)

/-- Definition II.1, PDF p.3: one compression code, with the reference untouched.
log2(c_i) <= n Q_i expresses an available dimension budget; smaller outputs can
be padded. Integer dimensions avoid the printed idealization 2^(n Q_i). -/
def MultipartyCompressionCode {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (n : ℕ) (Q : Fin m → ℝ) (eps : ℝ) : Prop :=
  ∃ c : Fin m → ℕ, (∀ i, 0 < c i) ∧
    (∀ i, Real.logb 2 (c i) ≤ (n : ℝ) * Q i) ∧
    ∃ enc : (i : Fin m) → Superop (Fin n → D i) (Fin (c i)),
      (∀ i, IsChannel (enc i)) ∧
    ∃ dec : Superop (RegisterBasis (fun i => Fin (c i))) (SenderBlock D n),
      IsChannel dec ∧
      1 - eps ≤ ((blockInput rho n) *
        idTensorSuperop (dec ∘ independentEncoders enc) (blockInput rho n)).trace.re

/-- Definition II.1, PDF p.3: all sufficiently large positive blocklengths,
with no rate slack inside this set; success is squared pure-state fidelity. -/
def multipartyAchievable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) : Set (Fin m → ℝ) :=
  {Q | (∀ i, 0 ≤ Q i) ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → 0 < n → MultipartyCompressionCode rho n Q eps}

/-- Definition II.1, PDF p.3: the closed operational rate region. -/
def multipartyCompressionRegion {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) : Set (Fin m → ℝ) :=
  closure (multipartyAchievable rho)

/-- PDF p.7, (7): C_K, with the factor 1/2 on the entire entropy expression. -/
def entropyThreshold {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (K : Finset (Fin m)) : ℝ :=
  ((∑ i ∈ K, entropyAt (trivialExtension (forgetEnvironment rho)) {i}) +
    vnEntropy (traceLeft rho) - entropyAt rho K) / 2

/-- PDF pp.6,15: local dimensions of the actual selected marginal, in increasing order. -/
abbrev SelectedDims {m : ℕ} (D : Fin m → Type) (K : Finset (Fin m)) :=
  fun j : Fin K.card => D ((K.orderIsoOfFin rfl) j).val

/-- PDF p.6, (6): trace out the reference and all senders outside K, then reindex.
No independently chosen extension or entropy property is assumed. -/
def selectedState {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (K : Finset (Fin m)) :
    Matrix (RegisterBasis (SelectedDims D K)) (RegisterBasis (SelectedDims D K)) ℂ :=
  fun a b => forgetEnvironment (registerMarginal rho K)
    (fun i => cast (congrArg (fun j : {j : Fin m // j ∈ K} => D j.val)
      ((K.orderIsoOfFin rfl).apply_symm_apply i)) (a ((K.orderIsoOfFin rfl).symm i)))
    (fun i => cast (congrArg (fun j : {j : Fin m // j ∈ K} => D j.val)
      ((K.orderIsoOfFin rfl).apply_symm_apply i)) (b ((K.orderIsoOfFin rfl).symm i)))

/-- PDF p.6, (6), and Definition V.1, pp.15–16: the half-infimum over ALL
finite extension dimensions of the actual A_K marginal. The empty-party
measure is zero; nonempty one-party inputs use the entropy definition itself. -/
def subsetSquashed {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (K : Finset (Fin m)) : ℝ :=
  if K = ∅ then 0 else halfExtensionSquashed .total (selectedState rho K)

/-- PDF p.9, (15): the entropy halfspace polyhedron P_H. -/
def entropyPolyhedron {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) : Set (Fin m → ℝ) :=
  {Q | ∀ K : Finset (Fin m), entropyThreshold rho K ≤ ∑ i ∈ K, Q i}

/-- PDF p.6, (6): the outer family; E_sq is outside the factor 1/2. -/
def outerPolyhedron {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) : Set (Fin m → ℝ) :=
  {Q | ∀ K : Finset (Fin m),
    entropyThreshold rho K - subsetSquashed rho K ≤ ∑ i ∈ K, Q i}

/-- PDF pp.7–9: last l senders of one fixed permutation, including l=0. -/
def senderSuffix {m : ℕ} (pi : Equiv.Perm (Fin m)) (l : ℕ) : Finset (Fin m) :=
  (Finset.univ.filter fun j : Fin m => m ≤ j.val + l).image pi

/-- Definition III.1, PDF p.7: the rate at pi(j) is half its mutual information
with R and the STRICTLY LATER senders. -/
def compressionCorner {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (pi : Equiv.Perm (Fin m)) : Fin m → ℝ :=
  fun i =>
    let later := (Finset.univ.filter fun j : Fin m => (pi.symm i).val < j.val).image pi
    (entropyAt (trivialExtension (forgetEnvironment rho)) {i} +
      entropyAt rho later - entropyAt rho (insert i later)) / 2

/-- Definition III.1, PDF p.7: set of corner rates; coincidences are allowed. -/
def compressionCorners {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) : Set (Fin m → ℝ) :=
  Set.range (compressionCorner rho)

/-- PDF p.9, (13): the resource-wasting cone. -/
def positiveCone (m : ℕ) : Set (Fin m → ℝ) := {v | ∀ i, 0 ≤ v i}

/-- PDF p.9, (14): convex combinations of corners plus arbitrary resource wasting. -/
def vertexPolyhedron {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) : Set (Fin m → ℝ) :=
  {Q | ∃ x ∈ convexHull ℝ (compressionCorners rho), ∃ v ∈ positiveCone m, Q = x + v}

/-- PDF p.13, Step 3: recession directions, at every feasible point and all t>=0. -/
def rateRecession {m : ℕ} (P : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {v | ∀ x ∈ P, ∀ t : ℝ, 0 ≤ t → x + t • v ∈ P}

/-- PDF p.12, (28): m strict inclusions from empty to the full sender set. -/
def IsMaximalChain {m : ℕ} (K : Fin (m+1) → Finset (Fin m)) : Prop :=
  K 0 = ∅ ∧ K ⟨m,Nat.lt_succ_self m⟩ = Finset.univ ∧
    ∀ j : Fin m, K j.castSucc ⊂ K j.succ

/-- PDF p.12, (27): the m NONEMPTY chain equations. -/
def chainEquations {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (K : Fin (m+1) → Finset (Fin m)) (Q : Fin m → ℝ) : Prop :=
  ∀ j : Fin m, (∑ i ∈ K j.succ, Q i) = entropyThreshold rho (K j.succ)

/-- PDF pp.13–14: single-party partial trace in the original local basis. -/
def localMarginal {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (i : Fin m) :
    Matrix (D i) (D i) ℂ :=
  fun a b => ∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
    if x i = a ∧ y i = b ∧ (∀ j, j ≠ i → x j = y j) then rho x y else 0

/-- PDF p.14: product of rho's OWN marginals, not a freely chosen product state. -/
def productOfMarginals {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  fun a b => ∏ i, localMarginal rho i (a i) (b i)

/-- PDF p.17, (53): the specified convex mixture. -/
def stateMixture {I : Type} (lambda : ℝ) (rho sigma : Matrix I I ℂ) : Matrix I I ℂ :=
  (lambda : ℂ) • rho + ((1-lambda : ℝ) : ℂ) • sigma

/-- PDF p.19, (67): the printed modulus, using FULL trace norm (p.2,(66)).
The theorem restricts 2 sqrt(eps)<=1; no extension dimension appears. -/
def continuityModulus {m : ℕ} (D : Fin m → Type) [∀ i, Fintype (D i)] (eps : ℝ) : ℝ :=
  16 * Real.sqrt eps * Real.logb 2 (∏ i, (Fintype.card (D i) : ℝ)) +
    ((m : ℝ)+1) * 2 * binEntropy2 (2 * Real.sqrt eps)

/-! Small sanity examples for the new constructions; no target theorem is proved. -/

example {m : ℕ} {D : Fin m → Type} {R : Type}
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (a b : (Fin 0 → R) × SenderBlock D 0) : blockInput rho 0 a b = 1 := by
  simp [blockInput]

example {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)] {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    subsetSquashed rho ∅ = 0 := by simp [subsetSquashed]

example {m : ℕ} (pi : Equiv.Perm (Fin m)) : senderSuffix pi 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨j,hj,_⟩ := Finset.mem_image.mp hi
  have h := (Finset.mem_filter.mp hj).2
  exact (Nat.not_le.mpr j.isLt) (by simpa using h)

example {I : Type} (rho sigma : Matrix I I ℂ) : stateMixture 0 rho sigma = sigma := by
  simp [stateMixture]

example {m : ℕ} {Q : Fin m → ℝ} : Q ∈ positiveCone m ↔ ∀ i, 0 ≤ Q i := Iff.rfl

example {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (a b : RegisterBasis D) :
    productOfMarginals rho a b = ∏ i, localMarginal rho i (a i) (b i) := rfl

section Compression

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)] [hD : ∀ i, Nonempty (D i)]
variable {R : Type} [Fintype R] [hR : Nonempty R]
variable (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1)

include hphi hD hR

end Compression

end QAlgorithms.Papers.Independent.Support50.P09


