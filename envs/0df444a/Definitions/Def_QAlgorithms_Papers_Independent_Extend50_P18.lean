-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18
-- name    : QAlgorithms_Papers_Independent_Extend50_P18
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T19:55:30.111006+00:00
-- url     : https://prove2.me/theorems/ceddeecf-c5eb-4572-a135-85d617950f86
-- title:
--   Definitions for Efficient multi port-based teleportation schemes
-- statement:
--   The objects the formalized statements of *Efficient multi port-based teleportation schemes* (arXiv:2008.00984) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ProtocolIndex`: Alice's N ports and the ordered k input registers (PDF pp.5-6).
--   - `PortChoice`: Ordered distinct port choices; l-th input is paired with i(l) (PDF p.5, (4)).
--   - `mpbtSignal`: Signal density (7), in computational coordinates. The Bell projectors each contribute 1/d and the unused registers contribute 1/d^(N-k), giving 1/d^N (PDF p.6). This definition is used only under k <= N and d > 0.
--   - `mpbtOperator`: Sum of all ordered signals, without an ensemble-probability factor (PDF p.6, (8)).
--   - `inverseRoot`: Support inverse square root, with value zero at the zero eigenvalue (PDF p.6, (10)).
--   - `srmRaw`: Uncompleted square-root measurement effect, distinct from the completed Pi (PDF p.6, (10)-(11)).
--   - `srmRemainder`: Equal distribution of the support-complement effect (PDF p.6, (11)).
--   - `srmEffect`: Completed deterministic SRM effect (PDF p.6, (10)).
--   - `protocolFidelity`: Entanglement fidelity functional (9), valid for the fixed normalized Bell resource and Bob's ordered port selection, with no further correction (PDF pp.5-6). The real part extracts the real trace of physical products.
--   - `irrepDim`: Physical irrep dimension, not an independently supplied scalar (PDF p.9, (28),(30)).
--   - `mpbtSchurMultiplicity`: Physical Schur-Weyl multiplicity, including all tensor copies (PDF p.9, (29)-(30)).
--   - `YoungPaths`: Saturated paths in the height-d Young lattice from alpha to mu. A path has one box added at each step, and is counted once, not weighted by its length (PDF pp.8-9, (58)-(59)).
--   - `pathCount`: Number of saturated paths (PDF pp.8-9, (58)-(59)).
--   - `fidelityExpression`: Explicit value of the deterministic performance formula. The outer sum is outside the square and path multiplicities are outside the square root (PDF p.18, (134), independently (140),(154)).
--   - `ContractionIndex`: Contraction registers: r untouched, k middle, k output, so n=r+2k (PDF p.9, (37)).
--   - `reverseWord`: Reversal of the output order in the explicitly paired systems of (37) (PDF p.9).
--   - `pairedContraction`: Product of partially transposed swaps, namely d^k times the normalized Bell projector on the paired registers, with untouched identities (37). Its entries are 0 or 1; there is no additional normalization (PDF p.9).
--   - `liftInput`: Embed an arbitrary operator on the first r+k registers, adding identity on the final k outputs (PDF p.9, (38)).
--   - `liftSurvivor`: Embed an operator on the untouched r registers by identities on both paired blocks (PDF p.9, (38)).
--   - `spechtActionMatrix`: Irrep matrices in the frozen orthonormal Specht basis. Fact 2 is independent of any branching convention (PDF pp.9-10, (32),(42)).
--   - `physicalBlock`: The physical block I_(U_lambda) tensor X, extended by zero, expressed via the frozen independently constructed Schur transform, not defined by the Fourier sum whose identity is being stated (PDF pp.9-10, (30),(42)).
--   - `includePermutation`: Embed S(t) into S(t+1), fixing the final register (PDF p.10, (50)-(51)).
--   - `restrictionProjector`: Character-defined beta-restriction projector inside the actual mu Specht module. This is the coordinate-independent restriction block of Lemma 3, not an arbitrarily supplied projection (PDF p.10, (46),(51)).
--   - `weightedTranspositions`: Weighted transposition sum: a=n contributes d times the identity, not one (PDF p.10, (45),(47)).
--   - `traceFinalQudits`: Unnormalized trace of the last k factors of an r+k factor operator. In Lemma 9/Corollary 10 these are the middle registers of n=r+2k (PDF pp.12-13).
--   - `permuteChoice`: Relabel all ordered selected ports by the actual permutation, preserving input order (PDF p.7, (22)).
--   - `portPermutation`: Physical permutation of Alice's ports, leaving the ordered inputs fixed (PDF p.7, (22)-(23)).
--   - `mixedTensorAction`: U on every Alice register and entrywise conjugate U on every input (PDF p.7, §IV).
--   - `eigenvalueExpression`: Eigenvalue expression (119), computed from physical dimensions (PDF p.17). The count |I| is (r+k)!/r!, with N=r+k.
--   - `reciprocalMinimum`: Minimum of the entire reciprocal eigenvalue expression over occurring extensions. Under d>0, every alpha admits an extension (add k boxes to row 1), the set is finite nonempty and all eigenvalues are positive. Thus no empty or unbounded sInf default is involved on theorem inputs (PDF pp.19-20, (141),(144)).
--   - `successExpression`: Optimal success probability expression, the minimum applies to the whole quotient m_alpha*d_alpha/lambda_mu(alpha) (PDF p.19, (141)).
--   - `PortFrames`: Coordinate conventions for selected and unused ports. These are arbitrary register enumerations, with selected registers in the specified input order; they do not constrain measurements or the resource (PDF pp.5-7).
--   - `successEffect`: Selected Bell projector tensor an operator on the remaining registers, transported through an explicit port enumeration (PDF p.6, (13)).
--   - `FeasibleSuccess`: Complete feasible family in the source's perfect-success model: each theta is PSD and the residual failure effect is PSD (PDF pp.6-7, (13)-(15)).
--   - `mpbtAverageSuccess`: Average success (12), or equivalently (14) since each Bell projector has trace one (PDF pp.6-7).
--   - `optimalTheta`: Proof-supported optimal unused-register effect: coefficient (d^k/d^N)*b_alpha, not the probability prefactor printed in (142). Printed: |I|/d^(2N); changed: d^(k-N). Why: (143)-(145) give the feasible saturating coefficient and (146)-(149) its matching upper bound (PDF pp.19-20). Independent moderation of this correction remains required.
--   - `FiniteUnitaryRepresentation`: Finite-dimensional unitary matrix representation (PDF p.11, (60)).
--   - `MatrixIrreducible`: Irreducibility for a unitary representation: only trivial invariant orthogonal projections. Positive dimension excludes the zero module (PDF p.11).
--   - `SubgroupBlockIndex`: Coordinate space grouped first by H-irrep type, then multiplicity copy, then irrep coordinate (PDF p.11, (60)-(61)).
--   - `subgroupBlockMatrix`: Repeated copies use the same fixed realization; zero off each diagonal copy, including distinct copies of the same irrep (PDF p.11, (60)-(61)).
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, https://arxiv.org/abs/2008.00984v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- Alice's N ports and the ordered k input registers (PDF pp.5-6). -/
abbrev ProtocolIndex (d N k : ℕ) := (Fin N → Fin d) × (Fin k → Fin d)

/-- Ordered distinct port choices; l-th input is paired with i(l) (PDF p.5, (4)). -/
abbrev PortChoice (N k : ℕ) := Fin k ↪ Fin N

/-- Signal density (7), in computational coordinates. The Bell projectors each
contribute 1/d and the unused registers contribute 1/d^(N-k), giving 1/d^N
(PDF p.6). This definition is used only under k <= N and d > 0. -/
def mpbtSignal {d N k : ℕ} (i : PortChoice N k) :
    Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ :=
  Matrix.of fun x y =>
    if (∀ a : Fin N, (∀ l : Fin k, i l ≠ a) → x.1 a = y.1 a) ∧
        (∀ l : Fin k, x.1 (i l) = x.2 l) ∧
        (∀ l : Fin k, y.1 (i l) = y.2 l)
    then ((d : ℂ) ^ N)⁻¹ else 0

/-- Sum of all ordered signals, without an ensemble-probability factor
(PDF p.6, (8)). -/
def mpbtOperator (d N k : ℕ) : Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ :=
  ∑ i : PortChoice N k, mpbtSignal i

/-- Support inverse square root, with value zero at the zero eigenvalue
(PDF p.6, (10)). -/
def inverseRoot (d N k : ℕ) : Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ :=
  cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (mpbtOperator d N k)

/-- Uncompleted square-root measurement effect, distinct from the completed Pi
(PDF p.6, (10)-(11)). -/
def srmRaw {d N k : ℕ} (i : PortChoice N k) :
    Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ :=
  inverseRoot d N k * mpbtSignal i * inverseRoot d N k

/-- Equal distribution of the support-complement effect (PDF p.6, (11)). -/
def srmRemainder (d N k : ℕ) : Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ :=
  ((Fintype.card (PortChoice N k) : ℂ)⁻¹) •
    (1 - ∑ i : PortChoice N k, srmRaw (d := d) i)

/-- Completed deterministic SRM effect (PDF p.6, (10)). -/
def srmEffect {d N k : ℕ} (i : PortChoice N k) :
    Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ :=
  srmRaw i + srmRemainder d N k

/-- Entanglement fidelity functional (9), valid for the fixed normalized Bell
resource and Bob's ordered port selection, with no further correction
(PDF pp.5-6). The real part extracts the real trace of physical products. -/
def protocolFidelity {d N k : ℕ}
    (effects : PortChoice N k → Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ) : ℝ :=
  (∑ i : PortChoice N k, (effects i * mpbtSignal i).trace.re) / (d : ℝ) ^ (2*k)

/-- A positive local dimension has a single scalar signal when d=1. -/
example {N k : ℕ} (i : PortChoice N k) :
    mpbtSignal (d := 1) i = (1 : Matrix (ProtocolIndex 1 N k) (ProtocolIndex 1 N k) ℂ) := by
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  have hlocal : ∀ a b : Fin 1, a = b := fun _ _ => Subsingleton.elim _ _
  have hpaired : ∀ l : Fin k, x.1 (i l) = x.2 l := fun _ => hlocal _ _
  simp [mpbtSignal, Matrix.one_apply, hpaired]

/-- Physical irrep dimension, not an independently supplied scalar
(PDF p.9, (28),(30)). -/
def irrepDim {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) : ℕ :=
  Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)

/-- Physical Schur-Weyl multiplicity, including all tensor copies
(PDF p.9, (29)-(30)). -/
def mpbtSchurMultiplicity {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) : ℕ :=
  Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda)

/-- Saturated paths in the height-d Young lattice from alpha to mu. A path has
one box added at each step, and is counted once, not weighted by its length
(PDF pp.8-9, (58)-(59)). -/
def YoungPaths {d r k : ℕ} (alpha : QAlgorithms.Schur.Partition d r)
    (mu : QAlgorithms.Schur.Partition d (r+k)) :=
  {p : (j : Fin (k+1)) → QAlgorithms.Schur.Partition d (r+j.val) //
    (p 0).val = alpha.val ∧ (p (Fin.last k)).val = mu.val ∧
      ∀ j : Fin k, (p j.castSucc).val ≤ (p j.succ).val}

/-- Paths form a finite type, ruling out Nat.card's infinite-type default. -/
instance youngPathsFinite {d r k : ℕ} (alpha : QAlgorithms.Schur.Partition d r)
    (mu : QAlgorithms.Schur.Partition d (r+k)) : Finite (YoungPaths alpha mu) := by
  unfold YoungPaths
  infer_instance

/-- Number of saturated paths (PDF pp.8-9, (58)-(59)). -/
def pathCount {d r k : ℕ} (alpha : QAlgorithms.Schur.Partition d r)
    (mu : QAlgorithms.Schur.Partition d (r+k)) : ℕ :=
  Nat.card (YoungPaths alpha mu)

/-- Explicit value of the deterministic performance formula. The outer sum is
outside the square and path multiplicities are outside the square root
(PDF p.18, (134), independently (140),(154)). -/
def fidelityExpression (d r k : ℕ) : ℝ :=
  (∑ alpha : QAlgorithms.Schur.Partition d r,
    (∑ mu : QAlgorithms.Schur.Partition d (r+k),
      (pathCount alpha mu : ℝ) *
        Real.sqrt ((mpbtSchurMultiplicity mu : ℝ) * (irrepDim mu : ℝ))) ^ 2) /
    (d : ℝ) ^ (r+k+2*k)

/-- Contraction registers: r untouched, k middle, k output, so n=r+2k
(PDF p.9, (37)). -/
abbrev ContractionIndex (d r k : ℕ) := (Fin r → Fin d) × ((Fin k → Fin d) × (Fin k → Fin d))

/-- Reversal of the output order in the explicitly paired systems of (37)
(PDF p.9). -/
def reverseWord {d k : ℕ} (w : (Fin k → Fin d)) : (Fin k → Fin d) := fun l => w l.rev

/-- Product of partially transposed swaps, namely d^k times the normalized
Bell projector on the paired registers, with untouched identities (37).
Its entries are 0 or 1; there is no additional normalization (PDF p.9). -/
def pairedContraction (d r k : ℕ) :
    Matrix (ContractionIndex d r k) (ContractionIndex d r k) ℂ :=
  Matrix.of fun x y => if x.1 = y.1 ∧ x.2.1 = reverseWord x.2.2 ∧
    y.2.1 = reverseWord y.2.2 then 1 else 0

/-- Embed an arbitrary operator on the first r+k registers, adding identity
on the final k outputs (PDF p.9, (38)). -/
def liftInput {d r k : ℕ} (X : Matrix ((Fin r → Fin d) × (Fin k → Fin d)) ((Fin r → Fin d) × (Fin k → Fin d)) ℂ) :
    Matrix (ContractionIndex d r k) (ContractionIndex d r k) ℂ :=
  Matrix.of fun x y => X (x.1,x.2.1) (y.1,y.2.1) * if x.2.2 = y.2.2 then 1 else 0

/-- Embed an operator on the untouched r registers by identities on both
paired blocks (PDF p.9, (38)). -/
def liftSurvivor {d r k : ℕ} (X : Matrix ((Fin r → Fin d)) ((Fin r → Fin d)) ℂ) :
    Matrix (ContractionIndex d r k) (ContractionIndex d r k) ℂ :=
  Matrix.of fun x y => X x.1 y.1 * if x.2 = y.2 then 1 else 0

/-- In local dimension one the contraction has exactly the scalar value one. -/
example (r k : ℕ) (x y : ContractionIndex 1 r k) : pairedContraction 1 r k x y = 1 := by
  simp [pairedContraction, Subsingleton.elim x.1 y.1,
    Subsingleton.elim x.2.1 (reverseWord x.2.2),
    Subsingleton.elim y.2.1 (reverseWord y.2.2)]

/-- Irrep matrices in the frozen orthonormal Specht basis. Fact 2 is independent
of any branching convention (PDF pp.9-10, (32),(42)). -/
def spechtActionMatrix {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (pi : Equiv.Perm (Fin n)) : Matrix (Fin (irrepDim lambda)) (Fin (irrepDim lambda)) ℂ :=
  Matrix.of fun i j => inner ℂ
    (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lambda) i)
    (QAlgorithms.Schur.spechtRepresentation lambda pi
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lambda) j))

/-- The physical block I_(U_lambda) tensor X, extended by zero, expressed via
the frozen independently constructed Schur transform, not defined by the
Fourier sum whose identity is being stated (PDF pp.9-10, (30),(42)). -/
def physicalBlock {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (X : Matrix (Fin (irrepDim lambda)) (Fin (irrepDim lambda)) ℂ) :
    Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ :=
  Matrix.of fun x y =>
    ∑ a : Fin (mpbtSchurMultiplicity lambda), ∑ i : Fin (irrepDim lambda),
      ∑ j : Fin (irrepDim lambda),
        star (QAlgorithms.Schur.decomposition d n ⟨lambda,(i,a)⟩ x) * X i j *
          QAlgorithms.Schur.decomposition d n ⟨lambda,(j,a)⟩ y

/-- The independently defined physical block sends the zero operator to zero. -/
example {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) :
    physicalBlock lambda 0 = 0 := by
  ext x y
  simp [physicalBlock]

/-- Embed S(t) into S(t+1), fixing the final register (PDF p.10, (50)-(51)). -/
def includePermutation {t : ℕ} (tau : Equiv.Perm (Fin t)) : Equiv.Perm (Fin (t+1)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr tau (Equiv.refl (Fin 1))).trans finSumFinEquiv)

/-- Character-defined beta-restriction projector inside the actual mu Specht
module. This is the coordinate-independent restriction block of Lemma 3,
not an arbitrarily supplied projection (PDF p.10, (46),(51)). -/
def restrictionProjector {d t : ℕ} (mu : QAlgorithms.Schur.Partition d (t+1))
    (beta : QAlgorithms.Schur.Partition d t) :
    Matrix (Fin (irrepDim mu)) (Fin (irrepDim mu)) ℂ :=
  ((irrepDim beta : ℂ) / (t.factorial : ℂ)) •
    ∑ tau : Equiv.Perm (Fin t),
      QAlgorithms.Schur.spechtCharacter beta tau⁻¹ • spechtActionMatrix mu (includePermutation tau)

/-- Weighted transposition sum: a=n contributes d times the identity, not one
(PDF p.10, (45),(47)). -/
def weightedTranspositions {d t : ℕ} (mu : QAlgorithms.Schur.Partition d (t+1)) :
    Matrix (Fin (irrepDim mu)) (Fin (irrepDim mu)) ℂ :=
  ∑ a : Fin (t+1), (if a = Fin.last t then (d : ℂ) else 1) •
    spechtActionMatrix mu (Equiv.swap a (Fin.last t))

/-- Unnormalized trace of the last k factors of an r+k factor operator. In
Lemma 9/Corollary 10 these are the middle registers of n=r+2k (PDF pp.12-13). -/
def traceFinalQudits {d r k : ℕ} (X : Matrix ((Fin (r+k) → Fin d)) ((Fin (r+k) → Fin d)) ℂ) :
    Matrix ((Fin r → Fin d)) ((Fin r → Fin d)) ℂ :=
  QAlgorithms.traceRight (Matrix.of fun (a b : (Fin r → Fin d) × (Fin k → Fin d)) =>
    X (Fin.addCases a.1 a.2) (Fin.addCases b.1 b.2))

/-- Relabel all ordered selected ports by the actual permutation, preserving
input order (PDF p.7, (22)). -/
def permuteChoice {N k : ℕ} (tau : Equiv.Perm (Fin N)) (i : PortChoice N k) : PortChoice N k :=
  ⟨fun l => tau (i l), tau.injective.comp i.injective⟩

/-- Physical permutation of Alice's ports, leaving the ordered inputs fixed
(PDF p.7, (22)-(23)). -/
def portPermutation {d N k : ℕ} (tau : Equiv.Perm (Fin N)) :
    Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ :=
  Matrix.of fun x y => if x.1 = y.1 ∘ tau.symm ∧ x.2 = y.2 then 1 else 0

/-- U on every Alice register and entrywise conjugate U on every input
(PDF p.7, §IV). -/
def mixedTensorAction {d N k : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (ProtocolIndex d N k) (ProtocolIndex d N k) ℂ :=
  Matrix.of fun x y =>
    (∏ a : Fin N, (U : Matrix (Fin d) (Fin d) ℂ) (x.1 a) (y.1 a)) *
      ∏ l : Fin k, star ((U : Matrix (Fin d) (Fin d) ℂ) (x.2 l) (y.2 l))

/-- Eigenvalue expression (119), computed from physical dimensions (PDF p.17).
The count |I| is (r+k)!/r!, with N=r+k. -/
def eigenvalueExpression {d r k : ℕ} (alpha : QAlgorithms.Schur.Partition d r)
    (mu : QAlgorithms.Schur.Partition d (r+k)) : ℝ :=
  ((r+k).factorial : ℝ) / (r.factorial : ℝ) / (d : ℝ) ^ (r+k) *
    ((mpbtSchurMultiplicity mu : ℝ) * (irrepDim alpha : ℝ)) /
      ((mpbtSchurMultiplicity alpha : ℝ) * (irrepDim mu : ℝ))

/-- Minimum of the entire reciprocal eigenvalue expression over occurring
extensions. Under d>0, every alpha admits an extension (add k boxes to row 1),
the set is finite nonempty and all eigenvalues are positive. Thus no empty or
unbounded sInf default is involved on theorem inputs (PDF pp.19-20, (141),(144)). -/
def reciprocalMinimum {d r k : ℕ} (alpha : QAlgorithms.Schur.Partition d r) : ℝ :=
  sInf {b : ℝ | ∃ mu : QAlgorithms.Schur.Partition d (r+k),
    0 < pathCount alpha mu ∧ b = (eigenvalueExpression alpha mu)⁻¹}

/-- Optimal success probability expression, the minimum applies to the whole
quotient m_alpha*d_alpha/lambda_mu(alpha) (PDF p.19, (141)). -/
def successExpression (d r k : ℕ) : ℝ :=
  ((r+k).factorial : ℝ) / (r.factorial : ℝ) / (d : ℝ) ^ (2*(r+k)) *
    ∑ alpha : QAlgorithms.Schur.Partition d r,
      (mpbtSchurMultiplicity alpha : ℝ) * (irrepDim alpha : ℝ) * reciprocalMinimum (k := k) alpha

/-- Coordinate conventions for selected and unused ports. These are arbitrary
register enumerations, with selected registers in the specified input order;
they do not constrain measurements or the resource (PDF pp.5-7). -/
def PortFrames (N k r : ℕ) :=
  (i : PortChoice N k) → {e : Fin N ≃ Fin k ⊕ Fin r // ∀ l : Fin k, e (i l) = Sum.inl l}

/-- Selected Bell projector tensor an operator on the remaining registers,
transported through an explicit port enumeration (PDF p.6, (13)). -/
def successEffect {d r k : ℕ} (frames : PortFrames (r+k) k r)
    (theta : (i : PortChoice (r+k) k) → Matrix ((Fin r → Fin d)) ((Fin r → Fin d)) ℂ)
    (i : PortChoice (r+k) k) :
    Matrix (ProtocolIndex d (r+k) k) (ProtocolIndex d (r+k) k) ℂ :=
  Matrix.of fun x y =>
    if (∀ l : Fin k, x.1 (i l) = x.2 l) ∧ (∀ l : Fin k, y.1 (i l) = y.2 l)
    then ((d : ℂ) ^ k)⁻¹ * theta i
      (fun a => x.1 ((frames i).val.symm (Sum.inr a)))
      (fun a => y.1 ((frames i).val.symm (Sum.inr a)))
    else 0

/-- Complete feasible family in the source's perfect-success model: each theta
is PSD and the residual failure effect is PSD (PDF pp.6-7, (13)-(15)). -/
def FeasibleSuccess {d r k : ℕ} (frames : PortFrames (r+k) k r)
    (theta : (i : PortChoice (r+k) k) → Matrix ((Fin r → Fin d)) ((Fin r → Fin d)) ℂ) : Prop :=
  (∀ i, (theta i).PosSemidef) ∧
    (1 - ∑ i : PortChoice (r+k) k, successEffect frames theta i).PosSemidef

/-- Average success (12), or equivalently (14) since each Bell projector has
trace one (PDF pp.6-7). -/
def mpbtAverageSuccess {d r k : ℕ} (frames : PortFrames (r+k) k r)
    (theta : (i : PortChoice (r+k) k) → Matrix ((Fin r → Fin d)) ((Fin r → Fin d)) ℂ) : ℝ :=
  (∑ i : PortChoice (r+k) k, (successEffect frames theta i).trace.re) /
    (d : ℝ) ^ (r+2*k)

/-- Proof-supported optimal unused-register effect: coefficient
(d^k/d^N)*b_alpha, not the probability prefactor printed in (142).
Printed: |I|/d^(2N); changed: d^(k-N). Why: (143)-(145) give the feasible
saturating coefficient and (146)-(149) its matching upper bound
(PDF pp.19-20). Independent moderation of this correction remains required. -/
def optimalTheta (d r k : ℕ) : Matrix ((Fin r → Fin d)) ((Fin r → Fin d)) ℂ :=
  ∑ alpha : QAlgorithms.Schur.Partition d r,
    (((d : ℂ)^k / (d : ℂ)^(r+k)) * (reciprocalMinimum (k := k) alpha : ℂ)) •
      QAlgorithms.Schur.isotypicProjector alpha

/-- Zero unused-register operator gives zero success effect, including all
possible off-diagonal Bell entries. -/
example {d r k : ℕ} (frames : PortFrames (r+k) k r) (i : PortChoice (r+k) k) :
    successEffect (d := d) frames (fun _ => 0) i = 0 := by
  ext x y
  simp [successEffect]

/-- Finite-dimensional unitary matrix representation (PDF p.11, (60)). -/
structure FiniteUnitaryRepresentation (G : Type*) [Group G] (m : ℕ) where
  matrix : G → Matrix (Fin m) (Fin m) ℂ
  map_one : matrix 1 = 1
  map_mul : ∀ g h, matrix (g*h) = matrix g * matrix h
  unitary : ∀ g, (matrix g)ᴴ * matrix g = 1 ∧ matrix g * (matrix g)ᴴ = 1

/-- Irreducibility for a unitary representation: only trivial invariant
orthogonal projections. Positive dimension excludes the zero module
(PDF p.11). -/
def MatrixIrreducible {G : Type*} [Group G] {m : ℕ} (rho : FiniteUnitaryRepresentation G m) : Prop :=
  0 < m ∧ ∀ P : Matrix (Fin m) (Fin m) ℂ,
    Pᴴ = P → P*P = P → (∀ g, P * rho.matrix g = rho.matrix g * P) → P = 0 ∨ P = 1

/-- Coordinate space grouped first by H-irrep type, then multiplicity copy,
then irrep coordinate (PDF p.11, (60)-(61)). -/
abbrev SubgroupBlockIndex {a : ℕ} (dims copies : Fin a → ℕ) :=
  (label : Fin a) × (Fin (copies label) × Fin (dims label))

/-- Repeated copies use the same fixed realization; zero off each diagonal
copy, including distinct copies of the same irrep (PDF p.11, (60)-(61)). -/
def subgroupBlockMatrix {G : Type*} [Group G] {a : ℕ} (dims copies : Fin a → ℕ)
    (reps : (label : Fin a) → FiniteUnitaryRepresentation G (dims label)) (g : G) :
    Matrix (SubgroupBlockIndex dims copies) (SubgroupBlockIndex dims copies) ℂ :=
  Matrix.of fun x y => if h : y.1 = x.1 then
    if x.2.1 = h ▸ y.2.1 then (reps x.1).matrix g x.2.2 (h ▸ y.2.2) else 0 else 0

end QAlgorithms.Papers.Independent.Extend50.P18


