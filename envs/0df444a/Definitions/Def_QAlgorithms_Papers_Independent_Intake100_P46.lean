-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46
-- name    : QAlgorithms_Papers_Independent_Intake100_P46
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:56:31.800252+00:00
-- url     : https://prove2.me/theorems/da2ca380-5053-467c-ac52-b370e8aef2c8
-- title:
--   Definitions for A purification postulate for quantum mechanics with indefinite causal order
-- statement:
--   The objects the formalized statements of *A purification postulate for quantum mechanics with indefinite causal order* (arXiv:1611.08535) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ProcessWireDimensions`: PDF pp.2,10: positive dimensions in wire order P, AI, AO, BI, BO, F.
--   - `ProcessBasis`: PDF p.2: the fixed computational basis of all six wires.
--   - `ProcessMatrix`: PDF p.2: a process operator, without any validity condition imposed by its type.
--   - `processCoordinates`: PDF pp.2–3: coordinate insertion in the fixed six-wire order.
--   - `unitaryChannelProjector`: PDF p.10, Eq.(40): |U>><<U| in input-first order, with no dimension factor.
--   - `IsReversibleMatrix`: PDF pp.3–4: reversible unitarity between possibly differently labelled finite bases. Both equations are required; an isometry into a larger space is excluded.
--   - `IsIsometricMatrix`: PDF p.4: an isometry need only satisfy the first of the two unitary equations.
--   - `IsCPTPChoi`: PDF p.11, before Eq.(45): the independent finite Choi criterion for a local CPTP map.
--   - `IsUnitaryChoi`: PDF pp.3,10: the CJ operator of some reversible unitary channel.
--   - `linkLaboratories`: PDF p.2, Eq.(1), and p.11, Eq.(43): link W with arbitrary ancillary local CJ operators. The laboratory indices are contracted bilinearly (no conjugation). All off-diagonal blocks of the ancillary wires are retained.
--   - `IsValidProcess`: PDF pp.2–3,11: operational process validity, independently of LV. Every positive ancillary dimension and every pair of local CPTP operators is tested.
--   - `IsPureProcess`: PDF p.3, Definition 1: purity tests all compatible unitary laboratories on all ancillary wires, including the enlarged SWAP laboratories in Eq.(9). Validity is kept separate so Theorem 2 does not silently assume arbitrary unitaries are processes.
--   - `processProjector`: PDF pp.3–4: a matrix from P AO BO to AI BI F, in its input-first CJ wire order.
--   - `replaceWires`: PDF p.11, Eq.(53): replace the wires in s by maximally mixed identity factors, preserving the order of every other wire. Strictly positive dimensions guard division.
--   - `validSubspaceProjector`: PDF p.12, Eq.(64): the complete bipartite linear normalization projector. The order of wire labels is P, AI, AO, BI, BO, F.
--   - `invalidSubspaceProjector`: PDF p.6, before Eq.(21): the complementary projector 1-LV.
--   - `vectorOuter`: PDF pp.5–6: a process-vector outer product; these vectors are unnormalized.
--   - `processVectorPairing`: PDF pp.5–6, Eq.(24): the usual conjugate-linear-first finite inner product.
--   - `laboratorySignature`: PDF pp.4–6: fixed laboratory dimensions, with independently specified global wires.
--   - `recoverProcess`: PDF p.4, Definition 3, specialized to trivial original P,F: insert |0> in Pprime and trace Fprime. The two new global dimensions are independent.
--   - `IsPurifiable`: PDF p.4, Definition 3: physical purification by an operationally valid pure process, with unrestricted positive new-past and new-future dimensions.
--   - `SupportSpectrum`: PDF pp.5–6, Eq.(19): the complete positive spectral support, with multiplicity. This is chosen spectral data, not extra unproved process constraints.
--   - `canonicalVector`: PDF pp.5–6, Eqs.(20),(23): the canonical positive-matrix purification, with future basis indexed by the spectral support. There is no normalization to trace one.
--   - `IsCompletion`: PDF p.6, Eqs.(23)–(24): all prescribed vectors, bilinear LV constraints and orthogonality with squared norm dAO*dBO.
--   - `reconstructedUnitary`: PDF p.6, Eq.(25): the actual matrix reconstructed by using wi as the past slices. Its input basis is Pprime AO BO and its output basis AI BI Fprime.
--   - `stateOutputSignature`: PDF p.4: a concrete dimension-increasing isometry, with every laboratory wire and P trivial, and F two-dimensional.
--   - `stateOutputIsometry`: PDF p.4: the isometry sends the only global input basis vector to future |0>.
--   - `IsTotallyIsotropic`: PDF pp.12–13: total isotropy is a zero compression, not invariance or membership in the kernel of C. Zero-dimensional ambient spaces are permitted.
--   - `positiveCount`: PDF p.12: positive eigenvalues counted with multiplicity.
--   - `negativeCount`: PDF p.12: strictly negative eigenvalues counted with multiplicity.
--   - `zeroCount`: PDF p.12: zero eigenvalues counted with multiplicity.
--   - `nullSquareSize`: PDF p.12: the claimed greatest null-square size, expressed without any supremum.
--   - `vectorizedComplement`: PDF p.6, Eq.(26): matrix of 1-LV on input-first vectorized operators. The coordinate pair (a,b) represents the operator entry (b,a).
--   - `purificationKernelOperator`: PDF p.6, Eq.(28): OW is computed from the canonical vector. Its ket factor is conjugated w0, so its bra factor is w0, using the conjugate-linear-first convention.
--   - `KernelBasisData`: PDF p.6, Eqs.(28)–(30): an explicit orthonormal basis of the entire kernel of OW. No basis-independence of the eventual numerical bound is asserted.
--   - `compressedOperator`: PDF p.6, Eq.(30): (conj R tensor R) Pi (transpose R tensor adjoint R), with Ria=conj(ri(a)). The entry formula retains the source's conjugations and factor order.
--   - `CompressionSpectrum`: PDF p.7, Eq.(31): a full orthonormal eigenbasis of the computed compression. Filtering its strictly nonzero eigenvalues below gives exactly the source's mk family.
--   - `NonzeroModes`: PDF p.7, Eq.(31): the complete nonzero-eigenvalue index set, possibly empty.
--   - `modeMatrix`: PDF p.7, Eq.(32): |transpose Mk>>=mk, with the same input-first CJ ordering. The intervening printed bra identity has a transpose discrepancy in this convention; only the printed reshaping and its inertia counts are used here. Transposing every constraint leaves its eigenvalues and the test bound unchanged.
--   - `constraintMatrix`: PDF p.7, Eq.(32): M+M† for false and i(M-M†) for true. Writing the latter as (iM)+(iM)† gives a Hermitian matrix by construction, without adding a hypothesis.
--   - `testBound`: PDF p.7, Eq.(34): the actual minimum over the explicit Hermitian constraints. Only the empty-family extension is top, rather than a junk natural-number zero; the footnote theorem treats that case separately.
--   - `liftKernelVector`: PDF pp.6–7: lift the kernel coordinates back to the laboratory/future vector.
--   - `qubitSignature`: PDF p.7, §6: four qubit laboratory wires, with trivial P and F.
--   - `laboratoryTensor`: PDF p.7, §6: a four-wire tensor, in AI AO BI BO order. Reuse the frozen Bool-indexed Pauli gates, with computational labels 0=false and 1=true.
--   - `ocbProcess`: PDF p.7, Eq.(35): the exact OCB matrix; the factor is 1/4, not 1/16.
--   - `optProcess`: PDF p.7, Eq.(37): the exact Wopt matrix, without a claim about purifiability.
--   - `qubitLaboratories`: PDF p.7: the common qubit laboratory dimensions, independently of global wires.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, https://arxiv.org/abs/1611.08535v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

/-!
Statements from Araújo, Feix, Navascués and Brukner, arXiv:1611.08535v4.
The local process interface uses fixed finite computational bases and unnormalized,
input-first Choi operators. Physical dimensions are positive natural numbers.
Theorem 4 below is explicitly restricted to the balanced domain required by
its proof; the unrestricted printed statement remains deferred.
Pauli gates come from the frozen Gates module. Other local names distinguish
this six-wire, arbitrary-ancilla process interface from incompatible accepted
interfaces with coincidentally matching short names.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF pp.2,10: positive dimensions in wire order P, AI, AO, BI, BO, F. -/
abbrev ProcessWireDimensions := Fin 6 → ℕ+

/-- PDF p.2: the fixed computational basis of all six wires. -/
abbrev ProcessBasis (d : ProcessWireDimensions) := (s : Fin 6) → Fin (d s : ℕ)

/-- PDF p.2: a process operator, without any validity condition imposed by its type. -/
abbrev ProcessMatrix (d : ProcessWireDimensions) := Matrix (ProcessBasis d) (ProcessBasis d) ℂ

/-- PDF pp.2–3: coordinate insertion in the fixed six-wire order. -/
def processCoordinates (d : ProcessWireDimensions) (p : Fin (d 0 : ℕ)) (ai : Fin (d 1 : ℕ))
    (ao : Fin (d 2 : ℕ)) (bi : Fin (d 3 : ℕ)) (bo : Fin (d 4 : ℕ))
    (f : Fin (d 5 : ℕ)) : ProcessBasis d :=
  Fin.cases p (Fin.cases ai (Fin.cases ao (Fin.cases bi
    (Fin.cases bo (Fin.cases f (fun i => Fin.elim0 i))))))

/-- PDF p.10, Eq.(40): |U>><<U| in input-first order, with no dimension factor. -/
def unitaryChannelProjector {I O : Type*} (U : Matrix O I ℂ) : Matrix (I × O) (I × O) ℂ :=
  fun x y => U x.2 x.1 * conj (U y.2 y.1)

/-- PDF pp.3–4: reversible unitarity between possibly differently labelled finite bases.
Both equations are required; an isometry into a larger space is excluded. -/
def IsReversibleMatrix {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (U : Matrix O I ℂ) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- PDF p.4: an isometry need only satisfy the first of the two unitary equations. -/
def IsIsometricMatrix {I O : Type*} [Fintype O] [DecidableEq I]
    (V : Matrix O I ℂ) : Prop := Vᴴ * V = 1

/-- PDF p.11, before Eq.(45): the independent finite Choi criterion for a local CPTP map. -/
def IsCPTPChoi {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (J : Matrix (I × O) (I × O) ℂ) : Prop :=
  J.PosSemidef ∧ ∀ i j, (∑ o, J (i,o) (j,o)) = if i = j then 1 else 0

/-- PDF pp.3,10: the CJ operator of some reversible unitary channel. -/
def IsUnitaryChoi {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (J : Matrix (I × O) (I × O) ℂ) : Prop :=
  ∃ U : Matrix O I ℂ, IsReversibleMatrix U ∧ J = unitaryChannelProjector U

/-- PDF p.2, Eq.(1), and p.11, Eq.(43): link W with arbitrary ancillary local CJ
operators. The laboratory indices are contracted bilinearly (no conjugation).
All off-diagonal blocks of the ancillary wires are retained. -/
def linkLaboratories (d : ProcessWireDimensions) (aIn aOut bIn bOut : ℕ+) (W : ProcessMatrix d)
    (A : Matrix ((Fin (d 1 : ℕ) × Fin (aIn : ℕ)) ×
      (Fin (d 2 : ℕ) × Fin (aOut : ℕ)))
      ((Fin (d 1 : ℕ) × Fin (aIn : ℕ)) ×
      (Fin (d 2 : ℕ) × Fin (aOut : ℕ))) ℂ)
    (B : Matrix ((Fin (d 3 : ℕ) × Fin (bIn : ℕ)) ×
      (Fin (d 4 : ℕ) × Fin (bOut : ℕ)))
      ((Fin (d 3 : ℕ) × Fin (bIn : ℕ)) ×
      (Fin (d 4 : ℕ) × Fin (bOut : ℕ))) ℂ) :
    Matrix ((Fin (d 0 : ℕ) × Fin (aIn : ℕ) × Fin (bIn : ℕ)) ×
      (Fin (d 5 : ℕ) × Fin (aOut : ℕ) × Fin (bOut : ℕ)))
      ((Fin (d 0 : ℕ) × Fin (aIn : ℕ) × Fin (bIn : ℕ)) ×
      (Fin (d 5 : ℕ) × Fin (aOut : ℕ) × Fin (bOut : ℕ))) ℂ :=
  fun u v => ∑ x : ProcessBasis d, ∑ y : ProcessBasis d,
    if x 0 = u.1.1 ∧ y 0 = v.1.1 ∧ x 5 = u.2.1 ∧ y 5 = v.2.1 then
      W x y * A ((x 1,u.1.2.1),(x 2,u.2.2.1))
        ((y 1,v.1.2.1),(y 2,v.2.2.1)) *
      B ((x 3,u.1.2.2),(x 4,u.2.2.2))
        ((y 3,v.1.2.2),(y 4,v.2.2.2)) else 0

/-- PDF pp.2–3,11: operational process validity, independently of LV. Every positive
ancillary dimension and every pair of local CPTP operators is tested. -/
def IsValidProcess {d : ProcessWireDimensions} (W : ProcessMatrix d) : Prop :=
  ∀ (aIn aOut bIn bOut : ℕ+) A B,
    IsCPTPChoi A → IsCPTPChoi B → IsCPTPChoi (linkLaboratories d aIn aOut bIn bOut W A B)

/-- PDF p.3, Definition 1: purity tests all compatible unitary laboratories on all
ancillary wires, including the enlarged SWAP laboratories in Eq.(9). Validity is
kept separate so Theorem 2 does not silently assume arbitrary unitaries are processes. -/
def IsPureProcess {d : ProcessWireDimensions} (W : ProcessMatrix d) : Prop :=
  ∀ (aIn aOut bIn bOut : ℕ+) U V,
    IsReversibleMatrix U → IsReversibleMatrix V →
      IsUnitaryChoi (linkLaboratories d aIn aOut bIn bOut W (unitaryChannelProjector U) (unitaryChannelProjector V))

/-- PDF pp.3–4: a matrix from P AO BO to AI BI F, in its input-first CJ wire order. -/
def processProjector {d : ProcessWireDimensions}
    (U : Matrix (Fin (d 1 : ℕ) × Fin (d 3 : ℕ) × Fin (d 5 : ℕ))
      (Fin (d 0 : ℕ) × Fin (d 2 : ℕ) × Fin (d 4 : ℕ)) ℂ) : ProcessMatrix d :=
  fun x y => U (x 1,x 3,x 5) (x 0,x 2,x 4) *
    conj (U (y 1,y 3,y 5) (y 0,y 2,y 4))

/-- PDF p.11, Eq.(53): replace the wires in s by maximally mixed identity factors,
preserving the order of every other wire. Strictly positive dimensions guard division. -/
def replaceWires {d : ProcessWireDimensions} (s : Finset (Fin 6)) (W : ProcessMatrix d) :
    ProcessMatrix d :=
  fun x y => if ∀ i ∈ s, x i = y i then
    ((∏ i ∈ s, (d i : ℕ) : ℕ) : ℂ)⁻¹ *
      ∑ z : ProcessBasis d,
        if ∀ i, i ∉ s → z i = x i then
          W z (fun i => if i ∈ s then z i else y i) else 0
    else 0

/-- PDF p.12, Eq.(64): the complete bipartite linear normalization projector.
The order of wire labels is P, AI, AO, BI, BO, F. -/
def validSubspaceProjector {d : ProcessWireDimensions} (W : ProcessMatrix d) : ProcessMatrix d :=
  W - replaceWires {5} W + replaceWires {2,5} W + replaceWires {4,5} W -
    replaceWires {2,4,5} W - replaceWires {1,2,5} W + replaceWires {1,2,4,5} W -
    replaceWires {3,4,5} W + replaceWires {2,3,4,5} W -
    replaceWires {1,2,3,4,5} W + replaceWires {0,1,2,3,4,5} W

/-- PDF p.6, before Eq.(21): the complementary projector 1-LV. -/
def invalidSubspaceProjector {d : ProcessWireDimensions} (W : ProcessMatrix d) : ProcessMatrix d :=
  W - validSubspaceProjector W

/-- PDF pp.5–6: a process-vector outer product; these vectors are unnormalized. -/
def vectorOuter {I : Type*} (v w : I → ℂ) : Matrix I I ℂ :=
  fun x y => v x * conj (w y)

/-- PDF pp.5–6, Eq.(24): the usual conjugate-linear-first finite inner product. -/
def processVectorPairing {I : Type*} [Fintype I] (v w : I → ℂ) : ℂ :=
  ∑ x, conj (v x) * w x

/-- PDF pp.4–6: fixed laboratory dimensions, with independently specified global wires. -/
def laboratorySignature (d : Fin 4 → ℕ+) (p f : ℕ+) : ProcessWireDimensions :=
  ![p,d 0,d 1,d 2,d 3,f]

-- the wire dimensions of the two signatures are compared by unfolding `![...]`; prove2me's checker needs more than
-- the default 200000 heartbeats here
set_option maxHeartbeats 800000 in
/-- PDF p.4, Definition 3, specialized to trivial original P,F: insert |0> in Pprime
and trace Fprime. The two new global dimensions are independent. -/
def recoverProcess {d : Fin 4 → ℕ+} {p f : ℕ+}
    (S : ProcessMatrix (laboratorySignature d p f)) :
    ProcessMatrix (laboratorySignature d 1 1) :=
  fun x y => ∑ t : Fin (f : ℕ),
    S (processCoordinates (laboratorySignature d p f) 0 (x 1) (x 2) (x 3) (x 4) t)
      (processCoordinates (laboratorySignature d p f) 0 (y 1) (y 2) (y 3) (y 4) t)

/-- PDF p.4, Definition 3: physical purification by an operationally valid pure process,
with unrestricted positive new-past and new-future dimensions. -/
def IsPurifiable {d : Fin 4 → ℕ+}
    (W : ProcessMatrix (laboratorySignature d 1 1)) : Prop :=
  ∃ (p f : ℕ+) (S : ProcessMatrix (laboratorySignature d p f)),
    IsValidProcess S ∧ IsPureProcess S ∧ recoverProcess S = W

/-- PDF pp.5–6, Eq.(19): the complete positive spectral support, with multiplicity.
This is chosen spectral data, not extra unproved process constraints. -/
structure SupportSpectrum {d : Fin 4 → ℕ+}
    (W : ProcessMatrix (laboratorySignature d 1 1)) where
  rank : ℕ+
  rank_eq : (rank : ℕ) = Matrix.rank W
  values : Fin (rank : ℕ) → ℝ
  positive : ∀ i, 0 < values i
  vectors : Fin (rank : ℕ) → ProcessBasis (laboratorySignature d 1 1) → ℂ
  orthonormal : ∀ i j, processVectorPairing (vectors i) (vectors j) = if i = j then 1 else 0
  decomposition : ∀ x y, W x y = ∑ i, (values i : ℂ) * vectors i x * conj (vectors i y)

/-- PDF pp.5–6, Eqs.(20),(23): the canonical positive-matrix purification, with future
basis indexed by the spectral support. There is no normalization to trace one. -/
def canonicalVector {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} (e : SupportSpectrum W) :
    ProcessBasis (laboratorySignature d 1 e.rank) → ℂ :=
  fun x => (Real.sqrt (e.values (x 5)) : ℂ) *
    e.vectors (x 5) (processCoordinates (laboratorySignature d 1 1) 0 (x 1) (x 2) (x 3) (x 4) 0)

/-- PDF p.6, Eqs.(23)–(24): all prescribed vectors, bilinear LV constraints and
orthogonality with squared norm dAO*dBO. -/
def IsCompletion {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} (e : SupportSpectrum W)
    (w : Fin (e.rank : ℕ) → ProcessBasis (laboratorySignature d 1 e.rank) → ℂ) : Prop :=
  w 0 = canonicalVector e ∧ ∀ i j,
    invalidSubspaceProjector (vectorOuter (w i) (w j)) = 0 ∧
    processVectorPairing (w i) (w j) = if i = j then ((d 1 : ℕ) * (d 3 : ℕ) : ℂ) else 0

/-- PDF p.6, Eq.(25): the actual matrix reconstructed by using wi as the past slices.
Its input basis is Pprime AO BO and its output basis AI BI Fprime. -/
def reconstructedUnitary {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} (e : SupportSpectrum W)
    (w : Fin (e.rank : ℕ) → ProcessBasis (laboratorySignature d 1 e.rank) → ℂ) :
    Matrix (Fin (d 0 : ℕ) × Fin (d 2 : ℕ) × Fin (e.rank : ℕ))
      (Fin (e.rank : ℕ) × Fin (d 1 : ℕ) × Fin (d 3 : ℕ)) ℂ :=
  fun o i => w i.1
    (processCoordinates (laboratorySignature d 1 e.rank) 0 o.1 i.2.1 o.2.1 i.2.2 o.2.2)

/-- PDF p.4: a concrete dimension-increasing isometry, with every laboratory wire
and P trivial, and F two-dimensional. -/
def stateOutputSignature : ProcessWireDimensions := ![1,1,1,1,1,2]

/-- PDF p.4: the isometry sends the only global input basis vector to future |0>. -/
def stateOutputIsometry :
    Matrix (Fin (stateOutputSignature 1 : ℕ) × Fin (stateOutputSignature 3 : ℕ) ×
      Fin (stateOutputSignature 5 : ℕ))
      (Fin (stateOutputSignature 0 : ℕ) × Fin (stateOutputSignature 2 : ℕ) ×
      Fin (stateOutputSignature 4 : ℕ)) ℂ :=
  fun o _ => if o.2.2 = 0 then 1 else 0

/-- PDF pp.12–13: total isotropy is a zero compression, not invariance or membership
in the kernel of C. Zero-dimensional ambient spaces are permitted. -/
def IsTotallyIsotropic {I : Type*} [Fintype I] (C : Matrix I I ℂ)
    (S : Submodule ℂ (I → ℂ)) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, ∑ i, ∑ j, conj (v i) * C i j * w j = 0

/-- PDF p.12: positive eigenvalues counted with multiplicity. -/
def positiveCount {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℂ} (hC : C.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hC.eigenvalues i).card

/-- PDF p.12: strictly negative eigenvalues counted with multiplicity. -/
def negativeCount {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℂ} (hC : C.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hC.eigenvalues i < 0).card

/-- PDF p.12: zero eigenvalues counted with multiplicity. -/
def zeroCount {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℂ} (hC : C.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hC.eigenvalues i = 0).card

/-- PDF p.12: the claimed greatest null-square size, expressed without any supremum. -/
def nullSquareSize {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℂ} (hC : C.IsHermitian) : ℕ :=
  min (positiveCount hC) (negativeCount hC) + zeroCount hC

/-- PDF p.6, Eq.(26): matrix of 1-LV on input-first vectorized operators.
The coordinate pair (a,b) represents the operator entry (b,a). -/
def vectorizedComplement {d : ProcessWireDimensions} :
    Matrix (ProcessBasis d × ProcessBasis d) (ProcessBasis d × ProcessBasis d) ℂ :=
  fun a b => invalidSubspaceProjector (Matrix.single b.2 b.1 1) a.2 a.1

/-- PDF p.6, Eq.(28): OW is computed from the canonical vector. Its ket factor
is conjugated w0, so its bra factor is w0, using the conjugate-linear-first convention. -/
def purificationKernelOperator {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} (e : SupportSpectrum W) :
    ProcessMatrix (laboratorySignature d 1 e.rank) :=
  fun v w => ∑ a, ∑ b, canonicalVector e a *
    vectorizedComplement (a,v) (b,w) * conj (canonicalVector e b)

/-- PDF p.6, Eqs.(28)–(30): an explicit orthonormal basis of the entire kernel of OW.
No basis-independence of the eventual numerical bound is asserted. -/
structure KernelBasisData {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} (e : SupportSpectrum W) where
  dimension : ℕ
  vectors : Fin dimension → ProcessBasis (laboratorySignature d 1 e.rank) → ℂ
  orthonormal : ∀ i j, processVectorPairing (vectors i) (vectors j) = if i = j then 1 else 0
  kernel_span : (Submodule.span ℂ (Set.range vectors) :
      Set (ProcessBasis (laboratorySignature d 1 e.rank) → ℂ)) =
    {v | (purificationKernelOperator e).mulVec v = 0}

/-- PDF p.6, Eq.(30): (conj R tensor R) Pi (transpose R tensor adjoint R), with
Ria=conj(ri(a)). The entry formula retains the source's conjugations and factor order. -/
def compressedOperator {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} {e : SupportSpectrum W}
    (b : KernelBasisData e) :
    Matrix (Fin b.dimension × Fin b.dimension) (Fin b.dimension × Fin b.dimension) ℂ :=
  fun i j => ∑ a, ∑ v, ∑ c, ∑ w,
    b.vectors i.1 a * conj (b.vectors i.2 v) * vectorizedComplement (a,v) (c,w) *
      conj (b.vectors j.1 c) * b.vectors j.2 w

/-- PDF p.7, Eq.(31): a full orthonormal eigenbasis of the computed compression.
Filtering its strictly nonzero eigenvalues below gives exactly the source's mk family. -/
structure CompressionSpectrum {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} {e : SupportSpectrum W}
    (b : KernelBasisData e) where
  values : (Fin b.dimension × Fin b.dimension) → ℝ
  vectors : (Fin b.dimension × Fin b.dimension) → (Fin b.dimension × Fin b.dimension) → ℂ
  orthonormal : ∀ i j, processVectorPairing (vectors i) (vectors j) = if i = j then 1 else 0
  spans : Submodule.span ℂ (Set.range vectors) = ⊤
  eigenvectors : ∀ i, (compressedOperator b).mulVec (vectors i) =
    (values i : ℂ) • vectors i

/-- PDF p.7, Eq.(31): the complete nonzero-eigenvalue index set, possibly empty. -/
abbrev NonzeroModes {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} {e : SupportSpectrum W}
    {b : KernelBasisData e} (s : CompressionSpectrum b) :=
  {i : Fin b.dimension × Fin b.dimension // s.values i ≠ 0}

/-- PDF p.7, Eq.(32): |transpose Mk>>=mk, with the same input-first CJ ordering.
The intervening printed bra identity has a transpose discrepancy in this convention;
only the printed reshaping and its inertia counts are used here. Transposing every
constraint leaves its eigenvalues and the test bound unchanged. -/
def modeMatrix {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} {e : SupportSpectrum W}
    {b : KernelBasisData e} (s : CompressionSpectrum b) (k : NonzeroModes s) :
    Matrix (Fin b.dimension) (Fin b.dimension) ℂ := fun i j => s.vectors k.val (i,j)

/-- PDF p.7, Eq.(32): M+M† for false and i(M-M†) for true. Writing the latter as
(iM)+(iM)† gives a Hermitian matrix by construction, without adding a hypothesis. -/
def constraintMatrix {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} {e : SupportSpectrum W}
    {b : KernelBasisData e} (s : CompressionSpectrum b) (k : NonzeroModes s × Bool) :
    Matrix (Fin b.dimension) (Fin b.dimension) ℂ :=
  let M := if k.2 then Complex.I • modeMatrix s k.1 else modeMatrix s k.1
  M + Mᴴ

/-- PDF p.7, Eq.(34): the actual minimum over the explicit Hermitian constraints.
Only the empty-family extension is top, rather than a junk natural-number zero;
the footnote theorem treats that case separately. -/
def testBound {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} {e : SupportSpectrum W}
    {b : KernelBasisData e} (s : CompressionSpectrum b) : WithTop ℕ :=
  Finset.univ.inf fun k : NonzeroModes s × Bool =>
    (nullSquareSize (C := constraintMatrix s k)
      (Matrix.isHermitian_add_transpose_self
        (if k.2 then Complex.I • modeMatrix s k.1 else modeMatrix s k.1)) : WithTop ℕ)

/-- PDF pp.6–7: lift the kernel coordinates back to the laboratory/future vector. -/
def liftKernelVector {d : Fin 4 → ℕ+}
    {W : ProcessMatrix (laboratorySignature d 1 1)} {e : SupportSpectrum W}
    (b : KernelBasisData e) (v : Fin b.dimension → ℂ) :
    ProcessBasis (laboratorySignature d 1 e.rank) → ℂ :=
  fun x => ∑ i, v i * b.vectors i x

/-- PDF p.7, §6: four qubit laboratory wires, with trivial P and F. -/
def qubitSignature : ProcessWireDimensions := ![1,2,2,2,2,1]

/-- PDF p.7, §6: a four-wire tensor, in AI AO BI BO order. Reuse the frozen
Bool-indexed Pauli gates, with computational labels 0=false and 1=true. -/
def laboratoryTensor (A B C D : Matrix Bool Bool ℂ) : ProcessMatrix qubitSignature :=
  fun x y => A (decide (x 1 ≠ 0)) (decide (y 1 ≠ 0)) *
    B (decide (x 2 ≠ 0)) (decide (y 2 ≠ 0)) *
    C (decide (x 3 ≠ 0)) (decide (y 3 ≠ 0)) *
    D (decide (x 4 ≠ 0)) (decide (y 4 ≠ 0))

/-- PDF p.7, Eq.(35): the exact OCB matrix; the factor is 1/4, not 1/16. -/
def ocbProcess : ProcessMatrix qubitSignature :=
  (1 / 4 : ℂ) • (laboratoryTensor 1 1 1 1 + (1 / (Real.sqrt 2 : ℂ)) •
    (laboratoryTensor 1 pauliZ pauliZ 1 + laboratoryTensor pauliZ 1 pauliX pauliZ))

/-- PDF p.7, Eq.(37): the exact Wopt matrix, without a claim about purifiability. -/
def optProcess : ProcessMatrix qubitSignature :=
  (1 / 4 : ℂ) • (laboratoryTensor 1 1 1 1 + (1 / (Real.sqrt 3 : ℂ)) •
    laboratoryTensor pauliZ 1 pauliX pauliZ + (((Real.sqrt 3 : ℂ) - 1) / 3) •
    (laboratoryTensor 1 pauliX pauliX 1 + laboratoryTensor 1 pauliY pauliY 1 +
      laboratoryTensor 1 pauliZ pauliZ 1))

/-- PDF p.7: the common qubit laboratory dimensions, independently of global wires. -/
def qubitLaboratories : Fin 4 → ℕ+ := ![2,2,2,2]

/-- Sanity: an empty mode family has top bound, never natural-number zero. -/
example {d : Fin 4 → ℕ+} {W : ProcessMatrix (laboratorySignature d 1 1)}
    {e : SupportSpectrum W} {b : KernelBasisData e} (s : CompressionSpectrum b)
    (hempty : ∀ k, s.values k = 0) : testBound s = ⊤ := by
  letI : IsEmpty (NonzeroModes s) := ⟨fun k => k.property (hempty k.val)⟩
  simp [testBound]

/-- Sanity: the qubit signature agrees exactly with the laboratory/past/future split. -/
example : laboratorySignature qubitLaboratories 1 1 = qubitSignature := by
  ext i
  fin_cases i <;> rfl

/-- Sanity: the tensor identity has diagonal entry one, without a normalization factor. -/
example (x : ProcessBasis qubitSignature) : laboratoryTensor 1 1 1 1 x x = 1 := by
  simp [laboratoryTensor, Matrix.one_apply_eq]

/-- Sanity: dependent coordinate insertion selects the future wire without a cast. -/
example (d : ProcessWireDimensions) (p : Fin (d 0 : ℕ)) (ai : Fin (d 1 : ℕ))
    (ao : Fin (d 2 : ℕ)) (bi : Fin (d 3 : ℕ)) (bo : Fin (d 4 : ℕ))
    (f : Fin (d 5 : ℕ)) : processCoordinates d p ai ao bi bo f 5 = f := by
  rfl

/-- Sanity: the imported Pauli convention sends |1> to -i|0> under Y. -/
example : QAlgorithms.pauliY false true = -Complex.I := by
  rfl

/-- Sanity: the one-dimensional identity has unnormalized CJ entry one. -/
example : unitaryChannelProjector (1 : Matrix (Fin 1) (Fin 1) ℂ) (0,0) (0,0) = 1 := by
  simp [unitaryChannelProjector]

/-- Sanity: both inverse equations hold for the identity, in every finite dimension. -/
example {I : Type*} [Fintype I] [DecidableEq I] :
    IsReversibleMatrix (1 : Matrix I I ℂ) := by
  simp [IsReversibleMatrix]

/-- Sanity: a zero process vector gives the zero operator, without a hidden offset. -/
example {d : ProcessWireDimensions} : processProjector (d := d) 0 = 0 := by
  ext x y
  simp [processProjector]

/-- Sanity: the zero Hermitian form is totally isotropic on every subspace. -/
example {I : Type*} [Fintype I] (S : Submodule ℂ (I → ℂ)) :
    IsTotallyIsotropic (0 : Matrix I I ℂ) S := by
  intro v hv w hw
  simp

end QAlgorithms.Papers.Independent.Intake100.P46


