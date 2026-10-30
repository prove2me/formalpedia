-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28
-- name    : QAlgorithms_Papers_Independent_Extend50_P28
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:07:32.183375+00:00
-- url     : https://prove2.me/theorems/77f6865a-c464-465f-a8ab-86f374c681f0
-- title:
--   Definitions for Simplified formalism of the algebra of partially transposed permutation operators with applications
-- statement:
--   The objects the formalized statements of *Simplified formalism of the algebra of partially transposed permutation operators with applications* (arXiv:1708.02434) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `irrepDim`: PDF pp.3,10: actual Specht dimension, distinguished from tensor multiplicity.
--   - `oneBoxBranch`: PDF pp.9–10: one-box branching. The types already fix consecutive sizes.
--   - `LowerShapes`: PDF p.9: removable lower shapes in a fixed upper shape.
--   - `UpperShapes`: PDF pp.10,13: every addable upper shape, including zero Gram branches.
--   - `PRIRBlockIndex`: PDF p.10: grouped PRIR indices before a coordinate reordering.
--   - `extendPerm`: PDF pp.9–13: the subgroup embedding fixes the last letter.
--   - `cosetRep`: PDF pp.10–13: coset representative, including the identity at the last letter.
--   - `lowerPerm`: PDF p.12: recover the lower permutation on the subgroup image. Outside that image this total helper returns identity; inducedAction only evaluates it in the branch where the argument fixes the last letter.
--   - `CoherentPRIR`: PDF pp.9–10, Definition 22: coherent based PRIRs. Character equalities pin each representation to the actual shape-labelled Specht irrep, rather than arbitrary blocks. The coordinate equivalence is precisely regrouping (30). The restriction condition uses one common lower matrix for each label. Real transposition entries implement Remark 9. None of (32)–(60) is an assumption here.
--   - `prirBlock`: PDF p.10: extract a block using its specified, shared lower-shape indices.
--   - `weightedBlock`: PDF pp.10–12: weighted alpha diagonal block over every induced branch.
--   - `inducedAction`: PDF p.13, Eq.(54): the concrete induced coset action.
--   - `ZColumn`: PDF p.13: column labels of Z, flattened only within each upper irrep. The inverse of R.coord restores precisely the printed (nu,xi,j) labels.
--   - `explicitZR`: PDF p.13, Eq.(55): explicit normalized matrix, with all addable branches.
--   - `prirDirectSumAction`: PDF p.13, Eq.(56): full block diagonal upper action, without height truncation.
--   - `columnT`: PDF p.14, Eq.(59): the explicitly constructed column vectors.
--   - `gramQ`: PDF p.5, Definition 7: dI on diagonal coset blocks; ordinary transposition blocks off diagonal. The conjugated permutation fixes the last letter.
--   - `contentEigenvalue`: PDF pp.6–7, Eqs.(9)–(10): d plus the signed content of the added cell. The sum has one term for a genuine one-box branch; diagonal additions have content zero.
--   - `contentDiagonal`: PDF p.14, Eq.(60): a branch eigenvalue on each internal coordinate.
--   - `lastPartialTranspose`: PDF pp.3–4: partial transpose on the last factor in the fixed tensor basis. N counts preceding factors; the matrix acts on N+1 factors.
--   - `transposedSwap`: PDF p.21, Eq.(100): unnormalized partially transposed swap T_a.
--   - `pbtOperator`: PDF p.21: rho is the concrete sum of N=n-1 unnormalized generators.
--   - `normalizedSignal`: PDF p.21, Eq.(100): normalized individual signal; resource pairs are normalized.
--   - `normalizedPBTOperator`: PDF p.21: rho-tilde is the sum of signals, not a trace-one state for N>1.
--   - `pbtFidelity`: PDF p.21, Eq.(99), equivalently p.24, Eq.(121): square-root-measurement entanglement fidelity, using the actual normalized signals and their sum. The support inverse is imported Mathlib cfc with x mapped to (sqrt x) inverse, which is zero at zero. Completing the measurement on the common signal kernel adds zero to this trace. For d=0 this total helper returns zero; every theorem assumes d>=2.
--   - `tensorIntertwiners`: PDF p.3: intertwiner space from the actual Specht irrep to the actual permutation representation. Its dimension is the occurrence multiplicity; no character-average theorem is used as a definition or assumption.
--   - `tensorMultiplicity`: PDF pp.3,15–16: actual tensor occurrence multiplicity.
--   - `cycleCount`: PDF p.22: cycle count includes fixed points; S(0) has zero cycles.
--   - `eigenMultiplicity`: PDF p.22: geometric eigenvalue multiplicity, equal to the spectral multiplicity for the Hermitian operator rho.
--   - `inverseRoot`: PDF p.26, Proposition 59: the printed domain lambda>=0 is corrected to lambda>0, as required by its use on positive eigenvalues on p.28. The printed second derivative is 3/4 times lambda^(-5/2), verified from the PDF image.
--   - `PhysicalLower`: PDF pp.17–19: physical lower shapes, including the empty diagram.
--   - `PhysicalUpper`: PDF pp.17–19: physical upper shapes, independent of any chosen predecessor.
--   - `Retained`: PDF pp.17–19: all retained one-box branches above a given alpha.
--   - `embeddedProjector`: PDF p.17, Eq.(76), and p.18, Eq.(83): character projector embedded in the specified tensor prefix. The group embeddings are fixed in every invocation.
--   - `subgroupMatrixUnit`: PDF p.17, Eq.(76): ordinary lower-group matrix units on the physical n=k+2 factor space, with the source's inverse permutation and reversed j,i entry.
--   - `constructedE`: PDF p.17, Eq.(75): actual physical matrix product. No multiplication law or isotypic-basis equality is built into the definition. Physical shapes guarantee positive tensor multiplicities; nonbranch choices are allowed for Remark 41.
--   - `aggregatedP`: PDF p.19, Eq.(96): sum of the constructed internal diagonal units. This is distinct from either ordinary central projector P_mu or P_alpha.
--   - `unitSynthesis`: PDF pp.19–20: the linear combination of the specified physical units.
--   - `IsMatrixAlgebraModel`: PDF pp.19–20: precise algebra-isomorphism-onto-the-span assertion. The explicit synthesis map is complex linear, multiplicative, injective, and has exactly the physical span as image. Thus even a proper nonunital physical corner is isomorphic to the complete source matrix algebra.
--   - `secondKindIntertwiners`: PDF pp.8,25: actual copies of the second-kind module inside physical tensor space. They intertwine the full ordinary subgroup and are annihilated by every moving-last-letter swap generator. This independently defines occurrence multiplicity, with no use of either (25) or (129).
--   - `secondKindMultiplicity`: PDF p.25: M_nu is actual physical second-kind occurrence multiplicity.
--   - `SecondShapes`: PDF p.25: second-kind labels have strictly fewer than d rows.
--   - `firstKindDimension`: PDF pp.5,8,25: the independently computed dimension of the first-kind carrier, namely the range of Q. No diagonal rank formula is an assumption.
--   - `naturalTrace`: PDF pp.23–24, Eqs.(112),(118): actual full-tensor unnormalized trace, using the support inverse, and retaining its complex value.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, https://arxiv.org/abs/1708.02434v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition

/-!
Statements from arXiv:1708.02434v2. All new objects are paper-local and computed
from tensor permutations or actual Specht modules. Abstract PRIR coordinates
carry only representation and restriction data, never the summation identities.
The physical-carrier statements requiring independently identified mixed-algebra
isotypic subspaces are deferred in HARD.md. Compilation awaits the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/- PDF pp.3,9: notation for the imported partition type, with no height truncation. -/
local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

/-- PDF pp.3,10: actual Specht dimension, distinguished from tensor multiplicity. -/
def irrepDim {h k : ℕ} (alpha : QAlgorithms.Schur.Partition h k) : ℕ :=
  Module.finrank ℂ (QAlgorithms.Schur.spechtSpace alpha)

/-- PDF pp.9–10: one-box branching. The types already fix consecutive sizes. -/
def oneBoxBranch {k : ℕ} (alpha : Shape k) (nu : Shape (k + 1)) : Prop :=
  alpha.val.cells ⊆ nu.val.cells

/-- PDF p.9: removable lower shapes in a fixed upper shape. -/
abbrev LowerShapes {k : ℕ} (nu : Shape (k + 1)) :=
  {alpha : Shape k // oneBoxBranch alpha nu}

/-- PDF pp.10,13: every addable upper shape, including zero Gram branches. -/
abbrev UpperShapes {k : ℕ} (alpha : Shape k) :=
  {nu : Shape (k + 1) // oneBoxBranch alpha nu}

/-- PDF p.10: grouped PRIR indices before a coordinate reordering. -/
abbrev PRIRBlockIndex {k : ℕ} (nu : Shape (k + 1)) :=
  (alpha : LowerShapes nu) × Fin (irrepDim alpha.val)

/-- PDF pp.9–13: the subgroup embedding fixes the last letter. -/
def extendPerm {k : ℕ} (sigma : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.permCongr (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1))
    (Equiv.Perm.sumCongr sigma (1 : Equiv.Perm (Fin 1)))

/-- PDF pp.10–13: coset representative, including the identity at the last letter. -/
def cosetRep {k : ℕ} (a : Fin (k + 1)) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.swap a (Fin.last k)

/-- PDF p.12: recover the lower permutation on the subgroup image. Outside that
image this total helper returns identity; inducedAction only evaluates it in the
branch where the argument fixes the last letter. -/
def lowerPerm {k : ℕ} (sigma : Equiv.Perm (Fin (k + 1))) : Equiv.Perm (Fin k) :=
  if h : ∃ tau : Equiv.Perm (Fin k), extendPerm tau = sigma then Classical.choose h else 1

/-- PDF pp.9–10, Definition 22: coherent based PRIRs. Character equalities pin each
representation to the actual shape-labelled Specht irrep, rather than arbitrary
blocks. The coordinate equivalence is precisely regrouping (30). The restriction
condition uses one common lower matrix for each label. Real transposition entries
implement Remark 9. None of (32)–(60) is an assumption here. -/
structure CoherentPRIR (k : ℕ) where
  lower : (alpha : Shape k) → Equiv.Perm (Fin k) →
    Matrix (Fin (irrepDim alpha)) (Fin (irrepDim alpha)) ℂ
  upper : (nu : Shape (k + 1)) → Equiv.Perm (Fin (k + 1)) →
    Matrix (Fin (irrepDim nu)) (Fin (irrepDim nu)) ℂ
  lower_one : ∀ alpha, lower alpha 1 = 1
  lower_mul : ∀ alpha sigma tau, lower alpha (sigma * tau) = lower alpha sigma * lower alpha tau
  upper_one : ∀ nu, upper nu 1 = 1
  upper_mul : ∀ nu sigma tau, upper nu (sigma * tau) = upper nu sigma * upper nu tau
  lower_unitary : ∀ alpha sigma, (lower alpha sigma)ᴴ * lower alpha sigma = 1
  upper_unitary : ∀ nu sigma, (upper nu sigma)ᴴ * upper nu sigma = 1
  lower_character : ∀ alpha sigma, (lower alpha sigma).trace =
    QAlgorithms.Schur.spechtCharacter alpha sigma
  upper_character : ∀ nu sigma, (upper nu sigma).trace =
    QAlgorithms.Schur.spechtCharacter nu sigma
  lower_positive : ∀ (alpha : Shape k), 0 < irrepDim alpha
  upper_positive : ∀ (nu : Shape (k + 1)), 0 < irrepDim nu
  coord : (nu : Shape (k + 1)) → PRIRBlockIndex nu ≃ Fin (irrepDim nu)
  restriction : ∀ nu (alpha beta : LowerShapes nu)
    (i : Fin (irrepDim alpha.val)) (j : Fin (irrepDim beta.val)) sigma,
    upper nu (extendPerm sigma) (coord nu ⟨alpha,i⟩) (coord nu ⟨beta,j⟩) =
      if h : alpha.val = beta.val then
        lower alpha.val sigma i (Fin.cast (congrArg irrepDim h.symm) j) else 0
  transposition_real : ∀ nu a i j, (upper nu (cosetRep a) i j).im = 0

/-- PDF p.10: extract a block using its specified, shared lower-shape indices. -/
def prirBlock {k : ℕ} (R : CoherentPRIR k) (nu : Shape (k + 1))
    (alpha beta : Shape k) (ha : oneBoxBranch alpha nu) (hb : oneBoxBranch beta nu)
    (sigma : Equiv.Perm (Fin (k + 1)))
    (i : Fin (irrepDim alpha)) (j : Fin (irrepDim beta)) : ℂ :=
  R.upper nu sigma (R.coord nu ⟨⟨alpha,ha⟩,i⟩) (R.coord nu ⟨⟨beta,hb⟩,j⟩)

/-- PDF pp.10–12: weighted alpha diagonal block over every induced branch. -/
def weightedBlock {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k)
    (sigma : Equiv.Perm (Fin (k + 1)))
    (i j : Fin (irrepDim alpha)) : ℂ :=
  ∑ nu : UpperShapes alpha, (irrepDim nu.val : ℂ) *
    prirBlock R nu.val alpha alpha nu.property nu.property sigma i j

/-- PDF p.13, Eq.(54): the concrete induced coset action. -/
def inducedAction {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k)
    (sigma : Equiv.Perm (Fin (k + 1))) :
    Matrix (Fin (k + 1) × Fin (irrepDim alpha))
      (Fin (k + 1) × Fin (irrepDim alpha)) ℂ :=
  fun p q => if p.1 = sigma q.1 then
    R.lower alpha (lowerPerm (cosetRep p.1 * sigma * cosetRep q.1)) p.2 q.2 else 0

/-- PDF p.13: column labels of Z, flattened only within each upper irrep.
The inverse of R.coord restores precisely the printed (nu,xi,j) labels. -/
abbrev ZColumn {k : ℕ} (alpha : Shape k) :=
  (nu : UpperShapes alpha) × Fin (irrepDim nu.val)

/-- PDF p.13, Eq.(55): explicit normalized matrix, with all addable branches. -/
def explicitZR {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) :
    Matrix (Fin (k + 1) × Fin (irrepDim alpha)) (ZColumn alpha) ℂ :=
  fun p q =>
    ((Real.sqrt (irrepDim q.1.val : ℝ) /
      (Real.sqrt (k + 1 : ℕ) * Real.sqrt (irrepDim alpha : ℝ)) : ℝ) : ℂ) *
    R.upper q.1.val (cosetRep p.1) (R.coord q.1.val ⟨⟨alpha,q.1.property⟩,p.2⟩) q.2

/-- PDF p.13, Eq.(56): full block diagonal upper action, without height truncation. -/
def prirDirectSumAction {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k)
    (sigma : Equiv.Perm (Fin (k + 1))) : Matrix (ZColumn alpha) (ZColumn alpha) ℂ :=
  fun p q => if h : p.1 = q.1 then
    R.upper p.1.val sigma p.2 (Fin.cast (congrArg (fun nu : UpperShapes alpha => irrepDim nu.val) h.symm) q.2)
    else 0

/-- PDF p.14, Eq.(59): the explicitly constructed column vectors. -/
def columnT {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) (q : ZColumn alpha) :
    EuclideanSpace ℂ (Fin (k + 1) × Fin (irrepDim alpha)) :=
  WithLp.toLp 2 (fun p => explicitZR R alpha p q)

/-- PDF p.5, Definition 7: dI on diagonal coset blocks; ordinary transposition
blocks off diagonal. The conjugated permutation fixes the last letter. -/
def gramQ {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) (d : ℕ) :
    Matrix (Fin (k + 1) × Fin (irrepDim alpha))
      (Fin (k + 1) × Fin (irrepDim alpha)) ℂ :=
  fun p q => if p.1 = q.1 then (d : ℂ) * (if p.2 = q.2 then 1 else 0) else
    R.lower alpha (lowerPerm (cosetRep p.1 * Equiv.swap p.1 q.1 * cosetRep q.1)) p.2 q.2

/-- PDF pp.6–7, Eqs.(9)–(10): d plus the signed content of the added cell.
The sum has one term for a genuine one-box branch; diagonal additions have content zero. -/
def contentEigenvalue (d : ℕ) (alpha nu : YoungDiagram) : ℝ :=
  (d : ℝ) + ∑ c ∈ nu.cells \ alpha.cells, ((c.2 : ℝ) - (c.1 : ℝ))

/-- PDF p.14, Eq.(60): a branch eigenvalue on each internal coordinate. -/
def contentDiagonal {k : ℕ} (alpha : Shape k) (d : ℕ) :
    Matrix (ZColumn alpha) (ZColumn alpha) ℂ :=
  Matrix.diagonal fun q => (contentEigenvalue d alpha.val q.1.val.val : ℂ)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)
/- PDF p.3: tensor index type used by imported tensorPermutation. -/

/-- PDF pp.3–4: partial transpose on the last factor in the fixed tensor basis.
N counts preceding factors; the matrix acts on N+1 factors. -/
def lastPartialTranspose (d N : ℕ) (X : Matrix (Word d (N + 1)) (Word d (N + 1)) ℂ) :
    Matrix (Word d (N + 1)) (Word d (N + 1)) ℂ :=
  fun x y => X (Function.update x (Fin.last N) (y (Fin.last N)))
    (Function.update y (Fin.last N) (x (Fin.last N)))

/-- PDF p.21, Eq.(100): unnormalized partially transposed swap T_a. -/
def transposedSwap (d N : ℕ) (a : Fin N) : Matrix (Word d (N + 1)) (Word d (N + 1)) ℂ :=
  lastPartialTranspose d N
    (QAlgorithms.Schur.tensorPermutation d (N + 1) (Equiv.swap a.castSucc (Fin.last N)))

/-- PDF p.21: rho is the concrete sum of N=n-1 unnormalized generators. -/
def pbtOperator (d N : ℕ) : Matrix (Word d (N + 1)) (Word d (N + 1)) ℂ :=
  ∑ a : Fin N, transposedSwap d N a

/-- PDF p.21, Eq.(100): normalized individual signal; resource pairs are normalized. -/
def normalizedSignal (d N : ℕ) (a : Fin N) : Matrix (Word d (N + 1)) (Word d (N + 1)) ℂ :=
  ((d : ℂ) ^ N)⁻¹ • transposedSwap d N a

/-- PDF p.21: rho-tilde is the sum of signals, not a trace-one state for N>1. -/
def normalizedPBTOperator (d N : ℕ) : Matrix (Word d (N + 1)) (Word d (N + 1)) ℂ :=
  ∑ a : Fin N, normalizedSignal d N a

/-- PDF p.21, Eq.(99), equivalently p.24, Eq.(121): square-root-measurement
entanglement fidelity, using the actual normalized signals and their sum.
The support inverse is imported Mathlib cfc with x mapped to (sqrt x) inverse,
which is zero at zero. Completing the measurement on the common signal kernel adds zero to this trace.
For d=0 this total helper returns zero; every theorem assumes d>=2. -/
def pbtFidelity (d N : ℕ) : ℝ :=
  if hd : 0 < d then
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    let L := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (normalizedPBTOperator d N)
    (∑ a : Fin N, (normalizedSignal d N a * L * normalizedSignal d N a * L).trace.re) / (d : ℝ) ^ 2
  else 0

/-- PDF p.3: intertwiner space from the actual Specht irrep to the actual
permutation representation. Its dimension is the occurrence multiplicity;
no character-average theorem is used as a definition or assumption. -/
def tensorIntertwiners {h n : ℕ} (d : ℕ) (alpha : QAlgorithms.Schur.Partition h n) :
    Submodule ℂ (QAlgorithms.Schur.spechtSpace alpha →ₗ[ℂ] EuclideanSpace ℂ (Word d n)) where
  carrier := {f | ∀ sigma v, f (QAlgorithms.Schur.spechtRepresentation alpha sigma v) =
    Matrix.toEuclideanLin (QAlgorithms.Schur.tensorPermutation d n sigma) (f v)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg sigma v
    simp only [LinearMap.add_apply, map_add, hf sigma v, hg sigma v]
  smul_mem' := by
    intro c f hf sigma v
    simp only [LinearMap.smul_apply, map_smul, hf sigma v]

/-- PDF pp.3,15–16: actual tensor occurrence multiplicity. -/
def tensorMultiplicity {h n : ℕ} (d : ℕ) (alpha : QAlgorithms.Schur.Partition h n) : ℕ :=
  Module.finrank ℂ (tensorIntertwiners d alpha)

/-- PDF p.22: cycle count includes fixed points; S(0) has zero cycles. -/
def cycleCount {m : ℕ} (sigma : Equiv.Perm (Fin m)) : ℕ :=
  m - sigma.support.card + sigma.cycleType.card

/-- PDF p.22: geometric eigenvalue multiplicity, equal to the spectral
multiplicity for the Hermitian operator rho. -/
def eigenMultiplicity {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (lambda : ℝ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (A - (lambda : ℂ) • 1).mulVecLin)

/-- PDF p.26, Proposition 59: the printed domain lambda>=0 is corrected to
lambda>0, as required by its use on positive eigenvalues on p.28. The printed
second derivative is 3/4 times lambda^(-5/2), verified from the PDF image. -/
def inverseRoot (x : ℝ) : ℝ := (Real.sqrt x)⁻¹

/-- PDF pp.17–19: physical lower shapes, including the empty diagram. -/
abbrev PhysicalLower (d k : ℕ) := {alpha : Shape k // alpha.val.colLen 0 ≤ d}

/-- PDF pp.17–19: physical upper shapes, independent of any chosen predecessor. -/
abbrev PhysicalUpper (d k : ℕ) := {nu : Shape (k + 1) // nu.val.colLen 0 ≤ d}

/-- PDF pp.17–19: all retained one-box branches above a given alpha. -/
abbrev Retained {k : ℕ} (d : ℕ) (alpha : Shape k) :=
  {nu : PhysicalUpper d k // oneBoxBranch alpha nu.val}

/-- PDF p.17, Eq.(76), and p.18, Eq.(83): character projector embedded in the
specified tensor prefix. The group embeddings are fixed in every invocation. -/
def embeddedProjector {h k n : ℕ} (d : ℕ) (alpha : QAlgorithms.Schur.Partition h k)
    (embed : Equiv.Perm (Fin k) → Equiv.Perm (Fin n)) : Matrix (Word d n) (Word d n) ℂ :=
  ((irrepDim alpha : ℂ) / (k.factorial : ℂ)) •
    ∑ sigma : Equiv.Perm (Fin k), QAlgorithms.Schur.spechtCharacter alpha sigma⁻¹ •
      QAlgorithms.Schur.tensorPermutation d n (embed sigma)

/-- PDF p.17, Eq.(76): ordinary lower-group matrix units on the physical
n=k+2 factor space, with the source's inverse permutation and reversed j,i entry. -/
def subgroupMatrixUnit {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (alpha : Shape k)
    (i j : Fin (irrepDim alpha)) : Matrix (Word d (k + 2)) (Word d (k + 2)) ℂ :=
  ((irrepDim alpha : ℂ) / (k.factorial : ℂ)) •
    ∑ sigma : Equiv.Perm (Fin k), R.lower alpha sigma⁻¹ j i •
      QAlgorithms.Schur.tensorPermutation d (k + 2) (extendPerm (extendPerm sigma))

/-- PDF p.17, Eq.(75): actual physical matrix product. No multiplication law or
isotypic-basis equality is built into the definition. Physical shapes guarantee
positive tensor multiplicities; nonbranch choices are allowed for Remark 41. -/
def constructedE {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (alpha : Shape k)
    (mu nu : PhysicalUpper d k) (i j : Fin (irrepDim alpha)) :
    Matrix (Word d (k + 2)) (Word d (k + 2)) ℂ :=
  ((tensorMultiplicity d alpha : ℂ) /
    (Real.sqrt ((tensorMultiplicity d mu.val : ℝ) * (tensorMultiplicity d nu.val : ℝ)) : ℂ)) •
    (embeddedProjector d mu.val extendPerm * subgroupMatrixUnit R d alpha i j *
      transposedSwap d (k + 1) (Fin.last k) * embeddedProjector d nu.val extendPerm)

/-- PDF p.19, Eq.(96): sum of the constructed internal diagonal units.
This is distinct from either ordinary central projector P_mu or P_alpha. -/
def aggregatedP {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (alpha : Shape k)
    (mu nu : PhysicalUpper d k) : Matrix (Word d (k + 2)) (Word d (k + 2)) ℂ :=
  ∑ i : Fin (irrepDim alpha), constructedE R d alpha mu nu i i

/-- PDF pp.19–20: the linear combination of the specified physical units. -/
def unitSynthesis {I J : Type*} [Fintype I] (E : I → I → Matrix J J ℂ)
    (A : Matrix I I ℂ) : Matrix J J ℂ :=
  ∑ i : I, ∑ j : I, A i j • E i j

/-- PDF pp.19–20: precise algebra-isomorphism-onto-the-span assertion. The
explicit synthesis map is complex linear, multiplicative, injective, and has
exactly the physical span as image. Thus even a proper nonunital physical corner
is isomorphic to the complete source matrix algebra. -/
def IsMatrixAlgebraModel {I J : Type*} [Fintype I] [Fintype J]
    (E : I → I → Matrix J J ℂ) : Prop :=
  Function.Injective (unitSynthesis E) ∧
  (∀ A B, unitSynthesis E (A + B) = unitSynthesis E A + unitSynthesis E B) ∧
  (∀ c : ℂ, ∀ A, unitSynthesis E (c • A) = c • unitSynthesis E A) ∧
  (∀ A B, unitSynthesis E (A * B) = unitSynthesis E A * unitSynthesis E B) ∧
  Set.range (unitSynthesis E) =
    (Submodule.span ℂ (Set.range (fun ij : I × I => E ij.1 ij.2)) : Set (Matrix J J ℂ))

/-- PDF pp.8,25: actual copies of the second-kind module inside physical
tensor space. They intertwine the full ordinary subgroup and are annihilated by
every moving-last-letter swap generator. This independently defines occurrence
multiplicity, with no use of either (25) or (129). -/
def secondKindIntertwiners {N : ℕ} (d : ℕ) (nu : Shape N) :
    Submodule ℂ (QAlgorithms.Schur.spechtSpace nu →ₗ[ℂ] EuclideanSpace ℂ (Word d (N + 1))) where
  carrier := {f | (∀ sigma v, f (QAlgorithms.Schur.spechtRepresentation nu sigma v) =
    Matrix.toEuclideanLin (QAlgorithms.Schur.tensorPermutation d (N + 1) (extendPerm sigma)) (f v)) ∧
    (∀ a : Fin N, ∀ v, Matrix.toEuclideanLin (transposedSwap d N a) (f v) = 0)}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro sigma v
      simp only [LinearMap.add_apply, map_add, hf.1 sigma v, hg.1 sigma v]
    · intro a v
      simp only [LinearMap.add_apply, map_add, hf.2 a v, hg.2 a v, add_zero]
  smul_mem' := by
    intro c f hf
    constructor
    · intro sigma v
      simp only [LinearMap.smul_apply, map_smul, hf.1 sigma v]
    · intro a v
      simp only [LinearMap.smul_apply, map_smul, hf.2 a v, smul_zero]

/-- PDF p.25: M_nu is actual physical second-kind occurrence multiplicity. -/
def secondKindMultiplicity {N : ℕ} (d : ℕ) (nu : Shape N) : ℕ :=
  Module.finrank ℂ (secondKindIntertwiners d nu)

/-- PDF p.25: second-kind labels have strictly fewer than d rows. -/
abbrev SecondShapes (d N : ℕ) := {nu : Shape N // nu.val.colLen 0 < d}

/-- PDF pp.5,8,25: the independently computed dimension of the first-kind
carrier, namely the range of Q. No diagonal rank formula is an assumption. -/
def firstKindDimension {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) (d : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (gramQ R alpha d).mulVecLin)

/-- PDF pp.23–24, Eqs.(112),(118): actual full-tensor unnormalized trace,
using the support inverse, and retaining its complex value. -/
def naturalTrace (d N : ℕ) (a : Fin N) : ℂ :=
  if hd : 0 < d then
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    let L := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (pbtOperator d N)
    (L * transposedSwap d N a * L * transposedSwap d N a).trace
  else 0

/-- Sanity: the terminal coset representative is identity, including k=0. -/
example (k : ℕ) : cosetRep (Fin.last k) = 1 := by
  change Equiv.swap (Fin.last k) (Fin.last k) = Equiv.refl _
  exact Equiv.swap_self _

/-- Sanity: at k=0 the induced Gram matrix is [d], not the zero matrix. -/
example (R : CoherentPRIR 0) (alpha : Shape 0) (d : ℕ)
    (i : Fin (irrepDim alpha)) : gramQ R alpha d (0,i) (0,i) = (d : ℂ) := by
  simp [gramQ]

/-- Sanity: with one tensor factor partial transpose is the ordinary transpose. -/
example (d : ℕ) (X : Matrix (Word d 1) (Word d 1) ℂ) (x y : Word d 1) :
    lastPartialTranspose d 0 X x y = X y x := by
  change X (Function.update x (Fin.last 0) (y (Fin.last 0)))
    (Function.update y (Fin.last 0) (x (Fin.last 0))) = X y x
  congr 1 <;> funext i <;> have hi : i = Fin.last 0 := Subsingleton.elim _ _
  all_goals subst i; simp

/-- Sanity: with zero ports the concrete operator is an empty sum. -/
example (d : ℕ) : pbtOperator d 0 = 0 := by simp [pbtOperator]

/-- Sanity: fixed points contribute cycles; the identity on m letters has m cycles. -/
example (m : ℕ) : cycleCount (1 : Equiv.Perm (Fin m)) = m := by simp [cycleCount]

/-- Sanity: inverse square root is defined at zero as zero; zero is excluded from
Proposition 59's convexity domain. -/
example : inverseRoot 0 = 0 := by simp [inverseRoot]

/-- Sanity: the zero-letter subgroup embeds as the identity on one letter. -/
example : extendPerm (1 : Equiv.Perm (Fin 0)) = 1 := by
  apply Equiv.ext
  intro i
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- Sanity: dropping the final letter in the smallest group has no residual action. -/
example (sigma : Equiv.Perm (Fin 1)) : lowerPerm sigma = 1 := Subsingleton.elim _ _

/-- Sanity: the identity diagonal weighted prirBlock counts every induced branch. -/
example {k : ℕ} (R : CoherentPRIR k) (alpha : Shape k) (i : Fin (irrepDim alpha)) :
    weightedBlock R alpha 1 i i = ∑ nu : UpperShapes alpha, (irrepDim nu.val : ℂ) := by
  simp [weightedBlock, prirBlock, R.upper_one]

/-- Sanity: no cell addition contributes no signed content. -/
example (d : ℕ) (alpha : YoungDiagram) : contentEigenvalue d alpha alpha = (d : ℝ) := by
  simp [contentEigenvalue]

/-- Sanity: normalized signal sum is also empty at zero ports. -/
example (d : ℕ) : normalizedPBTOperator d 0 = 0 := by simp [normalizedPBTOperator]

/-- Sanity: the operational fidelity of the empty signal family is zero. -/
example (d : ℕ) : pbtFidelity d 0 = 0 := by
  by_cases hd : 0 < d <;> simp [pbtFidelity, hd]

/-- Sanity: the tensor intertwiner constraints admit the zero intertwiner. -/
example {h n : ℕ} (d : ℕ) (alpha : QAlgorithms.Schur.Partition h n) :
    (0 : QAlgorithms.Schur.spechtSpace alpha →ₗ[ℂ] EuclideanSpace ℂ (Word d n)) ∈
      tensorIntertwiners d alpha := (tensorIntertwiners d alpha).zero_mem

/-- Sanity: second-kind constraints likewise admit the zero physical intertwiner. -/
example {N : ℕ} (d : ℕ) (nu : Shape N) :
    (0 : QAlgorithms.Schur.spechtSpace nu →ₗ[ℂ] EuclideanSpace ℂ (Word d (N + 1))) ∈
      secondKindIntertwiners d nu := (secondKindIntertwiners d nu).zero_mem

/-- Sanity: synthesis for a one-dimensional matrix algebra has one coefficient. -/
example {J : Type*} (E : Fin 1 → Fin 1 → Matrix J J ℂ) (A : Matrix (Fin 1) (Fin 1) ℂ) :
    unitSynthesis E A = A 0 0 • E 0 0 := by simp [unitSynthesis]

end QAlgorithms.Papers.Independent.Extend50.P28


