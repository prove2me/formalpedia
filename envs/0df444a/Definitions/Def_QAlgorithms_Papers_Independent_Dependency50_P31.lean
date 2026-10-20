-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31
-- name    : QAlgorithms_Papers_Independent_Dependency50_P31
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T14:32:10.292411+00:00
-- url     : https://prove2.me/theorems/1ccbe370-279b-497d-911f-fd82800835c1
-- title:
--   Definitions for Lower bound on entanglement in subspaces defined by Young diagrams
-- statement:
--   The objects the formalized statements of *Lower bound on entanglement in subspaces defined by Young diagrams* (arXiv:1805.00364) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `H`: The Hilbert tensor product with its computational orthonormal basis (p.5).
--   - `Filling`: A filling records the zero-based position of each label; label i means i+1 (p.7).
--   - `IsTableau`: Exactly the standard tableaux of a specified diagram, without a dimension cutoff (p.7).
--   - `Standard`: A standard tableau of some ordinary Young diagram (p.7).
--   - `tableauPrefix`: The first k labels, retaining their actual cell positions (pp.10,12).
--   - `suffix`: The last n-k labels, with one common translation of the diagram (pp.11-12). The compatibility predicate below rules out truncated subtraction on valid uses.
--   - `IsSuffix`: A suffix must be an ordinary standard diagram after a common translation, never after independent row shifts (pp.11-12).
--   - `prefixCells`: First k occupied cells, used to compute the prefix Young element (pp.8-9).
--   - `cellHook`: Hook length from occupied cells: the cell, its right arm, and its lower leg (p.5).
--   - `rowGroup`: Row-preserving permutations of a prefix, fixing every later particle (p.8).
--   - `columnGroup`: Column-preserving permutations of a prefix, fixing every later particle (p.8).
--   - `youngPrefix`: Equation (26), with factorials cancelled against the normalized row/column averages. R is an actual specified permutation action, not an unknown embedding (p.8).
--   - `projectionRec`: Hermitian Young recursion (27), computed in the ambient tensor space; the prefix operators already include identities on the remaining particles (p.9).
--   - `tableauProjector`: The paper's P_t, not the generally non-Hermitian Y_t (p.9).
--   - `tableauSpace`: Physical image of the recursive Hermitian Young projector (pp.9-10).
--   - `isotypicSpace`: The entire isotypic component, using the frozen central projector (pp.2,5).
--   - `leftWord`: The physical prefix of a tensor word (p.12).
--   - `rightWord`: The physical suffix of a tensor word, preserving particle order (p.12).
--   - `joinAt`: Physical tensor product across the k | n-k cut (p.7, equation (17)).
--   - `liftLeft`: P on the first k physical particles, identity on the others (p.12).
--   - `liftRight`: P on the last n-k physical particles, identity on the others (p.12).
--   - `tensorSubspace`: The embedded tensor product of two physical subspaces (p.12, equation (36)).
--   - `PhysicalSchmidtDecomposition`: A Schmidt decomposition, including orthonormal vectors, ordered nonnegative amplitudes, and reconstruction. Zero coefficients are allowed (pp.5,7). This differs from Information100.P03.SchmidtData: the present object records amplitudes and reconstructs a specified, possibly unnormalized physical vector.
--   - `appendLast`: Append the final physical particle. The n=0 default is unused in all results (p.5).
--   - `lastMarginal`: The actual last-particle partial trace, not a representation-factor trace (pp.2,5).
--   - `largestSchmidtSq`: Largest squared Schmidt amplitude: the operator norm of the positive last marginal (pp.5,12). This is homogeneous and does not silently normalize its argument.
--   - `entropyNats`: Von Neumann entropy in natural units; the accepted entropy is in bits (pp.3,6).
--   - `subspaceOptimum`: The unit-sphere supremum in a specified physical subspace (pp.5,14). Uses below have nonempty unit spheres and values in [0,1].
--   - `Removable`: Removable corner, in zero-based cell coordinates (p.5).
--   - `cornerBound`: The exact individual product in (13), using hooks of the original diagram (p.5).
--   - `cornerEntropy`: The natural-log reciprocal hook product of (16) (p.6).
--   - `lastBox`: Position of N, using a positive-size proof only to form its label (pp.15-18).
--   - `ColumnBefore`: Column order compares columns first, then rows (p.9).
--   - `ColumnOrdered`: Fully column-ordered filling (pp.9,17).
--   - `ColumnOrderedExceptLast`: Column order on all labels except N (pp.15-18).
--   - `slaterBlock`: A normalized Slater block (21), starting at physical slot offset. At invalid slots the coefficient is zero; all theorem uses have enough slots (pp.7,17-18).
--   - `columnHeights`: Column heights in left-to-right order (pp.4,17).
--   - `columnProduct`: Product of normalized column Slaters; no renormalization of the A block (pp.17-18). An empty list gives the scalar unit when n=0.
--   - `leftSize`: Number of particles strictly to the left of column l (pp.15,18).
--   - `optimizerSeed`: Unprojected B block in (62): the shortened corner column, later columns, and finally the one-particle u_{c_l}. Zero-height Slaters are scalar units (p.18).
--   - `optimizerNumerator`: The projected B numerator in (62), using P_{t_B} (p.18).
--   - `cornerOptimizerState`: Exactly state (62): normalized B factor and the product of normalized A Slaters (p.18). Nonzero denominator is concluded in Proposition 14, not assumed. This physical vector differs from Information100.P58.optimizer, which is a scalar distribution of erasure-channel sector weights.
--   - `orthogonalYoungVector`: The actual Young orthogonal line in the concrete regular Specht module, selected independently of the multiplicity vector. Unit vectors in that line differ only by phase, which cannot affect Schmidt spectra (pp.9,15). The fallback is unused for standard tableaux of nu, by the orthogonal-basis construction of Theorem 4.
--   - `MultiplicitySpace`: Concrete multiplicity space Hom_{S_N}(S^nu,H_N). It fixes the meaning of one common v across different tableaux; no arbitrary Schur-coordinate embedding or branch is assumed (p.15). The homogeneous Lemma 11 needs no norm on this space.
--   - `tableauState`: Evaluation v tensor |t> in physical tensor coordinates (p.15).
--   - `swapToLast`: Singling out particle k: swap it into the final physical position (p.6, Remark 4).
--   - `particleMarginal`: Actual k-particle marginal, obtained by the specified swap before tracing (p.6).
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, https://arxiv.org/abs/1805.00364v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- The Hilbert tensor product with its computational orthonormal basis (p.5). -/
abbrev H (d n : ℕ) := EuclideanSpace ℂ (Word n d)

/-- A filling records the zero-based position of each label; label i means i+1 (p.7). -/
abbrev Filling (n : ℕ) := Fin n → ℕ × ℕ

/-- Exactly the standard tableaux of a specified diagram, without a dimension cutoff (p.7). -/
def IsTableau {n : ℕ} (nu : YoungDiagram) (t : Filling n) : Prop :=
  Function.Injective t ∧ Finset.univ.image t = nu.cells ∧
    (∀ i j, (t i).1 = (t j).1 → (t i).2 < (t j).2 → i < j) ∧
    (∀ i j, (t i).2 = (t j).2 → (t i).1 < (t j).1 → i < j)

/-- A standard tableau of some ordinary Young diagram (p.7). -/
def Standard {n : ℕ} (t : Filling n) : Prop := ∃ nu, IsTableau nu t

/-- The first k labels, retaining their actual cell positions (pp.10,12). -/
def tableauPrefix {n : ℕ} (t : Filling n) (k : ℕ) (hk : k ≤ n) : Filling k :=
  fun i => t ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

/-- The last n-k labels, with one common translation of the diagram (pp.11-12).
The compatibility predicate below rules out truncated subtraction on valid uses. -/
def suffix {n : ℕ} (t : Filling n) (k : ℕ) (hk : k ≤ n)
    (shift : ℕ × ℕ) : Filling (n-k) :=
  fun i => let b := t ⟨k+i.val, by omega⟩; (b.1-shift.1, b.2-shift.2)

/-- A suffix must be an ordinary standard diagram after a common translation,
never after independent row shifts (pp.11-12). -/
def IsSuffix {n : ℕ} (t : Filling n) (k : ℕ) (hk : k ≤ n)
    (b : Filling (n-k)) : Prop :=
  Standard b ∧ ∃ shift : ℕ × ℕ, ∀ i : Fin (n-k),
    t ⟨k+i.val, by omega⟩ = ((b i).1+shift.1, (b i).2+shift.2)

/-- First k occupied cells, used to compute the prefix Young element (pp.8-9). -/
def prefixCells {n : ℕ} (t : Filling n) (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.univ.filter fun i : Fin n => i.val < k).image t

/-- Hook length from occupied cells: the cell, its right arm, and its lower leg (p.5). -/
def cellHook (cells : Finset (ℕ × ℕ)) (b : ℕ × ℕ) : ℕ :=
  1 + (cells.filter fun a => a.1 = b.1 ∧ b.2 < a.2).card +
    (cells.filter fun a => a.2 = b.2 ∧ b.1 < a.1).card

/-- Row-preserving permutations of a prefix, fixing every later particle (p.8). -/
def rowGroup {n : ℕ} (t : Filling n) (k : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun pi =>
    (∀ i : Fin n, k ≤ i.val → pi i = i) ∧ (∀ i : Fin n, (t (pi i)).1 = (t i).1)

/-- Column-preserving permutations of a prefix, fixing every later particle (p.8). -/
def columnGroup {n : ℕ} (t : Filling n) (k : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun pi =>
    (∀ i : Fin n, k ≤ i.val → pi i = i) ∧ (∀ i : Fin n, (t (pi i)).2 = (t i).2)

/-- Equation (26), with factorials cancelled against the normalized row/column
averages. R is an actual specified permutation action, not an unknown embedding (p.8). -/
def youngPrefix {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Equiv.Perm (Fin n) → Matrix ι ι ℂ) (t : Filling n) (k : ℕ) :
    Matrix ι ι ℂ :=
  ((∏ b ∈ prefixCells t k, (cellHook (prefixCells t k) b : ℂ))⁻¹) •
    ∑ a ∈ rowGroup t k, ∑ b ∈ columnGroup t k,
      ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ)) • R (a*b)

/-- Hermitian Young recursion (27), computed in the ambient tensor space;
the prefix operators already include identities on the remaining particles (p.9). -/
def projectionRec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℕ → Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | k+1 => if k+1 ≤ 2 then Y (k+1)
      else projectionRec Y k * Y (k+1) * projectionRec Y k

/-- The paper's P_t, not the generally non-Hermitian Y_t (p.9). -/
def tableauProjector (d : ℕ) {n : ℕ} (t : Filling n) : Matrix (Word n d) (Word n d) ℂ :=
  projectionRec (youngPrefix (Schur.tensorPermutation d n) t) n

/-- Physical image of the recursive Hermitian Young projector (pp.9-10). -/
def tableauSpace (d : ℕ) {n : ℕ} (t : Filling n) : Submodule ℂ (H d n) :=
  LinearMap.range (Matrix.toEuclideanLin (tableauProjector d t))

/-- The entire isotypic component, using the frozen central projector (pp.2,5). -/
def isotypicSpace {d n : ℕ} (nu : Schur.Partition d n) : Submodule ℂ (H d n) :=
  LinearMap.range (Matrix.toEuclideanLin (Schur.isotypicProjector nu))

/-- The physical prefix of a tensor word (p.12). -/
def leftWord {d n : ℕ} (k : ℕ) (hk : k ≤ n) (x : Word n d) : Word k d :=
  fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

/-- The physical suffix of a tensor word, preserving particle order (p.12). -/
def rightWord {d n : ℕ} (k : ℕ) (hk : k ≤ n) (x : Word n d) : Word (n-k) d :=
  fun i => x ⟨k+i.val, by omega⟩

/-- Physical tensor product across the k | n-k cut (p.7, equation (17)). -/
def joinAt {d n : ℕ} (k : ℕ) (hk : k ≤ n) (a : H d k) (b : H d (n-k)) : H d n :=
  WithLp.toLp 2 (fun x => a (leftWord k hk x) * b (rightWord k hk x))

/-- P on the first k physical particles, identity on the others (p.12). -/
def liftLeft {d n : ℕ} (k : ℕ) (hk : k ≤ n) (P : Matrix (Word k d) (Word k d) ℂ) :
    Matrix (Word n d) (Word n d) ℂ :=
  fun x y => if rightWord k hk x = rightWord k hk y
    then P (leftWord k hk x) (leftWord k hk y) else 0

/-- P on the last n-k physical particles, identity on the others (p.12). -/
def liftRight {d n : ℕ} (k : ℕ) (hk : k ≤ n)
    (P : Matrix (Word (n-k) d) (Word (n-k) d) ℂ) :
    Matrix (Word n d) (Word n d) ℂ :=
  fun x y => if leftWord k hk x = leftWord k hk y
    then P (rightWord k hk x) (rightWord k hk y) else 0

/-- The embedded tensor product of two physical subspaces (p.12, equation (36)). -/
def tensorSubspace {d n : ℕ} (k : ℕ) (hk : k ≤ n)
    (A : Submodule ℂ (H d k)) (B : Submodule ℂ (H d (n-k))) : Submodule ℂ (H d n) :=
  Submodule.span ℂ {x | ∃ a ∈ A, ∃ b ∈ B, x = joinAt k hk a b}

/-- A Schmidt decomposition, including orthonormal vectors, ordered nonnegative
amplitudes, and reconstruction. Zero coefficients are allowed (pp.5,7).
This differs from Information100.P03.SchmidtData: the present object records
amplitudes and reconstructs a specified, possibly unnormalized physical vector. -/
structure PhysicalSchmidtDecomposition {d n : ℕ} (psi : H d n) (k : ℕ) (hk : k ≤ n) where
  rank : ℕ
  coeff : Fin rank → ℝ
  left : Fin rank → H d k
  right : Fin rank → H d (n-k)
  nonneg : ∀ i, 0 ≤ coeff i
  ordered : Antitone coeff
  left_orthonormal : Orthonormal ℂ left
  right_orthonormal : Orthonormal ℂ right
  reconstruct : psi = ∑ i, (coeff i : ℂ) • joinAt k hk (left i) (right i)

/-- Append the final physical particle. The n=0 default is unused in all results (p.5). -/
def appendLast {d n : ℕ} (x : Word (n-1) d) (a : Fin d) : Word n d :=
  fun i => if h : i.val < n-1 then x ⟨i.val,h⟩ else a

/-- The actual last-particle partial trace, not a representation-factor trace (pp.2,5). -/
def lastMarginal {d n : ℕ} (psi : H d n) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => ∑ x : Word (n-1) d, psi (appendLast x a) * conj (psi (appendLast x b))

/-- Largest squared Schmidt amplitude: the operator norm of the positive last marginal
(pp.5,12). This is homogeneous and does not silently normalize its argument. -/
def largestSchmidtSq {d n : ℕ} (psi : H d n) : ℝ := specNorm (lastMarginal psi)

/-- Von Neumann entropy in natural units; the accepted entropy is in bits (pp.3,6). -/
def entropyNats {d n : ℕ} (psi : H d n) : ℝ := Real.log 2 * vnEntropy (lastMarginal psi)

/-- The unit-sphere supremum in a specified physical subspace (pp.5,14).
Uses below have nonempty unit spheres and values in [0,1]. -/
def subspaceOptimum {d n : ℕ} (U : Submodule ℂ (H d n)) : ℝ :=
  sSup {r : ℝ | ∃ psi ∈ U, ‖psi‖ = 1 ∧ r = largestSchmidtSq psi}

/-- Removable corner, in zero-based cell coordinates (p.5). -/
def Removable (nu : YoungDiagram) (b : ℕ × ℕ) : Prop :=
  b ∈ nu ∧ (b.1+1,b.2) ∉ nu ∧ (b.1,b.2+1) ∉ nu

/-- The exact individual product in (13), using hooks of the original diagram (p.5). -/
def cornerBound (nu : YoungDiagram) (b : ℕ × ℕ) : ℝ :=
  ∏ i ∈ Finset.range b.1, (1 - 1 / (cellHook nu.cells (i,b.2) : ℝ))

/-- The natural-log reciprocal hook product of (16) (p.6). -/
def cornerEntropy (nu : YoungDiagram) (b : ℕ × ℕ) : ℝ :=
  Real.log (∏ i ∈ Finset.range b.1,
    (cellHook nu.cells (i,b.2) : ℝ) / ((cellHook nu.cells (i,b.2) : ℝ)-1))

/-- Position of N, using a positive-size proof only to form its label (pp.15-18). -/
def lastBox {n : ℕ} (t : Filling n) (hn : 0 < n) : ℕ × ℕ :=
  t ⟨n-1, by omega⟩

/-- Column order compares columns first, then rows (p.9). -/
def ColumnBefore (a b : ℕ × ℕ) : Prop := a.2 < b.2 ∨ (a.2 = b.2 ∧ a.1 < b.1)

/-- Fully column-ordered filling (pp.9,17). -/
def ColumnOrdered {n : ℕ} (t : Filling n) : Prop :=
  ∀ i j, ColumnBefore (t i) (t j) → i < j

/-- Column order on all labels except N (pp.15-18). -/
def ColumnOrderedExceptLast {n : ℕ} (t : Filling n) : Prop :=
  ∀ i j : Fin n, i.val < n-1 → j.val < n-1 → ColumnBefore (t i) (t j) → i < j

/-- A normalized Slater block (21), starting at physical slot offset. At invalid
slots the coefficient is zero; all theorem uses have enough slots (pp.7,17-18). -/
def slaterBlock {d n : ℕ} (u : ℕ → EuclideanSpace ℂ (Fin d))
    (m offset : ℕ) (x : Word n d) : ℂ :=
  ((Real.sqrt (m.factorial : ℝ))⁻¹ : ℂ) *
    ∑ pi : Equiv.Perm (Fin m), ((((Equiv.Perm.sign pi : ℤˣ) : ℤ) : ℂ)) *
      ∏ i : Fin m, if h : offset+i.val < n
        then u (pi i).val (x ⟨offset+i.val,h⟩) else 0

/-- Column heights in left-to-right order (pp.4,17). -/
def columnHeights (nu : YoungDiagram) : List ℕ :=
  (List.range (nu.rowLen 0)).map nu.colLen

/-- Product of normalized column Slaters; no renormalization of the A block (pp.17-18).
An empty list gives the scalar unit when n=0. -/
def columnProduct {d : ℕ} (u : ℕ → EuclideanSpace ℂ (Fin d))
    (heights : List ℕ) (n : ℕ) : H d n :=
  WithLp.toLp 2 (fun x => ∏ j ∈ Finset.range heights.length,
    slaterBlock u (heights.getD j 0) (heights.take j).sum x)

/-- Number of particles strictly to the left of column l (pp.15,18). -/
def leftSize (nu : YoungDiagram) (l : ℕ) : ℕ := ((columnHeights nu).take l).sum

/-- Unprojected B block in (62): the shortened corner column, later columns,
and finally the one-particle u_{c_l}. Zero-height Slaters are scalar units (p.18). -/
def optimizerSeed {d n : ℕ} (nu : YoungDiagram) (l : ℕ)
    (u : ℕ → EuclideanSpace ℂ (Fin d)) : H d n :=
  let heights := (nu.colLen l-1) :: (columnHeights nu).drop (l+1)
  WithLp.toLp 2 (fun x => columnProduct u heights n x *
    if hn : 0 < n then u (nu.colLen l-1) (x ⟨n-1,by omega⟩) else 0)

/-- The projected B numerator in (62), using P_{t_B} (p.18). -/
def optimizerNumerator {d n : ℕ} (nu : YoungDiagram) (t : Filling n) (l : ℕ)
    (hk : leftSize nu l ≤ n) (u : ℕ → EuclideanSpace ℂ (Fin d)) : H d (n-leftSize nu l) :=
  act (tableauProjector d (suffix t (leftSize nu l) hk (0,l))) (optimizerSeed nu l u)

/-- Exactly state (62): normalized B factor and the product of normalized A Slaters (p.18).
Nonzero denominator is concluded in Proposition 14, not assumed.
This physical vector differs from Information100.P58.optimizer, which is a
scalar distribution of erasure-channel sector weights. -/
def cornerOptimizerState {d n : ℕ} (nu : YoungDiagram) (t : Filling n) (l : ℕ)
    (hk : leftSize nu l ≤ n) (u : ℕ → EuclideanSpace ℂ (Fin d)) : H d n :=
  let b := optimizerNumerator nu t l hk u
  joinAt (leftSize nu l) hk
    (columnProduct u ((columnHeights nu).take l) (leftSize nu l))
    (((‖b‖⁻¹ : ℝ) : ℂ) • b)

/-- The actual Young orthogonal line in the concrete regular Specht module,
selected independently of the multiplicity vector. Unit vectors in that line differ
only by phase, which cannot affect Schmidt spectra (pp.9,15). The fallback is unused
for standard tableaux of nu, by the orthogonal-basis construction of Theorem 4. -/
def orthogonalYoungVector {d n : ℕ} (nu : Schur.Partition d n) (t : Filling n) :
    Schur.spechtSpace nu :=
  if h : ∃ v : Schur.spechtSpace nu, ‖v‖ = 1 ∧
      act (projectionRec (youngPrefix (@Schur.leftRegular n) t) n) v.val = v.val
  then Classical.choose h else 0

/-- Concrete multiplicity space Hom_{S_N}(S^nu,H_N). It fixes the meaning of
one common v across different tableaux; no arbitrary Schur-coordinate embedding
or branch is assumed (p.15). The homogeneous Lemma 11 needs no norm on this space. -/
def MultiplicitySpace {d n : ℕ} (nu : Schur.Partition d n) :=
  {f : Schur.spechtSpace nu →ₗ[ℂ] H d n // ∀ pi v,
    f (Schur.spechtRepresentation nu pi v) = act (Schur.tensorPermutation d n pi) (f v)}

/-- Evaluation v tensor |t> in physical tensor coordinates (p.15). -/
def tableauState {d n : ℕ} {nu : Schur.Partition d n}
    (v : MultiplicitySpace nu) (t : Filling n) : H d n :=
  v.val (orthogonalYoungVector nu t)

/-- Singling out particle k: swap it into the final physical position (p.6, Remark 4). -/
def swapToLast {d n : ℕ} (hn : 0 < n) (k : Fin n) (psi : H d n) : H d n :=
  act (Schur.tensorPermutation d n (Equiv.swap k ⟨n-1,by omega⟩)) psi

/-- Actual k-particle marginal, obtained by the specified swap before tracing (p.6). -/
def particleMarginal {d n : ℕ} (hn : 0 < n) (k : Fin n) (psi : H d n) :
    Matrix (Fin d) (Fin d) ℂ := lastMarginal (swapToLast hn k psi)

/-- Sanity: the zero-particle recursion gives the scalar identity (p.9). -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ℕ → Matrix ι ι ℂ) :
    projectionRec Y 0 = 1 := by rfl

/-- Sanity: at two particles the recursion is the Young element itself (p.9). -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ℕ → Matrix ι ι ℂ) :
    projectionRec Y 2 = Y 2 := by simp [projectionRec]

/-- Sanity: a top-row corner has empty hook product, hence bound 1 (p.5). -/
example (nu : YoungDiagram) (j : ℕ) : cornerBound nu (0,j) = 1 := by
  simp [cornerBound]

/-- Sanity: its entropy contribution is ln(1)=0 (p.6). -/
example (nu : YoungDiagram) (j : ℕ) : cornerEntropy nu (0,j) = 0 := by
  simp [cornerEntropy]

/-- Sanity: the zero-column product is the scalar unit, including the vacuum A block (p.18). -/
example {d : ℕ} (u : ℕ → EuclideanSpace ℂ (Fin d)) (x : Word 0 d) :
    columnProduct u [] 0 x = 1 := by simp [columnProduct]

/-- Sanity: the zero-particle Slater is the scalar unit, as used in (62) (pp.7,18). -/
example {d n : ℕ} (u : ℕ → EuclideanSpace ℂ (Fin d)) (offset : ℕ) (x : Word n d) :
    slaterBlock u 0 offset x = 1 := by
  letI : Unique (Equiv.Perm (Fin 0)) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  simp [slaterBlock]

/-- Sanity: the zero vector has zero partial trace; it is never treated as a unit state (p.2). -/
example {d n : ℕ} : lastMarginal (0 : H d n) = 0 := by
  ext a b
  simp [lastMarginal]

/-- Sanity: the choice in an existing orthogonal line is normalized (pp.9,15). -/
example {d n : ℕ} (nu : Schur.Partition d n) (t : Filling n)
    (h : ∃ v : Schur.spechtSpace nu, ‖v‖ = 1 ∧
      act (projectionRec (youngPrefix (@Schur.leftRegular n) t) n) v.val = v.val) :
    ‖orthogonalYoungVector nu t‖ = 1 := by
  simpa only [orthogonalYoungVector, dif_pos h] using (Classical.choose_spec h).1

end QAlgorithms.Papers.Independent.Dependency50.P31


