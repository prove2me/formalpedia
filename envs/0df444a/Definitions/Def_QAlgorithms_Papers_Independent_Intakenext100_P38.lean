-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P38
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:29:38.595455+00:00
-- url     : https://prove2.me/theorems/aa4c189d-e02e-4b43-bc70-96d85ccedc88
-- title:
--   Definitions for On the universality of $S_n$-equivariant $k$-body gates
-- statement:
--   The objects the formalized statements of *On the universality of $S_n$-equivariant $k$-body gates* (arXiv:2303.00728) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `labelPauli`: Adapter to the frozen, standard-Y Pauli matrices (PDF p.10, A1).
--   - `axisCount`: Number of occurrences of an axis in a word (PDF pp.5,10).
--   - `symmetricPauli`: PDF pp.5,10, Definitions 3/5: sum of DISTINCT words with the specified counts. Overfull counts give the empty sum. This is neither an average nor a permutation sum.
--   - `symmetricUnitaryAlgebra`: PDF p.3, (10): real skew-Hermitian commutant. The displayed set is itself already a real subspace; taking its span supplies the ambient submodule interface.
--   - `specialSymmetricAlgebra`: PDF p.3, (11): total trace zero, as opposed to independently traceless blocks.
--   - `algebraCenter`: PDF p.4, (16): intrinsic center, without using the sought C-basis theorem. The commuting subset is a real subspace.
--   - `centerlessSymmetricAlgebra`: PDF p.3, (12): derived algebra of the compact skew commutant. For a compact reductive algebra, this intrinsic construction is the independently traceless multiplicity-block algebra. No coefficient constraint is built into this definition.
--   - `generatedSkewLie`: PDF p.2, (2): Mathlib real Lie closure for an arbitrary Hermitian generator set. The accepted Support50.P30.dynamicalLie instead fixes its three normalized generators, so it cannot represent arbitrary G or the higher-body families.
--   - `generators1`: PDF p.4, (21): the single collective-X generator.
--   - `generators1XY`: PDF p.4, (22): the collective X,Y generators.
--   - `generators2`: PDF pp.4–5, (23): the unnormalized Hermitian two-body generator set.
--   - `generatorsK`: PDF p.6, (36): collectives X,Y and every all-Z weight from 2 through k.
--   - `g2`
--   - `gK`
--   - `levelTriples`: Finite simplex at level m, including all boundary faces (PDF pp.5,10).
--   - `centralWeight`: PDF p.5, (28): real factorial coefficient, cast BEFORE division.
--   - `centralElement`: PDF pp.5,11, (28)/(B2): the Hermitian central candidate C_mu; C_0=I.
--   - `centralSpan`: PDF pp.6,20: the nonidentity central directions available through order 2r.
--   - `coefficientCombination`: PDF pp.5–6, (30)/(33): the full skew combination of real Pauli coefficients.
--   - `centralCoefficient`: PDF p.5, (31): the weighted central coefficient at level 2mu.
--   - `IsSemiUniversal`: PDF p.4, Definition 2: independent special-unitary control of every block.
--   - `IsEquivariantlyUniversal`: PDF p.4, Definition 2 (15): exact equivariant universality up to one global phase. The frozen QAlgorithms.IsUniversal instead concerns approximation by circuits over a gate set on all register sizes; it is a different predicate.
--   - `CentralProjector`: PDF pp.3–4: Hermitian central projections of the actual equivariant algebra. Minimal nonzero such projections are the canonical isotypic sectors.
--   - `IsCentralSector`: PDF pp.3–4: a single isotypic sector, specified without a chosen Schur frame.
--   - `IsSubspaceControllable`: PDF p.4, (13): every individual sector image contains its full special unitary algebra. E times the derived commutant is the repeated su(m_lambda) action on that sector. The existential M can depend on E and B, so this is individual control and does not impose simultaneous independent block control.
--   - `pauliDegreeSpace`: PDF p.6, Corollary 1: sums of Pauli terms of support at most k. A collective generator need not have a common set of k supported wires.
--   - `rotationCommutant`: PDF p.11, (B3)/(B5): skew commutant of all collective U(2) rotations.
--   - `permutationImage`: PDF pp.11–12: corrected meaning of S_n in (B3). Printed real span of iR(pi) is not skew for general permutations; use the skew part of the COMPLEX permutation group-algebra image, as required by the proof.
--   - `transpositionClass`: PDF p.12, Definition 6: involutions with exactly 2mu moved points are precisely products of mu disjoint transpositions. The remaining points are fixed.
--   - `transpositionSum`: PDF p.12, (B7): sum over distinct permutations in the transposition class.
--   - `transpositionPauliExpansion`: PDF p.12, (B12) corrected by p.13, (B17)–(B18): explicit four-index sum.
--   - `transpositionCentralExpansion`: PDF p.12, (B13): triangular expansion in the C-prefix.
--   - `axisRelabel`: PDF p.15, Lemma 4: coefficient permutation on the FULL Pauli-word basis, fixing I. This complex-linear map is not asserted to be a unitary conjugation.
--   - `appendixPauli`: PDF p.21, Note G changes BOTH Y to -Y and P to iP.
--   - `correctionA`: PDF p.22, (G4): the computed A, not an arbitrary input.
--   - `correctionB`: PDF p.22, (G5): the computed B.
--   - `correctionC`: PDF p.22, (G6): the computed C. Scalars use real subtraction.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, https://arxiv.org/abs/2303.00728v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

/-!
Statements from Kazi, Larocca and Cerezo, arXiv:2303.00728v2.
All spans and Lie closures are over the reals unless explicitly marked complex.
Paper-local definitions implement this paper only; matching accepted interfaces are imported. Compilation is pending batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- Adapter to the frozen, standard-Y Pauli matrices (PDF p.10, A1). -/
def labelPauli : (Option (Fin 3)) → Stabilizer.Pauli
  | none => .I
  | some j => if j = 0 then .X else if j = 1 then .Y else .Z

/-- Number of occurrences of an axis in a word (PDF pp.5,10). -/
def axisCount {n : ℕ} (w : Fin n → (Option (Fin 3))) (a : Fin 3) : ℕ :=
  (Finset.univ.filter fun j => w j = some a).card

/-- PDF pp.5,10, Definitions 3/5: sum of DISTINCT words with the specified counts.
Overfull counts give the empty sum. This is neither an average nor a permutation sum. -/
def symmetricPauli (n x y z : ℕ) : QnnOperator n :=
  ∑ w ∈ (Finset.univ : Finset (Fin n → (Option (Fin 3)))).filter
    (fun w => axisCount w 0 = x ∧ axisCount w 1 = y ∧ axisCount w 2 = z),
    pauliOps (fun j => labelPauli (w j))

/-- PDF p.3, (10): real skew-Hermitian commutant. The displayed set is itself
already a real subspace; taking its span supplies the ambient submodule interface. -/
def symmetricUnitaryAlgebra (n : ℕ) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {A | A.conjTranspose = -A ∧ PermutationEquivariant A}

/-- PDF p.3, (11): total trace zero, as opposed to independently traceless blocks. -/
def specialSymmetricAlgebra (n : ℕ) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {A | A ∈ symmetricUnitaryAlgebra n ∧ Matrix.trace A = 0}

/-- PDF p.4, (16): intrinsic center, without using the sought C-basis theorem.
The commuting subset is a real subspace. -/
def algebraCenter {n : ℕ} (g : Submodule ℝ (QnnOperator n)) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {A | A ∈ g ∧ ∀ B ∈ g, A * B = B * A}

/-- PDF p.3, (12): derived algebra of the compact skew commutant. For a compact
reductive algebra, this intrinsic construction is the independently traceless
multiplicity-block algebra. No coefficient constraint is built into this definition. -/
def centerlessSymmetricAlgebra (n : ℕ) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {M | ∃ A ∈ symmetricUnitaryAlgebra n,
    ∃ B ∈ symmetricUnitaryAlgebra n, M = A * B - B * A}

/-- PDF p.2, (2): Mathlib real Lie closure for an arbitrary Hermitian generator set.
The accepted Support50.P30.dynamicalLie instead fixes its three normalized
generators, so it cannot represent arbitrary G or the higher-body families. -/
def generatedSkewLie {n : ℕ} (G : Set (QnnOperator n)) : LieSubalgebra ℝ (QnnOperator n) :=
  LieSubalgebra.lieSpan ℝ (QnnOperator n) ((fun H => Complex.I • H) '' G)

/-- PDF p.4, (21): the single collective-X generator. -/
def generators1 (n : ℕ) : Set (QnnOperator n) := {symmetricPauli n 1 0 0}

/-- PDF p.4, (22): the collective X,Y generators. -/
def generators1XY (n : ℕ) : Set (QnnOperator n) :=
  {symmetricPauli n 1 0 0, symmetricPauli n 0 1 0}

/-- PDF pp.4–5, (23): the unnormalized Hermitian two-body generator set. -/
def generators2 (n : ℕ) : Set (QnnOperator n) :=
  {symmetricPauli n 1 0 0, symmetricPauli n 0 1 0, symmetricPauli n 0 0 2}

/-- PDF p.6, (36): collectives X,Y and every all-Z weight from 2 through k. -/
def generatorsK (n k : ℕ) : Set (QnnOperator n) :=
  {symmetricPauli n 1 0 0, symmetricPauli n 0 1 0} ∪
    {H | ∃ j : ℕ, 2 ≤ j ∧ j ≤ k ∧ H = symmetricPauli n 0 0 j}

abbrev g2 (n : ℕ) := generatedSkewLie (generators2 n)

abbrev gK (n k : ℕ) := generatedSkewLie (generatorsK n k)

/-- Finite simplex at level m, including all boundary faces (PDF pp.5,10). -/
def levelTriples (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (m + 1)) ×ˢ ((Finset.range (m + 1)) ×ˢ
    (Finset.range (m + 1)))).filter fun t => t.1 + t.2.1 + t.2.2 = m

/-- PDF p.5, (28): real factorial coefficient, cast BEFORE division. -/
def centralWeight (a b c : ℕ) : ℝ :=
  ((2 * a).factorial : ℝ) * ((2 * b).factorial : ℝ) * ((2 * c).factorial : ℝ) /
    ((a.factorial : ℝ) * (b.factorial : ℝ) * (c.factorial : ℝ))

/-- PDF pp.5,11, (28)/(B2): the Hermitian central candidate C_mu; C_0=I. -/
def centralElement (n mu : ℕ) : QnnOperator n :=
  ∑ t ∈ levelTriples mu, centralWeight t.1 t.2.1 t.2.2 •
    symmetricPauli n (2 * t.1) (2 * t.2.1) (2 * t.2.2)

/-- PDF pp.6,20: the nonidentity central directions available through order 2r. -/
def centralSpan (n r : ℕ) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {A | ∃ mu : ℕ, 1 ≤ mu ∧ mu ≤ r ∧
    A = Complex.I • centralElement n mu}

/-- PDF pp.5–6, (30)/(33): the full skew combination of real Pauli coefficients. -/
def coefficientCombination (n : ℕ) (c : ℕ → ℕ → ℕ → ℝ) : QnnOperator n :=
  Complex.I • (∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1),
    ∑ z ∈ Finset.range (n + 1),
      if x + y + z ≤ n then c x y z • symmetricPauli n x y z else 0)

/-- PDF p.5, (31): the weighted central coefficient at level 2mu. -/
def centralCoefficient (c : ℕ → ℕ → ℕ → ℝ) (mu : ℕ) : ℝ :=
  ∑ t ∈ levelTriples mu, c (2 * t.1) (2 * t.2.1) (2 * t.2.2) /
    ((t.1.factorial : ℝ) * (t.2.1.factorial : ℝ) * (t.2.2.factorial : ℝ))

/-- PDF p.4, Definition 2: independent special-unitary control of every block. -/
def IsSemiUniversal {n : ℕ} (g : Submodule ℝ (QnnOperator n)) : Prop :=
  centerlessSymmetricAlgebra n ≤ g ∧ g ≤ symmetricUnitaryAlgebra n

/-- PDF p.4, Definition 2 (15): exact equivariant universality up to one global phase.
The frozen QAlgorithms.IsUniversal instead concerns approximation by circuits
over a gate set on all register sizes; it is a different predicate. -/
def IsEquivariantlyUniversal {n : ℕ} (g : Submodule ℝ (QnnOperator n)) : Prop :=
  specialSymmetricAlgebra n ≤ g ∧ g ≤ symmetricUnitaryAlgebra n

/-- PDF pp.3–4: Hermitian central projections of the actual equivariant algebra.
Minimal nonzero such projections are the canonical isotypic sectors. -/
def CentralProjector (n : ℕ) (E : QnnOperator n) : Prop :=
  E.IsHermitian ∧ E * E = E ∧ PermutationEquivariant E ∧
    ∀ A ∈ symmetricUnitaryAlgebra n, E * A = A * E

/-- PDF pp.3–4: a single isotypic sector, specified without a chosen Schur frame. -/
def IsCentralSector (n : ℕ) (E : QnnOperator n) : Prop :=
  E ≠ 0 ∧ CentralProjector n E ∧
    ∀ F : QnnOperator n, CentralProjector n F → F * E = F → F = 0 ∨ F = E

/-- PDF p.4, (13): every individual sector image contains its full special
unitary algebra. E times the derived commutant is the repeated su(m_lambda)
action on that sector. The existential M can depend on E and B, so this is
individual control and does not impose simultaneous independent block control. -/
def IsSubspaceControllable {n : ℕ} (g : Submodule ℝ (QnnOperator n)) : Prop :=
  g ≤ symmetricUnitaryAlgebra n ∧
    ∀ E : QnnOperator n, IsCentralSector n E →
      ∀ B ∈ centerlessSymmetricAlgebra n, ∃ M ∈ g, E * M = E * B

/-- PDF p.6, Corollary 1: sums of Pauli terms of support at most k.
A collective generator need not have a common set of k supported wires. -/
def pauliDegreeSpace (n k : ℕ) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {A | ∃ w : Fin n → (Option (Fin 3)),
    (Finset.univ.filter fun j => w j ≠ none).card ≤ k ∧ A = pauliOps (fun j => labelPauli (w j))}

/-- PDF p.11, (B3)/(B5): skew commutant of all collective U(2) rotations. -/
def rotationCommutant (n : ℕ) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {A | A.conjTranspose = -A ∧
    ∀ U : Matrix.unitaryGroup Bool ℂ, A * piKron n (U : Matrix Bool Bool ℂ) = piKron n (U : Matrix Bool Bool ℂ) * A}

/-- PDF pp.11–12: corrected meaning of S_n in (B3).
Printed real span of iR(pi) is not skew for general permutations; use the skew
part of the COMPLEX permutation group-algebra image, as required by the proof. -/
def permutationImage (n : ℕ) : Submodule ℝ (QnnOperator n) :=
  Submodule.span ℝ {A | A.conjTranspose = -A ∧
    A ∈ Submodule.span ℂ (Set.range (qubitPermutationMatrix n))}

/-- PDF p.12, Definition 6: involutions with exactly 2mu moved points are
precisely products of mu disjoint transpositions. The remaining points are fixed. -/
def transpositionClass (n mu : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun pi => pi * pi = 1 ∧
    (Finset.univ.filter fun j => pi j ≠ j).card = 2 * mu

/-- PDF p.12, (B7): sum over distinct permutations in the transposition class. -/
def transpositionSum (n mu : ℕ) : QnnOperator n :=
  ∑ pi ∈ transpositionClass n mu, qubitPermutationMatrix n pi

/-- PDF p.12, (B12) corrected by p.13, (B17)–(B18): explicit four-index sum. -/
def transpositionPauliExpansion (n mu : ℕ) : QnnOperator n :=
  (((4 : ℝ) ^ mu)⁻¹ / (n - 2 * mu).factorial) •
    (∑ a ∈ Finset.range (mu + 1), ∑ b ∈ Finset.range (mu + 1),
      ∑ c ∈ Finset.range (mu + 1), ∑ f ∈ Finset.range (mu + 1),
        if a + b + c + f = mu then
          (centralWeight a b c * ((n - 2 * (mu - f)).factorial : ℝ) /
            (f.factorial : ℝ)) • symmetricPauli n (2 * a) (2 * b) (2 * c)
        else 0)

/-- PDF p.12, (B13): triangular expansion in the C-prefix. -/
def transpositionCentralExpansion (n mu : ℕ) : QnnOperator n :=
  (((4 : ℝ) ^ mu)⁻¹ / (n - 2 * mu).factorial) •
    ∑ j ∈ Finset.range (mu + 1),
      (((n - 2 * j).factorial : ℝ) / ((mu - j).factorial : ℝ)) • centralElement n j

/-- PDF p.15, Lemma 4: coefficient permutation on the FULL Pauli-word basis,
fixing I. This complex-linear map is not asserted to be a unitary conjugation. -/
def axisRelabel {n : ℕ} (sigma : Equiv.Perm (Fin 3)) (A : QnnOperator n) : QnnOperator n :=
  ∑ w : Fin n → (Option (Fin 3)),
    (Matrix.trace (pauliOps (fun j => labelPauli (w j)) * A) / (2 : ℂ) ^ n) •
      pauliOps (fun j => labelPauli (Option.map sigma (w j)))

/-- PDF p.21, Note G changes BOTH Y to -Y and P to iP. -/
def appendixPauli (n x y z : ℕ) : QnnOperator n :=
  Complex.I • (((-1 : ℝ) ^ y) • symmetricPauli n x y z)

/-- PDF p.22, (G4): the computed A, not an arbitrary input. -/
def correctionA (n k : ℕ) : QnnOperator n :=
  (-4 : ℝ) • appendixPauli n (k - 2) 2 0 +
    (2 * (k : ℝ)) • appendixPauli n k 0 0

/-- PDF p.22, (G5): the computed B. -/
def correctionB (n k : ℕ) : QnnOperator n :=
  (4 : ℝ) • appendixPauli n (k - 2) 0 2 -
    (2 * (k : ℝ)) • appendixPauli n k 0 0

/-- PDF p.22, (G6): the computed C. Scalars use real subtraction. -/
def correctionC (n k : ℕ) : QnnOperator n :=
  (-4 * ((k : ℝ) - 2)) • appendixPauli n (k - 2) 2 0 -
    (4 : ℝ) • appendixPauli n (k - 2) 0 2 +
    (2 * (k : ℝ) * ((k : ℝ) - 1)) • appendixPauli n k 0 0

/-- Structural sanity: a source generator enters the actual Lie closure. -/
example {n : ℕ} {G : Set (QnnOperator n)} {H : QnnOperator n} (h : H ∈ G) :
    Complex.I • H ∈ generatedSkewLie G :=
  LieSubalgebra.subset_lieSpan (Set.mem_image_of_mem _ h)

/-- Structural sanity: the zero-generator boundary has zero Lie closure. -/
example (n : ℕ) : generatedSkewLie (∅ : Set (QnnOperator n)) = ⊥ := by
  simp [generatedSkewLie, LieSubalgebra.span_empty]

/-- Scalar sanity: the three coefficients of C_1 are 2 (PDF p.5). -/
example : centralWeight 1 0 0 = 2 := by norm_num [centralWeight]

/-- Convention sanity: the local Y adapter is the frozen standard Pauli Y. -/
example : labelPauli (some 1) = Stabilizer.Pauli.Y := by
  norm_num [labelPauli]

/-- Convention sanity: Note G's odd-Y sign is negative. -/
example (n x z : ℕ) : appendixPauli n x 1 z =
    Complex.I • ((-1 : ℝ) • symmetricPauli n x 1 z) := by
  simp [appendixPauli]

/-- Sector sanity: the zero projection is explicitly excluded. -/
example (n : ℕ) : ¬ IsCentralSector n 0 := by
  intro h
  exact h.1 rfl

/-- Empty-register sanity: no word contains a nonidentity axis. -/
example (w : Fin 0 → (Option (Fin 3))) (a : Fin 3) : axisCount w a = 0 := by
  simp [axisCount]

/-- Simplex sanity: the zero level consists of exactly its origin. -/
example : levelTriples 0 = {(0, 0, 0)} := by
  norm_num [levelTriples]

/-- Central sanity: the zero coefficient constraint is exactly total trace zero. -/
example (c : ℕ → ℕ → ℕ → ℝ) : centralCoefficient c 0 = c 0 0 0 := by
  unfold centralCoefficient
  have hzero : levelTriples 0 = {(0, 0, 0)} := by
    norm_num [levelTriples]
  rw [hzero]
  norm_num

/-- Central normalization sanity: C_0 is the identity Pauli sum. -/
example (n : ℕ) : centralElement n 0 = symmetricPauli n 0 0 0 := by
  unfold centralElement
  have hzero : levelTriples 0 = {(0, 0, 0)} := by
    norm_num [levelTriples]
  rw [hzero]
  norm_num [centralWeight]

/-- Generator sanity: the original Hermitian ZZ sum is present without scaling. -/
example (n : ℕ) : symmetricPauli n 0 0 2 ∈ generators2 n := by
  simp [generators2]

/-- Tensor-power boundary sanity: U to the zeroth tensor power is scalar one. -/
example (U : Matrix.unitaryGroup Bool ℂ) (a b : Qubits 0) :
    piKron 0 (U : Matrix Bool Bool ℂ) a b = 1 := by
  simp [piKron]

end QAlgorithms.Papers.Independent.Intakenext100.P38


