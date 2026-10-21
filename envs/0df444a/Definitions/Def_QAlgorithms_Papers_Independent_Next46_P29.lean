-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29
-- name    : QAlgorithms_Papers_Independent_Next46_P29
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:13:11.269049+00:00
-- url     : https://prove2.me/theorems/b9537736-16d8-4c4e-9205-f23066f0a336
-- title:
--   Definitions for Quantum communication using a bounded-size quantum reference frame
-- statement:
--   The objects the formalized statements of *Quantum communication using a bounded-size quantum reference frame* (arXiv:0812.5040) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HasLieStructure`: PDF pp.3–4: a finite-dimensional real Lie structure on the group. The separate compactness and Hausdorff hypotheses below complete the source setting.
--   - `BasedUnitaryRep`: PDF pp.3–4: a continuous unitary representation in a specified orthonormal basis.
--   - `repMatrix`: The matrix of a based representation, PDF p.4.
--   - `asProjectiveRep`: PDF pp.3–4: the actual based unitary representation viewed through the accepted projective-representation interface, with every projective phase equal to one. Irreducibility below reuses the accepted invariant-subspace predicate.
--   - `CanonicalToken`: PDF p.5, Eqs.(13)–(17): the finite nonempty set of pairwise inequivalent irreps retained in the restricted token space. The two copies of `Fin (dim q)` are the paired carrier and chosen multiplicity bases; original unused multiplicities have already been discarded. No tight-frame identity or encoding formula is assumed.
--   - `TokenIndex`: PDF p.5, Eq.(15): carrier basis first, paired multiplicity basis second.
--   - `tokenDimension`: PDF p.5, Eq.(16): dimension of the entire restricted token space.
--   - `canonicalKet`: PDF p.5, Eq.(17). There is no additional factor `1 / sqrt (dim q)`.
--   - `tokenInclusion`: PDF p.5, Eq.(15): inclusion of a single based token summand.
--   - `tokenLeft`: PDF p.5, Eq.(13): the actual left action on the restricted token.
--   - `tokenRight`: PDF p.5, Eq.(20): the right action is constructed on the paired multiplicity basis by complex conjugation of the original irrep, not supplied as independent data.
--   - `tokenOrbit`: PDF p.4, Eq.(10): orbit of the fixed canonical token.
--   - `orbitKraus`: PDF p.8, Eq.(39): `K(g) = |g> tensor U_S(g)`, with token factor first.
--   - `canonicalEncoding`: PDF pp.4–5, Eqs.(9),(11),(17): canonical Haar-correlated encoding.
--   - `canonicalRecovery`: PDF p.8, Eqs.(38)–(39): fixed deterministic recovery by covariant token measurement followed by the conditional inverse message rotation.
--   - `overlapWeight`: PDF p.9, Eq.(40): overlap weight, including the normalization `D_R`.
--   - `effectiveChannel`: PDF p.9, Eq.(40): noisy message channel specified by the actual token overlap.
--   - `JointDecomposition`: PDF pp.6–7, Eqs.(22),(26): an exhaustive based isotypic decomposition of this actual token/message tensor representation. The inclusions are orthonormal, mutually orthogonal and exhaustive; equivalent copies are multiplicities. No encoding identity or reciprocal Clebsch–Gordan isometry is a field.
--   - `sectorBlock`: PDF p.8, Eq.(36): the relational block, obtained by projecting the actual joint operator into its based isotypic summand and tracing the carrier.
--   - `sectorRight`: PDF pp.6–7, Eqs.(25),(28),(31): right action induced on the actual multiplicity block. It is computed from the physical right action and based inclusions, with the carrier trace divided by the carrier dimension.
--   - `relationalIsometry`: PDF pp.6–8, Eqs.(30),(32),(35),(37): the reciprocal isometry constructed by contracting the actual coupled-basis coefficients with the paired canonical token. This fixes all phases from the input based decomposition, rather than assuming an unrelated isometry or the desired block encoding formula.
--   - `relationalEncoding`: PDF p.8, Eq.(37): relational encoding obtained directly from the untwirled physical token/message state in the actual coupled basis.
--   - `reciprocalProjector`: PDF pp.6–7, Eqs.(28),(33), Case B: projector onto precisely those conjugate token irreps retained in `q* tensor q_S`. Character projectors avoid choosing a second arbitrary Clebsch–Gordan basis. The character has no conjugate here because the retained irreps themselves are the conjugate token irreps.
--   - `relationalRecovery`: PDF p.9, Eq.(42): extraction from the actual relational subsystem.
--   - `relationalAccepted`: PDF p.10, Eq.(47): measure the actual joint irrep, accept exactly those whose reciprocal coupling contains no omitted token irrep, and extract the message.
--   - `relationalSuccess`: PDF p.10, Eq.(47): achieved good-sector weight; the sum may be empty.
--   - `phaseKet`: PDF p.11, Eq.(48): bounded phase token, including the vacuum cutoff `N = 0`.
--   - `numberRotation`: PDF p.11, Eq.(51): number representation with the same negative exponential on token and message; `d` is the number of number-basis states.
--   - `phaseOrbitKraus`: PDF pp.4,11: token/message orbit Kraus operator for the phase example.
--   - `phaseAverage`: PDF p.11: normalized U(1) Haar integral of a periodic function, using the interval `[0,2 pi]`; endpoints have measure zero.
--   - `phaseEncoding`: PDF p.11, Eqs.(48),(51): encoding from the actual common number rotation, not from a postulated partial-dephasing channel.
--   - `phaseRecovery`: PDF pp.8,11: the covariant token measurement and conditional inverse rotation.
--   - `numberProjector`: PDF p.11, Eq.(56): projection onto total occupation number `t`.
--   - `phaseBranch`: PDF p.11, Eq.(56): subnormalized joint state in a measured total-number sector.
--   - `numberDecoder`: PDF p.12, Eq.(58): coherent inverse on a number sector, zero outside it. At an endpoint its initial space is one-dimensional.
--   - `phaseDecodedBranch`: PDF p.12: subnormalized message recovered from the measured branch.
--   - `phaseAccepted`: PDF p.12, Eq.(59): accepted physical subchannel on arbitrary joint inputs. The accepted numbers are `1,...,N`, so for `N = 0` the sum is empty.
--   - `spinBasis`: PDF pp.12,15: normalized symmetric-tensor weight basis for spin `k/2`. Weight index `n` means magnetic weight `k/2 - n`. The denominator is nonzero because `n : Fin (k+1)`. This fixes the actual spin representation, including phases.
--   - `spinMatrix`: PDF pp.12,15: the actual spin-`k/2` matrix, obtained by restricting the `k`-fold tensor power of the fundamental qubit matrix to its symmetric subspace.
--   - `zRotation`: PDF p.15, Eq.(101): the fundamental z-rotation in the standard weight basis.
--   - `yRotation`: PDF p.15, Eq.(101): the fundamental y-rotation, including its off-diagonal signs.
--   - `eulerFundamental`: PDF p.15, Eqs.(99),(101): actual Euler-angle SU(2) matrix.
--   - `su2Average`: PDF p.15, normalized SU(2) Haar integration. The full Euler cover is `a in [0,2pi], b in [0,pi], c in [0,4pi]` with density `sin b/(16 pi^2)`. This is not the axis-angle half-cover of Eq.(69); normalization is valid also for half-integer representations. Endpoints are null sets.
--   - `directionKet`: PDF p.15, Eq.(94): highest-weight direction token, `j_R = k/2`.
--   - `directionKraus`: PDF p.15, Eq.(97): actual spin-coherent token orbit paired with the fundamental message rotation.
--   - `directionEncoding`: PDF p.15, Eq.(97): direction encoding by actual normalized SU(2) twirling.
--   - `directionRecovery`: PDF p.15, Eq.(98): direction POVM decoding, with `D_R = k+1`, not a sum of squared irrep dimensions.
--   - `spinZ`: PDF pp.13,15: angular momentum z-matrix in the standard spin weight basis.
--   - `spinRaise`: PDF pp.13,15: raising matrix in the standard spin weight basis.
--   - `spinCoupling`: PDF pp.13,15, Eqs.(74),(106): `J_R dot sigma` determines the actual spin-coupling spectral projectors, including the off-diagonal coupling phases.
--   - `spinPlus`: PDF p.15, Eq.(106): projector onto `J = (k+1)/2`, as a spectral polynomial of the actual total angular momentum. At `k=0` it is the full identity.
--   - `spinMinus`: PDF p.15, Eq.(106): projector onto `J = (k-1)/2`; it is zero when `k=0`.
--   - `directionPlusState`: PDF p.16, Eq.(113): state prepared after the plus outcome by adjoint recovery.
--   - `directionOptimal`: PDF p.16: optimal decoder for an equiprobable z-bit, using the same actual spin sectors and maximum-posterior repreparation.
--   - `zBitFidelity`: PDF p.16: average input/output fidelity for exactly the two equiprobable z-basis states, not entanglement fidelity or Haar-average pure-state fidelity.
--   - `CartesianIndex`: PDF p.12, Eq.(60): every integer spin `0,...,L`, with paired memory of its own dimension. Extra original multiplicity spaces are not included.
--   - `cartesianDimension`: PDF p.12, Eq.(61): restricted Cartesian-token dimension.
--   - `cartesianKet`: PDF p.12, Eq.(60): canonical token for the integer-spin cutoff.
--   - `cartesianOrbit`: PDF pp.12–13, Eqs.(60),(63): actual Cartesian orbit under symmetric-tensor spin matrices. Memory is unchanged; this formula avoids any arbitrary irrep data.
--   - `cartesianKraus`: PDF pp.12–13: actual canonical-token/message orbit Kraus operator.
--   - `cartesianEncoding`: PDF pp.12–13: Cartesian encoding with normalized SU(2) Haar law.
--   - `cartesianRecovery`: PDF pp.12–14: canonical adjoint recovery with the actual dimension factor.
--   - `cartesianSpinInclusion`: PDF p.13, Eqs.(73)–(75): inclusion of a token-spin carrier and message, with a fixed paired-memory index, into the full physical joint basis.
--   - `cartesianProjector`: PDF pp.13–14: actual total-spin sector `J=t+1/2`, built from the spectral spin-coupling projectors in each physical token summand.
--   - `cartesianAccepted`: PDF p.14, Eq.(93): accepted decoding after measuring total spin and rejecting the single top sector. At cutoff zero the accepted set is empty.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, https://arxiv.org/abs/0812.5040v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
Statements from Bartlett, Rudolph, Spekkens and Turner, arXiv:0812.5040v2.
Only this paper's local definitions are introduced here. The token register is
exactly the restricted register of Eq. (15); no unused ambient multiplicities occur.
Deferred nodes and source discrepancies are recorded in the unit's HARD.md.
Compilation is pending the batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)
open QAlgorithms.Papers.Independent.Information100.P63 (mixed)
open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)
open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.3–4: a finite-dimensional real Lie structure on the group.
The separate compactness and Hausdorff hypotheses below complete the source setting. -/
def HasLieStructure (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ n : ℕ, ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) G,
    letI := charts
    LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G

/-- PDF pp.3–4: a continuous unitary representation in a specified orthonormal basis. -/
structure BasedUnitaryRep (G : Type*) [Group G] [TopologicalSpace G] (d : ℕ) where
  hom : G →* Matrix.unitaryGroup (Fin d) ℂ
  continuous_matrix : Continuous (fun g => (hom g : Matrix (Fin d) (Fin d) ℂ))

/-- The matrix of a based representation, PDF p.4. -/
def repMatrix {G : Type*} [Group G] [TopologicalSpace G] {d : ℕ}
    (U : BasedUnitaryRep G d) (g : G) : Matrix (Fin d) (Fin d) ℂ :=
  U.hom g

/-- PDF pp.3–4: the actual based unitary representation viewed through the
accepted projective-representation interface, with every projective phase equal to one.
Irreducibility below reuses the accepted invariant-subspace predicate. -/
def asProjectiveRep {G : Type*} [Group G] [TopologicalSpace G] {d : ℕ}
    (U : BasedUnitaryRep G d) :
    QAlgorithms.Papers.Independent.Information100.P56.ProjectiveRep G (Fin d) where
  unitary := U.hom
  phase := fun _ _ => 1
  phase_norm := by intro g h; simp
  mul_phase := by
    intro g h
    change (U.hom (g * h) : Matrix (Fin d) (Fin d) ℂ) =
      (1 : ℂ) • ((U.hom g : Matrix (Fin d) (Fin d) ℂ) *
        (U.hom h : Matrix (Fin d) (Fin d) ℂ))
    simp

/-- PDF p.5, Eqs.(13)–(17): the finite nonempty set of pairwise inequivalent
irreps retained in the restricted token space. The two copies of `Fin (dim q)`
are the paired carrier and chosen multiplicity bases; original unused multiplicities
have already been discarded. No tight-frame identity or encoding formula is assumed. -/
structure CanonicalToken (G : Type*) [Group G] [TopologicalSpace G] where
  count : ℕ
  count_pos : 0 < count
  dim : Fin count → ℕ
  dim_pos : ∀ q, 0 < dim q
  rep : (q : Fin count) → BasedUnitaryRep G (dim q)
  irreducible : ∀ q, IsIrreducible (asProjectiveRep (rep q))
  inequivalent : ∀ q q', q ≠ q' →
    ∀ T : Matrix (Fin (dim q)) (Fin (dim q')) ℂ,
      (∀ g, repMatrix (rep q) g * T = T * repMatrix (rep q') g) → T = 0

/-- PDF p.5, Eq.(15): carrier basis first, paired multiplicity basis second. -/
abbrev TokenIndex {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) :=
  (q : Fin C.count) × (Fin (C.dim q) × Fin (C.dim q))

/-- PDF p.5, Eq.(16): dimension of the entire restricted token space. -/
def tokenDimension {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) : ℕ :=
  ∑ q, C.dim q ^ 2

/-- PDF p.5, Eq.(17). There is no additional factor `1 / sqrt (dim q)`. -/
def canonicalKet {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) :
    EuclideanSpace ℂ (TokenIndex C) :=
  WithLp.toLp 2 fun a => if a.2.1 = a.2.2 then
    (Real.sqrt ((C.dim a.1 : ℝ) / tokenDimension C) : ℂ) else 0

/-- PDF p.5, Eq.(15): inclusion of a single based token summand. -/
def tokenInclusion {G : Type*} [Group G] [TopologicalSpace G]
    (C : CanonicalToken G) (q : Fin C.count) :
    Matrix (TokenIndex C) (Fin (C.dim q) × Fin (C.dim q)) ℂ :=
  fun a b => if a = ⟨q, b⟩ then 1 else 0

/-- PDF p.5, Eq.(13): the actual left action on the restricted token. -/
def tokenLeft {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) (g : G) :
    Matrix (TokenIndex C) (TokenIndex C) ℂ :=
  ∑ q, tokenInclusion C q *
    ((repMatrix (C.rep q) g).kronecker (1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ)) *
    (tokenInclusion C q)ᴴ

/-- PDF p.5, Eq.(20): the right action is constructed on the paired multiplicity
basis by complex conjugation of the original irrep, not supplied as independent data. -/
def tokenRight {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) (h : G) :
    Matrix (TokenIndex C) (TokenIndex C) ℂ :=
  ∑ q, tokenInclusion C q *
    ((1 : Matrix (Fin (C.dim q)) (Fin (C.dim q)) ℂ).kronecker
      (fun a b => conj (repMatrix (C.rep q) h a b))) * (tokenInclusion C q)ᴴ

/-- PDF p.4, Eq.(10): orbit of the fixed canonical token. -/
def tokenOrbit {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G) (g : G) :
    EuclideanSpace ℂ (TokenIndex C) :=
  act (tokenLeft C g) (canonicalKet C)

/-- PDF p.8, Eq.(39): `K(g) = |g> tensor U_S(g)`, with token factor first. -/
def orbitKraus {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    (C : CanonicalToken G) (U : BasedUnitaryRep G s) (g : G) :
    Matrix (TokenIndex C × Fin s) (Fin s) ℂ :=
  fun a b => tokenOrbit C g a.1 * repMatrix U g a.2 b

/-- PDF pp.4–5, Eqs.(9),(11),(17): canonical Haar-correlated encoding. -/
def canonicalEncoding {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {s : ℕ}
    (mu : Measure G) (C : CanonicalToken G) (U : BasedUnitaryRep G s) :
    Superop (Fin s) (TokenIndex C × Fin s) :=
  fun X => ∫ g, orbitKraus C U g * X * (orbitKraus C U g)ᴴ ∂mu

/-- PDF p.8, Eqs.(38)–(39): fixed deterministic recovery by covariant token
measurement followed by the conditional inverse message rotation. -/
def canonicalRecovery {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {s : ℕ}
    (mu : Measure G) (C : CanonicalToken G) (U : BasedUnitaryRep G s) :
    Superop (TokenIndex C × Fin s) (Fin s) :=
  fun Y => (tokenDimension C : ℂ) •
    ∫ g, (orbitKraus C U g)ᴴ * Y * orbitKraus C U g ∂mu

/-- PDF p.9, Eq.(40): overlap weight, including the normalization `D_R`. -/
def overlapWeight {G : Type*} [Group G] [TopologicalSpace G]
    (C : CanonicalToken G) (g : G) : ℝ :=
  (tokenDimension C : ℝ) * Complex.normSq
    (∑ a, conj (canonicalKet C a) * tokenOrbit C g a)

/-- PDF p.9, Eq.(40): noisy message channel specified by the actual token overlap. -/
def effectiveChannel {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {s : ℕ}
    (mu : Measure G) (C : CanonicalToken G) (U : BasedUnitaryRep G s) :
    Superop (Fin s) (Fin s) :=
  fun X => ∫ g, (overlapWeight C g : ℂ) • conjSuperop (repMatrix U g) X ∂mu

/-- PDF pp.6–7, Eqs.(22),(26): an exhaustive based isotypic decomposition of
this actual token/message tensor representation. The inclusions are orthonormal,
mutually orthogonal and exhaustive; equivalent copies are multiplicities.
No encoding identity or reciprocal Clebsch–Gordan isometry is a field. -/
structure JointDecomposition {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    (C : CanonicalToken G) (U : BasedUnitaryRep G s) where
  count : ℕ
  count_pos : 0 < count
  dim : Fin count → ℕ
  mult : Fin count → ℕ
  dim_pos : ∀ q, 0 < dim q
  mult_pos : ∀ q, 0 < mult q
  rep : (q : Fin count) → BasedUnitaryRep G (dim q)
  irreducible : ∀ q, IsIrreducible (asProjectiveRep (rep q))
  inequivalent : ∀ q q', q ≠ q' →
    ∀ T : Matrix (Fin (dim q)) (Fin (dim q')) ℂ,
      (∀ g, repMatrix (rep q) g * T = T * repMatrix (rep q') g) → T = 0
  basis : (q : Fin count) →
    Matrix (TokenIndex C × Fin s) (Fin (dim q) × Fin (mult q)) ℂ
  orthonormal : ∀ q, (basis q)ᴴ * basis q = 1
  orthogonal : ∀ q q', q ≠ q' → (basis q)ᴴ * basis q' = 0
  exhaustive : ∑ q, basis q * (basis q)ᴴ = 1
  intertwines : ∀ g q,
    ((tokenLeft C g).kronecker (repMatrix U g)) * basis q =
      basis q * ((repMatrix (rep q) g).kronecker
        (1 : Matrix (Fin (mult q)) (Fin (mult q)) ℂ))

/-- PDF p.8, Eq.(36): the relational block, obtained by projecting the actual
joint operator into its based isotypic summand and tracing the carrier. -/
def sectorBlock {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (J : JointDecomposition C U) (q : Fin J.count)
    (Y : Matrix (TokenIndex C × Fin s) (TokenIndex C × Fin s) ℂ) :
    Matrix (Fin (J.mult q)) (Fin (J.mult q)) ℂ :=
  traceLeft ((J.basis q)ᴴ * Y * J.basis q)

/-- PDF pp.6–7, Eqs.(25),(28),(31): right action induced on the actual
multiplicity block. It is computed from the physical right action and based
inclusions, with the carrier trace divided by the carrier dimension. -/
def sectorRight {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (J : JointDecomposition C U) (q : Fin J.count) (h : G) :
    Matrix (Fin (J.mult q)) (Fin (J.mult q)) ℂ :=
  (J.dim q : ℂ)⁻¹ • traceLeft ((J.basis q)ᴴ *
    ((tokenRight C h).kronecker (1 : Matrix (Fin s) (Fin s) ℂ)) * J.basis q)

/-- PDF pp.6–8, Eqs.(30),(32),(35),(37): the reciprocal isometry constructed
by contracting the actual coupled-basis coefficients with the paired canonical
token. This fixes all phases from the input based decomposition, rather than
assuming an unrelated isometry or the desired block encoding formula. -/
def relationalIsometry {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (J : JointDecomposition C U) (q : Fin J.count) :
    Matrix (Fin (J.dim q) × Fin s) (Fin (J.mult q)) ℂ :=
  fun a m => (Real.sqrt ((tokenDimension C : ℝ) / J.dim q) : ℂ) *
    ∑ r, J.basis q (r, a.2) (a.1, m) * conj (canonicalKet C r)

/-- PDF p.8, Eq.(37): relational encoding obtained directly from the
untwirled physical token/message state in the actual coupled basis. -/
def relationalEncoding {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (J : JointDecomposition C U) (q : Fin J.count) :
    Superop (Fin s) (Fin (J.mult q)) :=
  fun X => traceLeft ((J.basis q)ᴴ * (pureDensity (canonicalKet C)).kronecker X * J.basis q)

/-- PDF pp.6–7, Eqs.(28),(33), Case B: projector onto precisely those
conjugate token irreps retained in `q* tensor q_S`. Character projectors avoid
choosing a second arbitrary Clebsch–Gordan basis. The character has no conjugate
here because the retained irreps themselves are the conjugate token irreps. -/
def reciprocalProjector {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {s : ℕ} {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (mu : Measure G) (J : JointDecomposition C U) (q : Fin J.count) :
    Matrix (Fin (J.dim q) × Fin s) (Fin (J.dim q) × Fin s) ℂ :=
  ∑ r, (C.dim r : ℂ) • ∫ g,
    (repMatrix (C.rep r) g).trace •
      (Matrix.kronecker (Matrix.of fun a b => conj (repMatrix (J.rep q) g a b)) (repMatrix U g)) ∂mu

/-- PDF p.9, Eq.(42): extraction from the actual relational subsystem. -/
def relationalRecovery {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (J : JointDecomposition C U) (q : Fin J.count) :
    Superop (Fin (J.mult q)) (Fin s) :=
  fun Z => traceLeft (relationalIsometry J q * Z * (relationalIsometry J q)ᴴ)

/-- PDF p.10, Eq.(47): measure the actual joint irrep, accept exactly those
whose reciprocal coupling contains no omitted token irrep, and extract the message. -/
def relationalAccepted {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {s : ℕ} {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (mu : Measure G) (J : JointDecomposition C U) :
    Superop (TokenIndex C × Fin s) (Fin s) :=
  fun Y => ∑ q, if reciprocalProjector mu J q = 1 then
    relationalRecovery J q (sectorBlock J q Y) else 0

/-- PDF p.10, Eq.(47): achieved good-sector weight; the sum may be empty. -/
def relationalSuccess {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {s : ℕ} {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (mu : Measure G) (J : JointDecomposition C U) : ℝ :=
  ∑ q, if reciprocalProjector mu J q = 1 then
    (J.dim q : ℝ) ^ 2 / tokenDimension C else 0

section GeneralResults

variable {G : Type*} [Group G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hCompact : CompactSpace G] [hT2 : T2Space G] [MeasurableSpace G] [hBorel : BorelSpace G]
  (mu : Measure G) [hHaar : Measure.IsHaarMeasure mu] [hProb : IsProbabilityMeasure mu]

include hTop hCompact hT2 hBorel hHaar hProb

end GeneralResults

/-- PDF p.11, Eq.(48): bounded phase token, including the vacuum cutoff `N = 0`. -/
def phaseKet (N : ℕ) : EuclideanSpace ℂ (Fin (N + 1)) :=
  WithLp.toLp 2 fun _ => ((Real.sqrt (N + 1 : ℝ))⁻¹ : ℂ)

/-- PDF p.11, Eq.(51): number representation with the same negative exponential
on token and message; `d` is the number of number-basis states. -/
def numberRotation (d : ℕ) (theta : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun n => Complex.exp (-Complex.I * (n.val : ℂ) * (theta : ℂ))

/-- PDF pp.4,11: token/message orbit Kraus operator for the phase example. -/
def phaseOrbitKraus (N : ℕ) (theta : ℝ) : Matrix (Fin (N + 1) × Fin 2) (Fin 2) ℂ :=
  fun a b => act (numberRotation (N + 1) theta) (phaseKet N) a.1 *
    numberRotation 2 theta a.2 b

/-- PDF p.11: normalized U(1) Haar integral of a periodic function, using the
interval `[0,2 pi]`; endpoints have measure zero. -/
def phaseAverage {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ → V) : V :=
  (2 * Real.pi)⁻¹ • ∫ theta in Set.Icc 0 (2 * Real.pi), f theta

/-- PDF p.11, Eqs.(48),(51): encoding from the actual common number rotation,
not from a postulated partial-dephasing channel. -/
def phaseEncoding (N : ℕ) : Superop (Fin 2) (Fin (N + 1) × Fin 2) :=
  fun X => phaseAverage fun theta => phaseOrbitKraus N theta * X * (phaseOrbitKraus N theta)ᴴ

/-- PDF pp.8,11: the covariant token measurement and conditional inverse rotation. -/
def phaseRecovery (N : ℕ) : Superop (Fin (N + 1) × Fin 2) (Fin 2) :=
  fun Y => (N + 1 : ℂ) • phaseAverage
    (fun theta => (phaseOrbitKraus N theta)ᴴ * Y * phaseOrbitKraus N theta)

/-- PDF p.11, Eq.(56): projection onto total occupation number `t`. -/
def numberProjector (N t : ℕ) : Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ :=
  Matrix.diagonal fun a => if a.1.val + a.2.val = t then 1 else 0

/-- PDF p.11, Eq.(56): subnormalized joint state in a measured total-number sector. -/
def phaseBranch (N t : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (N + 1) × Fin 2) (Fin (N + 1) × Fin 2) ℂ :=
  conjSuperop (numberProjector N t) ((pureDensity (phaseKet N)).kronecker X)

/-- PDF p.12, Eq.(58): coherent inverse on a number sector, zero outside it.
At an endpoint its initial space is one-dimensional. -/
def numberDecoder (N t : ℕ) : Matrix (Fin 2) (Fin (N + 1) × Fin 2) ℂ :=
  fun b a => if a.2 = b ∧ a.1.val + a.2.val = t then 1 else 0

/-- PDF p.12: subnormalized message recovered from the measured branch. -/
def phaseDecodedBranch (N t : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  conjSuperop (numberDecoder N t) (phaseBranch N t X)

/-- PDF p.12, Eq.(59): accepted physical subchannel on arbitrary joint inputs.
The accepted numbers are `1,...,N`, so for `N = 0` the sum is empty. -/
def phaseAccepted (N : ℕ) : Superop (Fin (N + 1) × Fin 2) (Fin 2) :=
  fun Y => ∑ t ∈ Finset.range (N + 2),
    if 0 < t ∧ t < N + 1 then conjSuperop (numberDecoder N t) Y else 0

/-- PDF pp.12,15: normalized symmetric-tensor weight basis for spin `k/2`.
Weight index `n` means magnetic weight `k/2 - n`. The denominator is nonzero
because `n : Fin (k+1)`. This fixes the actual spin representation, including phases. -/
def spinBasis (k : ℕ) : Matrix (Qubits k) (Fin (k + 1)) ℂ :=
  fun b n => if hammingWeight b = n.val then
    ((Real.sqrt (Nat.choose k n.val : ℝ))⁻¹ : ℂ) else 0

/-- PDF pp.12,15: the actual spin-`k/2` matrix, obtained by restricting the
`k`-fold tensor power of the fundamental qubit matrix to its symmetric subspace. -/
def spinMatrix (k : ℕ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  (spinBasis k)ᴴ *
    (Matrix.of fun a b : Qubits k => ∏ i, W (if a i then 1 else 0) (if b i then 1 else 0)) *
    spinBasis k

/-- PDF p.15, Eq.(101): the fundamental z-rotation in the standard weight basis. -/
def zRotation (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun b => if b = 0 then Complex.exp (-Complex.I * a / 2)
    else Complex.exp (Complex.I * a / 2)

/-- PDF p.15, Eq.(101): the fundamental y-rotation, including its off-diagonal signs. -/
def yRotation (b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then (Real.cos (b / 2) : ℂ)
    else if i = 0 then -(Real.sin (b / 2) : ℂ) else (Real.sin (b / 2) : ℂ)

/-- PDF p.15, Eqs.(99),(101): actual Euler-angle SU(2) matrix. -/
def eulerFundamental (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  zRotation a * yRotation b * zRotation c

/-- PDF p.15, normalized SU(2) Haar integration. The full Euler cover is
`a in [0,2pi], b in [0,pi], c in [0,4pi]` with density `sin b/(16 pi^2)`.
This is not the axis-angle half-cover of Eq.(69); normalization is valid also
for half-integer representations. Endpoints are null sets. -/
def su2Average {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ → ℝ → ℝ → V) : V :=
  (16 * Real.pi ^ 2)⁻¹ •
    ∫ a in Set.Icc 0 (2 * Real.pi),
      ∫ b in Set.Icc 0 Real.pi,
        ∫ c in Set.Icc 0 (4 * Real.pi), Real.sin b • f a b c

/-- PDF p.15, Eq.(94): highest-weight direction token, `j_R = k/2`. -/
def directionKet (k : ℕ) : EuclideanSpace ℂ (Fin (k + 1)) :=
  ket ⟨0, Nat.zero_lt_succ k⟩

/-- PDF p.15, Eq.(97): actual spin-coherent token orbit paired with the
fundamental message rotation. -/
def directionKraus (k : ℕ) (a b c : ℝ) :
    Matrix (Fin (k + 1) × Fin 2) (Fin 2) ℂ :=
  fun x y => act (spinMatrix k (eulerFundamental a b c)) (directionKet k) x.1 *
    eulerFundamental a b c x.2 y

/-- PDF p.15, Eq.(97): direction encoding by actual normalized SU(2) twirling. -/
def directionEncoding (k : ℕ) : Superop (Fin 2) (Fin (k + 1) × Fin 2) :=
  fun X => su2Average fun a b c =>
    directionKraus k a b c * X * (directionKraus k a b c)ᴴ

/-- PDF p.15, Eq.(98): direction POVM decoding, with `D_R = k+1`, not a sum
of squared irrep dimensions. -/
def directionRecovery (k : ℕ) : Superop (Fin (k + 1) × Fin 2) (Fin 2) :=
  fun Y => (k + 1 : ℂ) • su2Average
    (fun a b c => (directionKraus k a b c)ᴴ * Y * directionKraus k a b c)

/-- PDF pp.13,15: angular momentum z-matrix in the standard spin weight basis. -/
def spinZ (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun n => ((k : ℂ) / 2 - n.val)

/-- PDF pp.13,15: raising matrix in the standard spin weight basis. -/
def spinRaise (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun n m => if m.val = n.val + 1 then
    (Real.sqrt ((n.val + 1 : ℝ) * ((k : ℝ) - n.val)) : ℂ) else 0

/-- PDF pp.13,15, Eqs.(74),(106): `J_R dot sigma` determines the actual
spin-coupling spectral projectors, including the off-diagonal coupling phases. -/
def spinCoupling (k : ℕ) : Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℂ :=
  (spinZ k).kronecker (Matrix.diagonal (![1, -1] : Fin 2 → ℂ)) +
    (spinRaise k).kronecker (Matrix.single 1 0 1) +
    ((spinRaise k)ᴴ).kronecker (Matrix.single 0 1 1)

/-- PDF p.15, Eq.(106): projector onto `J = (k+1)/2`, as a spectral polynomial
of the actual total angular momentum. At `k=0` it is the full identity. -/
def spinPlus (k : ℕ) : Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℂ :=
  (k + 1 : ℂ)⁻¹ • (spinCoupling k + ((k + 2 : ℂ) / 2) • 1)

/-- PDF p.15, Eq.(106): projector onto `J = (k-1)/2`; it is zero when `k=0`. -/
def spinMinus (k : ℕ) : Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℂ :=
  1 - spinPlus k

/-- PDF p.16, Eq.(113): state prepared after the plus outcome by adjoint recovery. -/
def directionPlusState (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (![((k + 1 : ℂ) / (k + 2)), (k + 2 : ℂ)⁻¹] : Fin 2 → ℂ)

/-- PDF p.16: optimal decoder for an equiprobable z-bit, using the same actual
spin sectors and maximum-posterior repreparation. -/
def directionOptimal (k : ℕ) : Superop (Fin (k + 1) × Fin 2) (Fin 2) :=
  fun Y => ((spinPlus k * Y).trace) • Matrix.single 0 0 1 +
    ((spinMinus k * Y).trace) • Matrix.single 1 1 1

/-- PDF p.16: average input/output fidelity for exactly the two equiprobable
z-basis states, not entanglement fidelity or Haar-average pure-state fidelity. -/
def zBitFidelity (F : Superop (Fin 2) (Fin 2)) : ℝ :=
  ((F (Matrix.single 0 0 1) 0 0).re + (F (Matrix.single 1 1 1) 1 1).re) / 2

/-- PDF p.12, Eq.(60): every integer spin `0,...,L`, with paired memory of
its own dimension. Extra original multiplicity spaces are not included. -/
abbrev CartesianIndex (L : ℕ) :=
  (j : Fin (L + 1)) × (Fin (2 * j.val + 1) × Fin (2 * j.val + 1))

/-- PDF p.12, Eq.(61): restricted Cartesian-token dimension. -/
def cartesianDimension (L : ℕ) : ℕ :=
  ∑ j : Fin (L + 1), (2 * j.val + 1) ^ 2

/-- PDF p.12, Eq.(60): canonical token for the integer-spin cutoff. -/
def cartesianKet (L : ℕ) : EuclideanSpace ℂ (CartesianIndex L) :=
  WithLp.toLp 2 fun a => if a.2.1 = a.2.2 then
    (Real.sqrt ((2 * a.1.val + 1 : ℝ) / cartesianDimension L) : ℂ) else 0

/-- PDF pp.12–13, Eqs.(60),(63): actual Cartesian orbit under symmetric-tensor
spin matrices. Memory is unchanged; this formula avoids any arbitrary irrep data. -/
def cartesianOrbit (L : ℕ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    EuclideanSpace ℂ (CartesianIndex L) :=
  WithLp.toLp 2 fun a =>
    (Real.sqrt ((2 * a.1.val + 1 : ℝ) / cartesianDimension L) : ℂ) *
      spinMatrix (2 * a.1.val) W a.2.1 a.2.2

/-- PDF pp.12–13: actual canonical-token/message orbit Kraus operator. -/
def cartesianKraus (L : ℕ) (a b c : ℝ) :
    Matrix (CartesianIndex L × Fin 2) (Fin 2) ℂ :=
  fun x y => cartesianOrbit L (eulerFundamental a b c) x.1 *
    eulerFundamental a b c x.2 y

/-- PDF pp.12–13: Cartesian encoding with normalized SU(2) Haar law. -/
def cartesianEncoding (L : ℕ) : Superop (Fin 2) (CartesianIndex L × Fin 2) :=
  fun X => su2Average fun a b c => cartesianKraus L a b c * X * (cartesianKraus L a b c)ᴴ

/-- PDF pp.12–14: canonical adjoint recovery with the actual dimension factor. -/
def cartesianRecovery (L : ℕ) : Superop (CartesianIndex L × Fin 2) (Fin 2) :=
  fun Y => (cartesianDimension L : ℂ) • su2Average
    (fun a b c => (cartesianKraus L a b c)ᴴ * Y * cartesianKraus L a b c)

/-- PDF p.13, Eqs.(73)–(75): inclusion of a token-spin carrier and message,
with a fixed paired-memory index, into the full physical joint basis. -/
def cartesianSpinInclusion (L : ℕ) (j : Fin (L + 1)) (n : Fin (2 * j.val + 1)) :
    Matrix (CartesianIndex L × Fin 2) (Fin (2 * j.val + 1) × Fin 2) ℂ :=
  fun x y => if x = (⟨j, (y.1, n)⟩, y.2) then 1 else 0

/-- PDF pp.13–14: actual total-spin sector `J=t+1/2`, built from the
spectral spin-coupling projectors in each physical token summand. -/
def cartesianProjector (L t : ℕ) :
    Matrix (CartesianIndex L × Fin 2) (CartesianIndex L × Fin 2) ℂ :=
  ∑ j : Fin (L + 1), ∑ n : Fin (2 * j.val + 1),
    cartesianSpinInclusion L j n *
      (if t = j.val then spinPlus (2 * j.val)
       else if t + 1 = j.val then spinMinus (2 * j.val) else 0) *
      (cartesianSpinInclusion L j n)ᴴ

/-- PDF p.14, Eq.(93): accepted decoding after measuring total spin and
rejecting the single top sector. At cutoff zero the accepted set is empty. -/
def cartesianAccepted (L : ℕ) : Superop (CartesianIndex L × Fin 2) (Fin 2) :=
  fun Y => ∑ t ∈ Finset.range L,
    cartesianRecovery L (conjSuperop (cartesianProjector L t) Y)

/-! Small definition sanity checks; these are not proofs of the paper results. -/

example {G : Type*} [Group G] [TopologicalSpace G] {d : ℕ}
    (U : BasedUnitaryRep G d) (g : G) :
    (asProjectiveRep U).unitary g = U.hom g := by
  rfl

example {G : Type*} [Group G] [TopologicalSpace G] {d : ℕ} (U : BasedUnitaryRep G d) :
    repMatrix U 1 = 1 := by
  simp [repMatrix]

example {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G)
    (a : TokenIndex C) (h : a.2.1 ≠ a.2.2) : canonicalKet C a = 0 := by
  simp [canonicalKet, h]

example {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G)
    (q : Fin C.count) (b : Fin (C.dim q) × Fin (C.dim q)) :
    tokenInclusion C q ⟨q, b⟩ b = 1 := by
  simp [tokenInclusion]

example {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (J : JointDecomposition C U) (q : Fin J.count) : sectorBlock J q 0 = 0 := by
  ext a b
  simp [sectorBlock, traceLeft, Matrix.of] <;> rfl

example {G : Type*} [Group G] [TopologicalSpace G] (C : CanonicalToken G)
    (a : TokenIndex C) (hD : tokenDimension C = 1) (hd : C.dim a.1 = 1)
    (ha : a.2.1 = a.2.2) : canonicalKet C a = 1 := by
  simp [canonicalKet, hD, hd, ha]

example {G : Type*} [Group G] [TopologicalSpace G] {s : ℕ}
    {C : CanonicalToken G} {U : BasedUnitaryRep G s}
    (J : JointDecomposition C U) (q : Fin J.count) : relationalRecovery J q 0 = 0 := by
  ext a b
  simp [relationalRecovery, traceLeft, Matrix.of] <;> rfl

example : phaseKet 0 0 = 1 := by
  simp [phaseKet]

example (d : ℕ) : numberRotation d 0 = 1 := by
  simp [numberRotation]

example (X : Matrix (Fin 2) (Fin 2) ℂ) : dephasing (dephasing X) = dephasing X := by
  ext a b
  simp [dephasing, Matrix.diagonal_apply]

example (X : Matrix (Fin 2) (Fin 2) ℂ) : dephasing X 0 1 = 0 := by
  simp [dephasing]

example (Y : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ) : phaseAccepted 0 Y = 0 := by
  unfold phaseAccepted
  apply Finset.sum_eq_zero
  intro t ht
  have h : ¬(0 < t ∧ t < 0 + 1) := by omega
  exact if_neg h

example : mixed (O := Fin 1) = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [mixed]

example : spinBasis 0 (fun _ => false) 0 = 1 := by
  simp [spinBasis, hammingWeight]

example : spinBasis 1 (fun _ => false) 0 = 1 := by
  simp [spinBasis, hammingWeight]

example : yRotation 0 = 1 := by
  ext i j
  by_cases h : i = j <;> simp [yRotation, Matrix.one_apply, h]

example : eulerFundamental 0 0 0 = 1 := by
  have hy : yRotation 0 = 1 := by
    ext i j
    by_cases h : i = j <;> simp [yRotation, Matrix.one_apply, h]
  simp [eulerFundamental, zRotation, hy]

example (k : ℕ) : IsState (directionKet k) := by
  simp [directionKet, IsState, ket]

example (X : Matrix (Fin 2) (Fin 2) ℂ) : zBitFidelity (fun _ => X) =
    (X 0 0 + X 1 1).re / 2 := by
  simp [zBitFidelity]

example : cartesianDimension 0 = 1 := by
  simp [cartesianDimension]

example (Y : Matrix (CartesianIndex 0 × Fin 2) (CartesianIndex 0 × Fin 2) ℂ) :
    cartesianAccepted 0 Y = 0 := by
  simp [cartesianAccepted]

end QAlgorithms.Papers.Independent.Next46.P29


