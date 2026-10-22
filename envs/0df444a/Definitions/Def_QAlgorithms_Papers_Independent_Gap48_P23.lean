-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
-- name    : QAlgorithms_Papers_Independent_Gap48_P23
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T22:24:54.626993+00:00
-- url     : https://prove2.me/theorems/b9224f95-661f-4c4f-a0b0-3e7b24a0b127
-- title:
--   Definitions for Quantum majority vote
-- statement:
--   The objects the formalized statements of *Quantum majority vote* (arXiv:2211.11729) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `permuteWord`: PDF p.10, (2.1): action on words, with the inverse permutation.
--   - `wordPermutationMatrix`: PDF p.10, (2.1): physical permutation matrix.
--   - `encodedInput`: PDF p.11, (2.8): input density for an unknown word and common basis.
--   - `targetDensity`: PDF p.11, (2.9): ideal single-qudit output density.
--   - `WordSymmetric`: PDF p.12, Definition 2.3: symmetry under every coordinate permutation.
--   - `Equivariant`: PDF p.12, Definition 2.3: equivariance under every alphabet permutation.
--   - `inputFidelity`: PDF p.11, (2.10): squared overlap with the normalized pure target.
--   - `fidelityValues`: PDF pp.11-12, Definition 2.2: all allowed squared overlaps. For a channel, a nonempty promise and d>=1 these values form a nonempty bounded subset of [0,1]. No averaging over x or U is used.
--   - `functionFidelity`: PDF p.11, (2.11): worst case, used only with lawful channels and nonempty promises.
--   - `optimalFunctionFidelity`: PDF p.12: channel chosen before every unknown x and U. Attainment is retained explicitly by the optimality statements rather than inferred from this supremum.
--   - `IsFunctionOptimal`: PDF p.12: the channel attains the maximal worst-case fidelity.
--   - `booleanWordWeight`: PDF p.12: number of ones in a Boolean word.
--   - `weightRepresentative`: PDF p.17: the representative 0^(n-h)1^h; uses h<=n in every statement.
--   - `majority`: PDF pp.12,37: majority, with odd positive n imposed by theorems.
--   - `parity`: PDF p.36: Boolean parity.
--   - `majorityPromise`: PDF pp.1,38: minority booleanWordWeight at most floor(n/q), q=3 for the abstract/proof, q=6 for the distinct stronger printed promise on pp.5,37.
--   - `PermutationInvariant`: PDF p.15, Definition 2.7: equality on every operator.
--   - `WordUnitaryEquivariant`: PDF p.15, Definition 2.8: covariance on every operator.
--   - `permutationSymmetrization`: PDF p.14, (2.26): exact finite permutation average.
--   - `unitarySymmetrization`: PDF p.14, (2.26): normalized Haar twirling, on every operator.
--   - `functionOutputChoi`: PDF p.10, (2.5): unnormalized Choi matrix, output tensor input.
--   - `ofChoi`: PDF p.10, (2.6): inverse Choi map, on every operator.
--   - `idealNot`: PDF p.14, (2.25): the ideal complex-linear NOT, not a quantum channel.
--   - `CompletelyPositive`: PDF p.11: CP positivity tested on every reference system. This unbundled predicate is used only for maps whose linearity follows from their explicit body.
--   - `polynomialIrrep`: PDF p.58, (C.9): literal normalized-monomial coefficients. The guards are exactly the factorial/exponent domain, so natural subtraction never clips a term.
--   - `monomialKet`: PDF p.60, (C.15): normalized monomial ket, also defined at ell=0 and psi=0.
--   - `blockDiagonal`: PDF pp.63-64: direct sum of matrices, including an empty first sector.
--   - `ordinaryCG`: PDF p.63, (C.44): ordinary CG with the source real phases; nonexistent boundary kets are omitted by equality guards.
--   - `dualCG`: PDF p.64, (C.49): dual CG, S acts on the first qubit only.
--   - `lowerCGAction`: PDF p.63, (C.41): the first CG sector is absent at ell=0, rather than T^0.
--   - `lowerDualAction`: PDF p.64, (C.51): first dual sector, with empty ell=0 sector.
--   - `extremalChoi`: PDF pp.27-28, (4.4): literal D-based endpoint Choi matrices.
--   - `extremalChannel`: PDF p.27, Lemma 4.1: source endpoints defined by inverse Choi, on all operators.
--   - `symmetricEmbedding`: PDF p.29, (4.16): the accepted real Dicke embedding, in physical Bool coordinates.
--   - `dickeColumnProjector`: PDF p.65, (D.2): projector constructed from the Dicke columns.
--   - `symmetricEmbeddingChannel`: PDF p.68, (D.26): embedding channel, on all operators.
--   - `partialTraceChannel`: PDF p.29, (4.18): trace all but the first qubit. The ell>=1 theorem guard makes site zero valid; the zero-copy total value is unused.
--   - `universalNotChannel`: PDF p.29, (4.19): measure coherent states and prepare their orthogonal state. The accepted definition uses the complex trace booleanWordWeight, preserving linearity.
--   - `PolynomialCovariant`: PDF p.27: covariance uses exactly T^ell(U) on input and U on output.
--   - `traceKraus`: PDF p.73, (E.10): partial-trace Kraus family, including both adjacent bras.
--   - `notKraus`: PDF p.73, (E.11): negative first amplitude; endpoints need no invalid bras.
--   - `traceIsometry`: PDF p.77, (E.51): exact source lower isometry. For ell>=1 the accepted Fin((ell-1)+1) environment is naturally the source ell-dimensional space.
--   - `notIsometry`: PDF p.77, (E.52): exact source phases, the negative of the accepted upper isometry.
--   - `traceMatrixUnit`: PDF p.74, (E.17): all matrix-unit branches, not just diagonal probabilities.
--   - `notMatrixUnit`: PDF p.74, (E.18): both negative off-diagonal amplitudes are preserved.
--   - `TwoRowShape`: PDF p.18: two-row shape (n-k,k), including k=0.
--   - `degree`: PDF p.18: degree and dimension of the unitary register.
--   - `schurMultiplicity`: PDF p.18, (3.5): schurMultiplicity; the binomial predecessor at k=0 is zero.
--   - `SchurIndex`: PDF p.20: total coordinate index, with dependent ranges for w and i.
--   - `RealSchurCoefficients`: PDF p.20: the source's fixed real coefficient family, reused at every booleanWordWeight.
--   - `wordAt`: Physical coordinate lookup used only to avoid ill-typed boundary indices. All indices in the source seed are in range for a valid shape.
--   - `schurSeed`: PDF p.20, (3.11): Dicke vector followed by k ordered normalized singlets. The source |01>-|10> phase is retained.
--   - `schurVector`: PDF p.20, (3.13): actual constructed vectors, never an arbitrary Schur isometry.
--   - `LawfulCoefficients`: PDF p.20, (3.14)-(3.15): the ONLY basis assumptions are at w=0. Neither orthogonality at other weights nor block covariance is assumed.
--   - `schurTransform`: PDF p.21, (3.19): rows of the source Schur transform.
--   - `preprocessingBranch`: PDF p.21, Algorithm 1: retain the unitary register and trace schurMultiplicity.
--   - `ReducedIndex`: PDF p.21, Algorithm 1: classical shape label and quantum unitary register.
--   - `preprocessing`: PDF p.21: measuring the label removes cross-sector coherences.
--   - `schurRecovery`: PDF pp.23-24: schurRecovery measures the shape, tensors I_d/d, and applies inverse Schur. It is constructed independently of its left-inverse property.
--   - `permutationTwirl`: PDF p.23, (3.31): the input permutation unitarySymmetrization.
--   - `partitionIrrep`: PDF p.63, (C.39): polynomial partition action, including singular M.
--   - `reducedAction`: PDF p.21: direct-sum output action.
--   - `samplingProbability`: PDF p.22, (3.22), corrected support: printed k<=h, CHANGED k<=h<=n-k. WHY: h-k must be a valid unitary-register coordinate; at n=3,h=3,k=1 the printed probability is 2. Independent moderation of this correction is required.
--   - `predictedBranch`: PDF p.22: unnormalized block, with branch ket formed only on its support.
--   - `template`: PDF p.30, Algorithm 2: interpolation parameters fixed before all unknown inputs.
--   - `permutationBlock`: PDF p.49: permutation block computed in the w=0 coordinates.
--   - `unitarySubspace`: PDF p.56, (3.16): actual unitary subspace at a fixed schurMultiplicity label.
--   - `schurWeightProbability`: PDF p.31, (4.25): signed binomial difference, choose(n,-1)=0.
--   - `lpTraceCoefficient`: PDF p.31, (4.26): every subtraction is real.
--   - `lpNotCoefficient`: PDF p.31, (4.27): every subtraction is real.
--   - `FunctionLPFeasible`: PDF p.31, (LP): exactly floor(n/2)+2 real variables, and one fidelity inequality plus two cube inequalities per lower-half booleanWordWeight, hence 3floor(n/2)+3 constraints. No division is in naturals.
--   - `majorityWeightFidelity`: PDF p.37, (5.6): all-partial-trace per-booleanWordWeight majority fidelity.
--   - `recurrenceA`: PDF p.80, (F.5): recurrence coefficients, only used at 1<=h<=floor(n/2).
--   - `recurrenceB`: PDF p.80, (F.5): the signed numerator must not use natural subtraction.
--   - `majorityRecurrence`: PDF pp.36,82, Lemma 5.1: g(0)=0 is an unused totalization; the outer factor multiplies the ENTIRE bracket including +1.
--   - `tableFunction`: PDF p.35: lower-half truth table read left to right as the binary digits of mask; the upper half is determined by equivariance. Used only for odd n.
--   - `smallFidelities`: PDF p.35: literal finite tables; no extrapolated suffix rule.
--   - `parityFidelities`: PDF p.36: twenty computed parity values, n=1,3,...,39, without conjectural extrapolation.
--   - `schurDicke`: PDF p.20, (3.12): Dicke ket; invalid weights give zero. Valid weights in theorems are always bounded by ell.
--   - `pairDicke`: PDF p.69, (D.31): (ell+1)-qubit symmetric vector in first-qubit/rest coordinates.
--   - `primedDicke`: PDF p.69, (D.32): the primed Dicke vectors, with the negative second term.
--   - `physicalSymmetricSpace`: PDF p.68, (D.28): C^2 tensor Sym(ell).
--   - `traceSubspace`: PDF p.69, (D.33): actual partial-trace sector.
--   - `notSubspace`: PDF p.68, (D.29): actual UNOT sector in the same ambient space.
--   - `singletDicke`: PDF p.69, (D.37): ordered normalized singlet followed by ell-1 symmetric qubits.
--   - `symmetricCG`: PDF p.71, (D.48): rectangular physical CG from its actual row bras.
--   - `symmetricDualCG`: PDF p.72, (D.55): S on the first qubit, identity on ALL ell remaining qubits.
--   - `DiagramVertex`: PDF pp.51-53: vertices are left (false) and right (true) qubit endpoints.
--   - `singletEdge`: PDF p.51: source ordered singlet pair edges on one side.
--   - `diagramAdjacent`: PDF pp.51-52, (B.22): connectivity comes only from pi wires and seed pairs.
--   - `diagramFree`: PDF p.51: free endpoints are precisely the unpaired symmetric-register sites.
--   - `diagramConnected`: PDF p.51: paths follow the actual graph, independently of Hamming weights.
--   - `ProperMatching`: PDF p.51: a proper matching joins every pair of distinct free endpoints in a connected path on opposite sides. Closed loops are allowed.
--   - `diagramLoops`: PDF p.53: closed connected components, counted once as finite vertex sets.
--   - `ValidDiagramColoring`: PDF pp.51-54: binary contraction labels: wires preserve bits, singlets flip bits, and free endpoints are fixed at 0. This is an independent graph coloring specification, not an assumption on the desired matrix element.
--   - `diagramSign`: PDF p.53, (B.35): product of oriented S-entry signs in a fixed admissible coloring. A closed loop may be colored either way; its even number of singlet edges makes this product independent of that choice. The unused noncolorable case is totalized by +1. All reversed ordered singlets contribute their minus.
--   - `bilinearVectorize`: PDF p.45, (A.2): unnormalized vectorization, row index first.
--   - `vectorizedBra`: PDF p.45, footnote 13: bilinear vectorized bra, NOT Hilbert conjugate transpose.
--   - `vectorSwap`: PDF p.45: the two-system swap in the same tensor coordinates.
--   - `singleContraction`: PDF pp.45-46, (A.9): literal tensor contraction of a vectorized ket and bra.
--   - `networkChain`: PDF p.46, (A.10)-(A.12): independent tensor-network coefficient sum. The path has L edges and L+1 vertex labels, with its two endpoints fixed. This definition is a sum over internal tensor indices, not a matrix product.
--   - `alternatingFactors`: PDF p.46: alternating factors, with k A/B pairs and optionally a final A.
--   - `alternatingMatrixProduct`: PDF p.46: ordered product A_1 B_1 ... A_k B_k.
--   - `singletMatrix`: PDF p.48, (A.24): real antisymmetric singlet matrix.
--   - `normalizedSingletMatrix`: PDF p.51: normalized singlet matrix, whose vectorization is |Psi^->.
--   - `reversedKetFactors`: PDF pp.48,51: replace selected vectorized KETS by their transposes. Only even-position factors are kets; odd-position factors remain the bras.
--   - `reversalCount`: Count reversed kets actually present (k in the even chain; k+1 otherwise).
--   - `appendixMatrixLayout`: PDF pp.83-85: literal shared row layout of the eight printed 16x16 matrices. Each named matrix below supplies all eight integer entries and its printed scale; no channel or optimality assumption enters this construction.
--   - `optimalChoiID`: PDF p.82, G.1: literal identity Choi matrix.
--   - `optimalChoiNOT`: PDF p.82, G.1: literal optimal NOT Choi matrix, scale 1/3.
--   - `optimalChoiMAJ3`: PDF p.83, G.1: literal MAJ3 Choi matrix, scale 1/9.
--   - `optimalChoiPAR3`: PDF p.83, G.1: literal PAR3 Choi matrix, scale 1/15.
--   - `optimalChoiNPAR3`: PDF p.83, G.1: literal NPAR3 Choi matrix, scale 1/5.
--   - `optimalChoiNMAJ3`: PDF p.84, G.1: literal NMAJ3 Choi matrix, scale 1/45.
--   - `idealChoiID`: PDF p.84, G.2: literal ideal identity matrix, scale 1.
--   - `idealChoiNOT`: PDF p.84, G.2: literal ideal NOT matrix, scale 1.
--   - `idealChoiMAJ3`: PDF p.84, G.2: literal ideal MAJ3 matrix, scale 1/6.
--   - `idealChoiPAR3`: PDF p.85, G.2: literal ideal PAR3 matrix, scale 1/3.
--   - `idealChoiNPAR3`: PDF p.85, G.2: literal ideal NPAR3 matrix, scale 1/3.
--   - `idealChoiNMAJ3`: PDF p.85, G.2: literal ideal NMAJ3 matrix, scale 1/6.
--   - `flatOne`: Output-first lexicographic one-input coordinate order, PDF pp.82,84.
--   - `flatThree`: Output-first lexicographic three-input coordinate order, PDF pp.83-85.
--   - `appendixOneChannel`: PDF pp.82-85: inverse Choi applied to the literal one-input matrices.
--   - `appendixThreeChannel`: PDF pp.83-85: inverse Choi applied to the literal three-input matrices.
--   - `elementaryGateSet`: PDF p.33: exactly arbitrary unitary one-qubit gates and CNOT, with named wires supplied by the accepted Circuit syntax. No coefficient oracle is a gate.
--   - `OneOutputCircuit`: PDF pp.11,33,78-79: initialize zero ancillas, apply a finite chronological list of the specified gates, retain a named output qubit and discard the rest.
--   - `circuitOutput`: PDF p.11: exact mixed-input channel semantics, after the specified binary embedding J. Equality is on all operators, including entangled-input extensions.
--   - `wordBinaryEmbedding`: PDF p.33: coordinate identification of the source Fin-2 word with Bool wires.
--   - `controlledBinaryEmbedding`: PDF pp.78-79: binary embedding of a qubit and a (ell+1)-dimensional label.
--   - `controlledRotation`: PDF p.78, (E.58)-(E.60): label-controlled real rotation, with no oracle.
--   - `controlledDecrement`: PDF p.78, (E.61): decrement label modulo ell+1 if qubit is one.
--   - `controlledIncrement`: PDF p.79, (E.64): increment label modulo ell+2 if qubit is zero.
--   - `paddedRotation`: PDF pp.78-79: binary padding is identity outside valid labels.
--   - `paddedDecrement`: PDF pp.78-79: decrement padding is identity outside valid labels.
--   - `paddedIncrement`: PDF p.79: increment padding is identity outside valid labels.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, https://arxiv.org/abs/2211.11729v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

/-! Statements from Buhrman et al., Quantum majority vote, arXiv:2211.11729v1.
All page references are PDF pages. The finite alphabet is `Fin d`; thus Boolean
words use `Fin 2`, with the usual zero/one identification. All new definitions
are local to this paper; exact frozen helpers are imported and opened below. The accepted library is imported without modification.
Compilation is pending the external mechanical handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory
open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.
open QAlgorithms.Papers.Independent.Information100.P58 (Word)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.10, (2.1): action on words, with the inverse permutation. -/
def permuteWord {n d : ℕ} (p : Equiv.Perm (Fin n)) (x : Word n d) : Word n d :=
  Equiv.arrowCongr p (Equiv.refl (Fin d)) x

/-- PDF p.10, (2.1): physical permutation matrix. -/
def wordPermutationMatrix (n d : ℕ) (p : Equiv.Perm (Fin n)) : Op (Word n d) :=
  QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix
    (Equiv.arrowCongr p (Equiv.refl (Fin d)))

/-- PDF p.11, (2.8): input density for an unknown word and common basis. -/
def encodedInput {n d : ℕ} (U : Op (Fin d)) (x : Word n d) : Op (Word n d) :=
  conjSuperop (tensorPower n U) (Matrix.single x x 1)

/-- PDF p.11, (2.9): ideal single-qudit output density. -/
def targetDensity {d : ℕ} (U : Op (Fin d)) (b : Fin d) : Op (Fin d) :=
  conjSuperop U (Matrix.single b b 1)

/-- PDF p.12, Definition 2.3: symmetry under every coordinate permutation. -/
def WordSymmetric {n d : ℕ} (f : Word n d → Fin d) : Prop :=
  ∀ p x, f (permuteWord p x) = f x

/-- PDF p.12, Definition 2.3: equivariance under every alphabet permutation. -/
def Equivariant {n d : ℕ} (f : Word n d → Fin d) : Prop :=
  ∀ (p : Equiv.Perm (Fin d)) x, f (p ∘ x) = p (f x)

/-- PDF p.11, (2.10): squared overlap with the normalized pure target. -/
def inputFidelity {n d : ℕ} (f : Word n d → Fin d)
    (Phi : Superop (Word n d) (Fin d))
    (x : Word n d) (U : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  effectProb (targetDensity U.val (f x)) (Phi (encodedInput U.val x))

/-- PDF pp.11-12, Definition 2.2: all allowed squared overlaps.
For a channel, a nonempty promise and d>=1 these values form a nonempty bounded
subset of [0,1]. No averaging over x or U is used. -/
def fidelityValues {n d : ℕ} (P : Word n d → Prop) (f : Word n d → Fin d)
    (Phi : Superop (Word n d) (Fin d)) : Set ℝ :=
  {r | ∃ x, P x ∧ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, r = inputFidelity f Phi x U}

/-- PDF p.11, (2.11): worst case, used only with lawful channels and nonempty promises. -/
def functionFidelity {n d : ℕ} (P : Word n d → Prop) (f : Word n d → Fin d)
    (Phi : Superop (Word n d) (Fin d)) : ℝ := sInf (fidelityValues P f Phi)

/-- PDF p.12: channel chosen before every unknown x and U. Attainment is retained
explicitly by the optimality statements rather than inferred from this supremum. -/
def optimalFunctionFidelity {n d : ℕ} (P : Word n d → Prop) (f : Word n d → Fin d) : ℝ :=
  sSup {r | ∃ Phi : Superop (Word n d) (Fin d), IsChannel Phi ∧
    r = functionFidelity P f Phi}

/-- PDF p.12: the channel attains the maximal worst-case fidelity. -/
def IsFunctionOptimal {n d : ℕ} (P : Word n d → Prop) (f : Word n d → Fin d)
    (Phi : Superop (Word n d) (Fin d)) : Prop :=
  IsChannel Phi ∧ functionFidelity P f Phi = optimalFunctionFidelity P f

/-- PDF p.12: number of ones in a Boolean word. -/
def booleanWordWeight {n : ℕ} (x : Word n 2) : ℕ := (Finset.univ.filter (fun i => x i = 1)).card

/-- PDF p.17: the representative 0^(n-h)1^h; uses h<=n in every statement. -/
def weightRepresentative (n h : ℕ) : Word n 2 := fun i => if i.val < n - h then 0 else 1

/-- PDF pp.12,37: majority, with odd positive n imposed by theorems. -/
def majority (n : ℕ) (x : Word n 2) : Fin 2 := if n < 2 * booleanWordWeight x then 1 else 0

/-- PDF p.36: Boolean parity. -/
def parity (n : ℕ) (x : Word n 2) : Fin 2 := ⟨booleanWordWeight x % 2, Nat.mod_lt _ (by omega)⟩

/-- PDF pp.1,38: minority booleanWordWeight at most floor(n/q), q=3 for the abstract/proof,
q=6 for the distinct stronger printed promise on pp.5,37. -/
def majorityPromise (n q : ℕ) (x : Word n 2) : Prop := min (booleanWordWeight x) (n - booleanWordWeight x) ≤ n / q

/-- PDF p.15, Definition 2.7: equality on every operator. -/
def PermutationInvariant {n d : ℕ} (Phi : Superop (Word n d) (Fin d)) : Prop :=
  ∀ p rho, Phi (conjSuperop (wordPermutationMatrix n d p) rho) = Phi rho

/-- PDF p.15, Definition 2.8: covariance on every operator. -/
def WordUnitaryEquivariant {n d : ℕ} (Phi : Superop (Word n d) (Fin d)) : Prop :=
  ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
    Phi (conjSuperop (tensorPower n U.val) rho) = conjSuperop U.val (Phi rho)

/-- PDF p.14, (2.26): exact finite permutation average. -/
def permutationSymmetrization {n d : ℕ} (Phi : Superop (Word n d) (Fin d)) : Superop (Word n d) (Fin d) :=
  fun rho => (1 / (Nat.factorial n : ℂ)) •
    ∑ p : Equiv.Perm (Fin n), Phi (conjSuperop (wordPermutationMatrix n d p) rho)

/-- PDF p.14, (2.26): normalized Haar twirling, on every operator. -/
def unitarySymmetrization {n d : ℕ} (Phi : Superop (Word n d) (Fin d)) : Superop (Word n d) (Fin d) :=
  fun rho a b => ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    (conjSuperop U.valᴴ (Phi (conjSuperop (tensorPower n U.val) rho))) a b
      ∂Schur.unitaryHaar d

/-- PDF p.10, (2.5): unnormalized Choi matrix, output tensor input. -/
def functionOutputChoi {I O : Type*} [Fintype I] [DecidableEq I] (Phi : Superop I O) : Op (O × I) :=
  fun a b => QAlgorithms.Papers.Independent.Information100.P34.choi Phi
    (a.2, a.1) (b.2, b.1)

/-- PDF p.10, (2.6): inverse Choi map, on every operator. -/
def ofChoi {I O : Type*} [Fintype I] (J : Op (O × I)) : Superop I O :=
  fun rho a b => ∑ i, ∑ j, J (a, i) (b, j) * rho i j

/-- PDF p.14, (2.25): the ideal complex-linear NOT, not a quantum channel. -/
def idealNot : Superop (Fin 2) (Fin 2) := fun rho => rho.trace • 1 - rho

/-- PDF p.11: CP positivity tested on every reference system. This unbundled
predicate is used only for maps whose linearity follows from their explicit body. -/
def CompletelyPositive {I O : Type*} (Phi : Superop I O) : Prop :=
  ∀ r : ℕ, ∀ X : Op (Fin r × I), X.PosSemidef → (idTensorSuperop Phi X).PosSemidef

example : weightRepresentative 1 0 0 = 0 := by rfl

example (d : ℕ) (M : Op (Fin d)) (x y : Word 0 d) : tensorPower 0 M x y = 1 := by
  simp [tensorPower]

example : idealNot (0 : Op (Fin 2)) = 0 := by simp [idealNot]

example {I O : Type*} [Fintype I] [DecidableEq I] (Phi : Superop I O) (a b : O) (i j : I) :
    functionOutputChoi Phi (a, i) (b, j) = Phi (Matrix.single i j 1) a b := by rfl

/-- PDF p.58, (C.9): literal normalized-monomial coefficients. The guards are
exactly the factorial/exponent domain, so natural subtraction never clips a term. -/
def polynomialIrrep (ell : ℕ) (M : Op (Fin 2)) : Op (Fin (ell + 1)) :=
  fun j k => (Real.sqrt ((Nat.factorial j.val : ℝ) * Nat.factorial (ell - j.val) *
      Nat.factorial k.val * Nat.factorial (ell - k.val)) : ℂ) *
    ∑ r ∈ Finset.range (ell + 1),
      if r + j.val ≤ ell ∧ r + k.val ≤ ell ∧ ell ≤ j.val + k.val + r then
        M 0 0 ^ r * M 0 1 ^ (ell - j.val - r) * M 1 0 ^ (ell - k.val - r) *
          M 1 1 ^ (j.val + k.val + r - ell) /
          ((Nat.factorial r : ℂ) * Nat.factorial (ell - j.val - r) *
            Nat.factorial (ell - k.val - r) * Nat.factorial (j.val + k.val + r - ell))
      else 0

/-- PDF p.60, (C.15): normalized monomial ket, also defined at ell=0 and psi=0. -/
def monomialKet (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Fin (ell + 1)) :=
  WithLp.toLp 2 fun k => (Real.sqrt (Nat.choose ell k.val : ℝ) : ℂ) *
    psi 0 ^ (ell - k.val) * psi 1 ^ k.val

/-- PDF pp.63-64: direct sum of matrices, including an empty first sector. -/
def blockDiagonal {I J : Type*} (A : Op I) (B : Op J) : Op (I ⊕ J) :=
  fun x y => match x, y with
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inr i, Sum.inr j => B i j
  | _, _ => 0

/-- PDF p.63, (C.44): ordinary CG with the source real phases; nonexistent
boundary kets are omitted by equality guards. -/
def ordinaryCG (ell : ℕ) : Matrix (Fin ell ⊕ Fin (ell + 2)) (Fin 2 × Fin (ell + 1)) ℂ :=
  fun row col =>
    let i := col.1.val
    let k := col.2.val + i
    match row with
    | Sum.inl v => if v.val + 1 = k then
        (if i = 0 then (Real.sqrt (k : ℝ) : ℂ)
         else -(Real.sqrt ((ell : ℝ) + 1 - k) : ℂ)) / (Real.sqrt ((ell : ℝ) + 1) : ℂ)
      else 0
    | Sum.inr w => if w.val = k then
        (if i = 0 then (Real.sqrt ((ell : ℝ) + 1 - k) : ℂ)
         else (Real.sqrt (k : ℝ) : ℂ)) / (Real.sqrt ((ell : ℝ) + 1) : ℂ)
      else 0

/-- PDF p.64, (C.49): dual CG, S acts on the first qubit only. -/
def dualCG (ell : ℕ) := ordinaryCG ell *
  Matrix.kronecker (!![0, 1; -1, 0] : Op (Fin 2)) (1 : Op (Fin (ell + 1)))

/-- PDF p.63, (C.41): the first CG sector is absent at ell=0, rather than T^0. -/
def lowerCGAction (ell : ℕ) (M : Op (Fin 2)) : Op (Fin ell) :=
  fun i j => M.det * polynomialIrrep (ell - 1) M
    ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

/-- PDF p.64, (C.51): first dual sector, with empty ell=0 sector. -/
def lowerDualAction (ell : ℕ) (M : Op (Fin 2)) : Op (Fin ell) :=
  fun i j => polynomialIrrep (ell - 1) M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

/-- PDF pp.27-28, (4.4): literal D-based endpoint Choi matrices. -/
def extremalChoi (ell : ℕ) (second : Bool) : Op (Fin 2 × Fin (ell + 1)) :=
  (dualCG ell)ᴴ * blockDiagonal
    (if second then 0 else (((ell : ℂ) + 1) / ell) • (1 : Op (Fin ell)))
    (if second then (((ell : ℂ) + 1) / (ell + 2)) • (1 : Op (Fin (ell + 2))) else 0) * dualCG ell

/-- PDF p.27, Lemma 4.1: source endpoints defined by inverse Choi, on all operators. -/
def extremalChannel (ell : ℕ) (second : Bool) : Superop (Fin (ell + 1)) (Fin 2) :=
  ofChoi (extremalChoi ell second)

/-- PDF p.29, (4.16): the accepted real Dicke embedding, in physical Bool coordinates. -/
abbrev symmetricEmbedding := QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding

/-- PDF p.65, (D.2): projector constructed from the Dicke columns. -/
def dickeColumnProjector (ell : ℕ) : Op (Qubits ell) :=
  symmetricEmbedding ell * (symmetricEmbedding ell)ᴴ

/-- PDF p.68, (D.26): embedding channel, on all operators. -/
def symmetricEmbeddingChannel (ell : ℕ) : Superop (Fin (ell + 1)) (Qubits ell) :=
  conjSuperop (symmetricEmbedding ell)

/-- PDF p.29, (4.18): trace all but the first qubit. The ell>=1 theorem guard
makes site zero valid; the zero-copy total value is unused. -/
def partialTraceChannel (ell : ℕ) : Superop (Fin (ell + 1)) (Fin 2) :=
  fun rho => if h : 0 < ell then
    QAlgorithms.Papers.Independent.Support21.P18.siteReduction
      (symmetricEmbeddingChannel ell rho) ⟨0, h⟩ else 0

/-- PDF p.29, (4.19): measure coherent states and prepare their orthogonal state.
The accepted definition uses the complex trace booleanWordWeight, preserving linearity. -/
abbrev universalNotChannel := QAlgorithms.Papers.Independent.Support21.P18.measurementNot

/-- PDF p.27: covariance uses exactly T^ell(U) on input and U on output. -/
def PolynomialCovariant (ell : ℕ) (Phi : Superop (Fin (ell + 1)) (Fin 2)) : Prop :=
  ∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) rho,
    Phi (conjSuperop (polynomialIrrep ell U.val) rho) = conjSuperop U.val (Phi rho)

/-- PDF p.73, (E.10): partial-trace Kraus family, including both adjacent bras. -/
def traceKraus (ell : ℕ) (v : Fin ell) : Matrix (Fin 2) (Fin (ell + 1)) ℂ :=
  fun i j => if i = 0 ∧ j.val = v.val then
    (Real.sqrt (((ell : ℝ) - v.val) / ell) : ℂ)
    else if i = 1 ∧ j.val = v.val + 1 then
      (Real.sqrt (((v.val : ℝ) + 1) / ell) : ℂ) else 0

/-- PDF p.73, (E.11): negative first amplitude; endpoints need no invalid bras. -/
def notKraus (ell : ℕ) (w : Fin (ell + 2)) : Matrix (Fin 2) (Fin (ell + 1)) ℂ :=
  fun i j => if i = 0 ∧ j.val + 1 = w.val then
    -(Real.sqrt ((w.val : ℝ) / (ell + 2)) : ℂ)
    else if i = 1 ∧ j.val = w.val then
      (Real.sqrt (((ell : ℝ) + 1 - w.val) / (ell + 2)) : ℂ) else 0

/-- PDF p.77, (E.51): exact source lower isometry. For ell>=1 the accepted
Fin((ell-1)+1) environment is naturally the source ell-dimensional space. -/
abbrev traceIsometry := QAlgorithms.Papers.Independent.Support21.P18.lowerIsometry

/-- PDF p.77, (E.52): exact source phases, the negative of the accepted upper isometry. -/
def notIsometry (ell : ℕ) := -QAlgorithms.Papers.Independent.Support21.P18.upperIsometry ell

/-- PDF p.74, (E.17): all matrix-unit branches, not just diagonal probabilities. -/
def traceMatrixUnit (ell : ℕ) (w v : Fin (ell + 1)) : Op (Fin 2) :=
  if w = v then Matrix.diagonal ![(((ell : ℝ) - w.val) / ell : ℂ), ((w.val : ℝ) / ell : ℂ)]
  else if v.val = w.val + 1 then
    (Real.sqrt (((ell : ℝ) - w.val) * v.val) / ell : ℂ) • Matrix.single 0 1 1
  else if w.val = v.val + 1 then
    (Real.sqrt (((ell : ℝ) - v.val) * w.val) / ell : ℂ) • Matrix.single 1 0 1
  else 0

/-- PDF p.74, (E.18): both negative off-diagonal amplitudes are preserved. -/
def notMatrixUnit (ell : ℕ) (w v : Fin (ell + 1)) : Op (Fin 2) :=
  if w = v then Matrix.diagonal ![(((w.val : ℝ) + 1) / (ell + 2) : ℂ),
      (((ell : ℝ) + 1 - w.val) / (ell + 2) : ℂ)]
  else if v.val = w.val + 1 then
    (-(Real.sqrt (((ell : ℝ) + 1 - v.val) * (w.val + 1))) / (ell + 2) : ℂ) • Matrix.single 0 1 1
  else if w.val = v.val + 1 then
    (-(Real.sqrt (((ell : ℝ) + 1 - w.val) * (v.val + 1))) / (ell + 2) : ℂ) • Matrix.single 1 0 1
  else 0

example : monomialKet 0 (0 : EuclideanSpace ℂ (Fin 2)) 0 = 1 := by simp [monomialKet]

example : ordinaryCG 0 (Sum.inr (0 : Fin 2)) (0, 0) = 1 := by
  norm_num [ordinaryCG]

example (ell : ℕ) : lowerCGAction 0 (0 : Op (Fin 2)) = (0 : Op (Fin 0)) := by
  funext i
  exact Fin.elim0 i

example (ell : ℕ) : notKraus ell 0 0 0 = 0 := by simp [notKraus]

/-- PDF p.18: two-row shape (n-k,k), including k=0. -/
abbrev TwoRowShape (n : ℕ) := Fin (n / 2 + 1)

/-- PDF p.18: degree and dimension of the unitary register. -/
def degree (n : ℕ) (k : TwoRowShape n) : ℕ := n - 2 * k.val

/-- PDF p.18, (3.5): schurMultiplicity; the binomial predecessor at k=0 is zero. -/
def schurMultiplicity (n : ℕ) (k : TwoRowShape n) : ℕ :=
  Nat.choose n k.val - if k.val = 0 then 0 else Nat.choose n (k.val - 1)

/-- PDF p.20: total coordinate index, with dependent ranges for w and i. -/
abbrev SchurIndex (n : ℕ) := Sigma fun k : TwoRowShape n => Fin (degree n k + 1) × Fin (schurMultiplicity n k)

/-- PDF p.20: the source's fixed real coefficient family, reused at every booleanWordWeight. -/
abbrev RealSchurCoefficients (n : ℕ) := (k : TwoRowShape n) → Fin (schurMultiplicity n k) → Equiv.Perm (Fin n) → ℝ

/-- Physical coordinate lookup used only to avoid ill-typed boundary indices.
All indices in the source seed are in range for a valid shape. -/
def wordAt {n : ℕ} (x : Word n 2) (j : ℕ) : Fin 2 := if h : j < n then x ⟨j, h⟩ else 0

/-- PDF p.20, (3.11): Dicke vector followed by k ordered normalized singlets.
The source |01>-|10> phase is retained. -/
def schurSeed (n : ℕ) (k : TwoRowShape n) (w : Fin (degree n k + 1)) :
    EuclideanSpace ℂ (Word n 2) :=
  WithLp.toLp 2 fun x =>
    if (∑ j : Fin (degree n k), if wordAt x j.val = 1 then 1 else 0) = w.val then
      ((Real.sqrt (Nat.choose (degree n k) w.val : ℝ))⁻¹ : ℂ) *
        ∏ j : Fin k.val,
          if wordAt x (degree n k + 2 * j.val) = 0 ∧
              wordAt x (degree n k + 2 * j.val + 1) = 1 then
            ((Real.sqrt 2)⁻¹ : ℂ)
          else if wordAt x (degree n k + 2 * j.val) = 1 ∧
              wordAt x (degree n k + 2 * j.val + 1) = 0 then
            -((Real.sqrt 2)⁻¹ : ℂ) else 0
    else 0

/-- PDF p.20, (3.13): actual constructed vectors, never an arbitrary Schur isometry. -/
def schurVector {n : ℕ} (alpha : RealSchurCoefficients n) (a : SchurIndex n) :
    EuclideanSpace ℂ (Word n 2) :=
  if a.2.2.val = 0 then schurSeed n a.1 a.2.1 else
    ∑ p : Equiv.Perm (Fin n), (alpha a.1 a.2.2 p : ℂ) •
      WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n a.1 a.2.1))

/-- PDF p.20, (3.14)-(3.15): the ONLY basis assumptions are at w=0.
Neither orthogonality at other weights nor block covariance is assumed. -/
def LawfulCoefficients {n : ℕ} (alpha : RealSchurCoefficients n) : Prop :=
  ∀ k : TwoRowShape n,
    (∀ i j : Fin (schurMultiplicity n k),
      inner ℂ (schurVector alpha ⟨k, ⟨⟨0, by omega⟩, i⟩⟩)
        (schurVector alpha ⟨k, ⟨⟨0, by omega⟩, j⟩⟩) = if i = j then 1 else 0) ∧
    Submodule.span ℂ (Set.range (fun i : Fin (schurMultiplicity n k) =>
      schurVector alpha ⟨k, ⟨⟨0, by omega⟩, i⟩⟩)) =
    Submodule.span ℂ (Set.range (fun p : Equiv.Perm (Fin n) =>
      WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n k ⟨0, by omega⟩))))

/-- PDF p.21, (3.19): rows of the source Schur transform. -/
def schurTransform {n : ℕ} (alpha : RealSchurCoefficients n) : Matrix (SchurIndex n) (Word n 2) ℂ :=
  fun a x => conj (schurVector alpha a x)

/-- PDF p.21, Algorithm 1: retain the unitary register and trace schurMultiplicity. -/
def preprocessingBranch {n : ℕ} (alpha : RealSchurCoefficients n) (k : TwoRowShape n)
    (rho : Op (Word n 2)) : Op (Fin (degree n k + 1)) :=
  fun w v => ∑ i : Fin (schurMultiplicity n k),
    (schurTransform alpha * rho * (schurTransform alpha)ᴴ) ⟨k, (w, i)⟩ ⟨k, (v, i)⟩

/-- PDF p.21, Algorithm 1: classical shape label and quantum unitary register. -/
abbrev ReducedIndex (n : ℕ) := Sigma fun k : TwoRowShape n => Fin (degree n k + 1)

/-- PDF p.21: measuring the label removes cross-sector coherences. -/
def preprocessing {n : ℕ} (alpha : RealSchurCoefficients n) : Superop (Word n 2) (ReducedIndex n) :=
  fun rho a b => if h : a.1 = b.1 then
    preprocessingBranch alpha a.1 rho a.2 (h.symm ▸ b.2) else 0

/-- PDF pp.23-24: schurRecovery measures the shape, tensors I_d/d, and applies
inverse Schur. It is constructed independently of its left-inverse property. -/
def schurRecovery {n : ℕ} (alpha : RealSchurCoefficients n) : Superop (ReducedIndex n) (Word n 2) :=
  fun rho => (schurTransform alpha)ᴴ *
    (Matrix.of fun (a b : SchurIndex n) => if h : a.1 = b.1 then
      if a.2.2.val = b.2.2.val then rho ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ /
        (schurMultiplicity n a.1 : ℂ) else 0 else 0) * schurTransform alpha

/-- PDF p.23, (3.31): the input permutation unitarySymmetrization. -/
def permutationTwirl (n : ℕ) : Superop (Word n 2) (Word n 2) :=
  fun rho => (1 / (Nat.factorial n : ℂ)) •
    ∑ p : Equiv.Perm (Fin n), conjSuperop (wordPermutationMatrix n 2 p) rho

/-- PDF p.63, (C.39): polynomial partition action, including singular M. -/
def partitionIrrep (n : ℕ) (k : TwoRowShape n) (M : Op (Fin 2)) :=
  M.det ^ k.val • polynomialIrrep (degree n k) M

/-- PDF p.21: direct-sum output action. -/
def reducedAction (n : ℕ) (M : Op (Fin 2)) : Op (ReducedIndex n) :=
  fun a b => if h : a.1 = b.1 then partitionIrrep n a.1 M a.2 (h.symm ▸ b.2) else 0

/-- PDF p.22, (3.22), corrected support: printed k<=h, CHANGED k<=h<=n-k.
WHY: h-k must be a valid unitary-register coordinate; at n=3,h=3,k=1 the
printed probability is 2. Independent moderation of this correction is required. -/
def samplingProbability (n h : ℕ) (k : TwoRowShape n) : ℝ :=
  if k.val ≤ h ∧ h ≤ n - k.val then
    ((Nat.choose n k.val : ℝ) - (if k.val = 0 then 0 else (Nat.choose n (k.val - 1) : ℝ))) /
      (Nat.choose n h : ℝ) else 0

/-- PDF p.22: unnormalized block, with branch ket formed only on its support. -/
def predictedBranch (n : ℕ) (k : TwoRowShape n) (h : ℕ) (U : Op (Fin 2)) : Op (Fin (degree n k + 1)) :=
  if hsupport : k.val ≤ h ∧ h ≤ n - k.val then
    if hvalid : h - k.val < degree n k + 1 then
      (samplingProbability n h k : ℂ) • conjSuperop (partitionIrrep n k U)
        (Matrix.single ⟨h - k.val, hvalid⟩ ⟨h - k.val, hvalid⟩ 1) else 0
  else 0

/-- PDF p.30, Algorithm 2: interpolation parameters fixed before all unknown inputs. -/
def template {n : ℕ} (alpha : RealSchurCoefficients n) (t : TwoRowShape n → ℝ) :
    Superop (Word n 2) (Fin 2) :=
  fun rho => ∑ k : TwoRowShape n,
    ((t k : ℂ) • partialTraceChannel (degree n k) (preprocessingBranch alpha k rho) +
      ((1 - t k : ℝ) : ℂ) • universalNotChannel (degree n k) (preprocessingBranch alpha k rho))

/-- PDF p.49: permutation block computed in the w=0 coordinates. -/
def permutationBlock {n : ℕ} (alpha : RealSchurCoefficients n) (k : TwoRowShape n)
    (p : Equiv.Perm (Fin n)) : Op (Fin (schurMultiplicity n k)) :=
  fun i j => inner ℂ (schurVector alpha ⟨k, (⟨0, by omega⟩, i)⟩)
    (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec
      (schurVector alpha ⟨k, (⟨0, by omega⟩, j)⟩)))

/-- PDF p.56, (3.16): actual unitary subspace at a fixed schurMultiplicity label. -/
def unitarySubspace {n : ℕ} (alpha : RealSchurCoefficients n) (k : TwoRowShape n) (i : Fin (schurMultiplicity n k)) :=
  Submodule.span ℂ (Set.range (fun w : Fin (degree n k + 1) => schurVector alpha ⟨k, (w, i)⟩))

example : schurMultiplicity 1 0 = 1 := by norm_num [schurMultiplicity]

example : samplingProbability 3 3 ⟨1, by norm_num⟩ = 0 := by norm_num [samplingProbability]

example {n : ℕ} (alpha : RealSchurCoefficients n) (a : SchurIndex n) (hi : a.2.2.val = 0) :
    schurVector alpha a = schurSeed n a.1 a.2.1 := by simp [schurVector, hi]

/-- PDF p.31, (4.25): signed binomial difference, choose(n,-1)=0. -/
def schurWeightProbability (n h k : ℕ) : ℝ :=
  ((Nat.choose n k : ℝ) - if k = 0 then 0 else (Nat.choose n (k - 1) : ℝ)) /
    (Nat.choose n h : ℝ)

/-- PDF p.31, (4.26): every subtraction is real. -/
def lpTraceCoefficient {n : ℕ} (f : Word n 2 → Fin 2) (h k : ℕ) : ℝ :=
  ((n : ℝ) - h - k - (f (weightRepresentative n h)).val * ((n : ℝ) - 2 * h)) /
    ((n : ℝ) - 2 * k)

/-- PDF p.31, (4.27): every subtraction is real. -/
def lpNotCoefficient {n : ℕ} (f : Word n 2 → Fin 2) (h k : ℕ) : ℝ :=
  ((h : ℝ) - k + 1 + (f (weightRepresentative n h)).val * ((n : ℝ) - 2 * h)) /
    ((n : ℝ) - 2 * k + 2)

/-- PDF p.31, (LP): exactly floor(n/2)+2 real variables, and one fidelity
inequality plus two cube inequalities per lower-half booleanWordWeight, hence 3floor(n/2)+3
constraints. No division is in naturals. -/
def FunctionLPFeasible {n : ℕ} (f : Word n 2 → Fin 2) (c : ℝ) (t : TwoRowShape n → ℝ) : Prop :=
  (∀ k, 0 ≤ t k ∧ t k ≤ 1) ∧
  ∀ h : TwoRowShape n, c ≤ ∑ k : TwoRowShape n, if k.val ≤ h.val then
    schurWeightProbability n h.val k.val *
      (t k * lpTraceCoefficient f h.val k.val + (1 - t k) * lpNotCoefficient f h.val k.val) else 0

/-- PDF p.37, (5.6): all-partial-trace per-booleanWordWeight majority fidelity. -/
def majorityWeightFidelity (n h : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (h + 1), schurWeightProbability n h k *
    (((n : ℝ) - h - k) / ((n : ℝ) - 2 * k))

/-- PDF p.80, (F.5): recurrence coefficients, only used at 1<=h<=floor(n/2). -/
def recurrenceA (n h : ℕ) : ℝ :=
  (((n : ℝ) - 2 * h) * h) / (((n : ℝ) - 2 * h + 2) * ((n : ℝ) - h + 1))

/-- PDF p.80, (F.5): the signed numerator must not use natural subtraction. -/
def recurrenceB (n h : ℕ) : ℝ :=
  (4 * (h : ℝ)^2 - (4 * (n : ℝ) + 5) * h + ((n : ℝ) + 1) * ((n : ℝ) + 2)) /
    (((n : ℝ) - 2 * h + 2) * ((n : ℝ) - h + 1))

/-- PDF pp.36,82, Lemma 5.1: g(0)=0 is an unused totalization; the outer
factor multiplies the ENTIRE bracket including +1. -/
def majorityRecurrence : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 8 / 9
  | m + 3 =>
    let z : ℝ := m + 3
    2 * z / ((2 * z - 1)^2 * (2 * z + 1)) *
      ((2 * z * (4 * z - 7) + 5) * majorityRecurrence (m + 2) -
        4 * (z - 1) * (z - 2) * majorityRecurrence (m + 1) + 1)

/-- PDF p.35: lower-half truth table read left to right as the binary digits
of mask; the upper half is determined by equivariance. Used only for odd n. -/
def tableFunction (n mask : ℕ) (x : Word n 2) : Fin 2 :=
  let h := booleanWordWeight x
  let j := if h ≤ n / 2 then h else n - h
  let b := (mask / 2 ^ (n / 2 - j)) % 2
  if h ≤ n / 2 then ⟨b, Nat.mod_lt _ (by omega)⟩
  else ⟨1 - b, by have : b < 2 := Nat.mod_lt _ (by omega); omega⟩

/-- PDF p.35: literal finite tables; no extrapolated suffix rule. -/
def smallFidelities (n : ℕ) : List ℝ := match n with
  | 1 => [1, 2/3]
  | 3 => [8/9, 3/5, 4/5, 29/45]
  | 5 => [62/75, 4/7, 5/7, 95/153, 124/153, 4/7, 5/7, 331/525]
  | 7 => [2888/3675, 5/9, 2/3, 47/78, 59/78, 5/9, 2/3, 1141/1845,
      1444/1845, 5/9, 2/3, 47/78, 59/78, 5/9, 2/3, 6841/11025]
  | _ => []

/-- PDF p.36: twenty computed parity values, n=1,3,...,39, without conjectural extrapolation. -/
def parityFidelities : List ℝ :=
  [1, 3/5, 5/7, 5/9, 7/11, 7/13, 3/5, 9/17, 11/19, 11/21,
   13/23, 13/25, 5/9, 15/29, 17/31, 17/33, 19/35, 19/37, 7/13, 21/41]

example : majorityRecurrence 2 = (8 / 9 : ℝ) := by rfl

example (n : ℕ) : schurWeightProbability n 0 0 = 1 := by simp [schurWeightProbability]

example : parityFidelities.length = 20 := by rfl

/-- PDF p.20, (3.12): Dicke ket; invalid weights give zero. Valid weights
in theorems are always bounded by ell. -/
def schurDicke (ell w : ℕ) : EuclideanSpace ℂ (Qubits ell) :=
  QAlgorithms.Papers.Independent.Information100.P22.dicke (I := Fin ell) w

/-- PDF p.69, (D.31): (ell+1)-qubit symmetric vector in first-qubit/rest coordinates. -/
def pairDicke (ell w : ℕ) : EuclideanSpace ℂ (Fin 2 × Qubits ell) :=
  WithLp.toLp 2 fun x => if x.1.val + hammingWeight x.2 = w then
    ((Real.sqrt (Nat.choose (ell+1) w : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.69, (D.32): the primed Dicke vectors, with the negative second term. -/
def primedDicke (ell : ℕ) (w : Fin ell) : EuclideanSpace ℂ (Fin 2 × Qubits ell) :=
  WithLp.toLp 2 fun x =>
    if x.1 = 0 then (Real.sqrt (((w.val : ℝ)+1)/(ell+1)) : ℂ) * schurDicke ell (w.val+1) x.2
    else -(Real.sqrt (((ell : ℝ)-w.val)/(ell+1)) : ℂ) * schurDicke ell w.val x.2

/-- PDF p.68, (D.28): C^2 tensor Sym(ell). -/
def physicalSymmetricSpace (ell : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin 2 × Qubits ell)) :=
  Submodule.span ℂ (Set.range (fun a : Fin 2 × Fin (ell+1) =>
    WithLp.toLp 2 fun x : Fin 2 × Qubits ell => if x.1 = a.1 then schurDicke ell a.2.val x.2 else 0))

/-- PDF p.69, (D.33): actual partial-trace sector. -/
def traceSubspace (ell : ℕ) := Submodule.span ℂ (Set.range (primedDicke ell))

/-- PDF p.68, (D.29): actual UNOT sector in the same ambient space. -/
def notSubspace (ell : ℕ) := Submodule.span ℂ (Set.range (fun w : Fin (ell+2) => pairDicke ell w.val))

/-- PDF p.69, (D.37): ordered normalized singlet followed by ell-1 symmetric qubits. -/
def singletDicke (ell : ℕ) (w : Fin ell) : EuclideanSpace ℂ (Fin 2 × Qubits ell) :=
  WithLp.toLp 2 fun x => if h : 0 < ell then
    (if x.1 = 0 ∧ x.2 ⟨0,h⟩ = true then ((Real.sqrt 2)⁻¹ : ℂ)
     else if x.1 = 1 ∧ x.2 ⟨0,h⟩ = false then -((Real.sqrt 2)⁻¹ : ℂ) else 0) *
    schurDicke (ell-1) w.val (fun j => x.2 ⟨j.val+1, by omega⟩)
  else 0

/-- PDF p.71, (D.48): rectangular physical CG from its actual row bras. -/
def symmetricCG (ell : ℕ) : Matrix (Fin ell ⊕ Fin (ell+2)) (Fin 2 × Qubits ell) ℂ :=
  fun row x => match row with
  | Sum.inl v => conj (primedDicke ell v x)
  | Sum.inr w => conj (pairDicke ell w.val x)

/-- PDF p.72, (D.55): S on the first qubit, identity on ALL ell remaining qubits. -/
def symmetricDualCG (ell : ℕ) := symmetricCG ell *
  Matrix.kronecker (!![0,1;-1,0] : Op (Fin 2)) (1 : Op (Qubits ell))

example (x : Qubits 0) : schurDicke 0 0 x = 1 := by
  simp [schurDicke, QAlgorithms.Papers.Independent.Information100.P22.dicke, hammingWeight]

/-- PDF pp.51-53: vertices are left (false) and right (true) qubit endpoints. -/
abbrev DiagramVertex (n : ℕ) := Bool × Fin n

/-- PDF p.51: source ordered singlet pair edges on one side. -/
def singletEdge {n : ℕ} (k : TwoRowShape n) (a b : Fin n) : Prop :=
  ∃ j : Fin k.val, (a.val = degree n k + 2*j.val ∧ b.val = degree n k + 2*j.val+1) ∨
    (b.val = degree n k + 2*j.val ∧ a.val = degree n k + 2*j.val+1)

/-- PDF pp.51-52, (B.22): connectivity comes only from pi wires and seed pairs. -/
def diagramAdjacent {n : ℕ} (k l : TwoRowShape n) (p : Equiv.Perm (Fin n))
    (a b : DiagramVertex n) : Prop :=
  if a.1 = b.1 then singletEdge (if a.1 then l else k) a.2 b.2
  else if a.1 then b.2 = p a.2 else a.2 = p b.2

/-- PDF p.51: free endpoints are precisely the unpaired symmetric-register sites. -/
def diagramFree {n : ℕ} (k l : TwoRowShape n) (a : DiagramVertex n) : Prop :=
  a.2.val < degree n (if a.1 then l else k)

/-- PDF p.51: paths follow the actual graph, independently of Hamming weights. -/
def diagramConnected {n : ℕ} (k l : TwoRowShape n) (p : Equiv.Perm (Fin n))
    (a b : DiagramVertex n) : Prop := Relation.ReflTransGen (diagramAdjacent k l p) a b

/-- PDF p.51: a proper matching joins every pair of distinct free endpoints
in a connected path on opposite sides. Closed loops are allowed. -/
def ProperMatching {n : ℕ} (k l : TwoRowShape n) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b, diagramFree k l a → diagramFree k l b → a ≠ b →
    diagramConnected k l p a b → a.1 ≠ b.1

/-- PDF p.53: closed connected components, counted once as finite vertex sets. -/
def diagramLoops {n : ℕ} (k : TwoRowShape n) (p : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ.image (fun a : DiagramVertex n =>
    Finset.univ.filter (fun b => diagramConnected k k p a b))).filter
      (fun component => ∀ a ∈ component, ¬ diagramFree k k a)).card

/-- PDF pp.51-54: binary contraction labels: wires preserve bits, singlets
flip bits, and free endpoints are fixed at 0. This is an independent graph
coloring specification, not an assumption on the desired matrix element. -/
def ValidDiagramColoring {n : ℕ} (k : TwoRowShape n) (p : Equiv.Perm (Fin n))
    (z : DiagramVertex n → Bool) : Prop :=
  (∀ j : Fin n, z (false,p j) = z (true,j)) ∧
  (∀ side : Bool, ∀ a b : Fin n, singletEdge k a b → z (side,a) ≠ z (side,b)) ∧
  (∀ a, diagramFree k k a → z a = false)

/-- PDF p.53, (B.35): product of oriented S-entry signs in a fixed admissible
coloring. A closed loop may be colored either way; its even number of singlet
edges makes this product independent of that choice. The unused noncolorable
case is totalized by +1. All reversed ordered singlets contribute their minus. -/
def diagramSign {n : ℕ} (k : TwoRowShape n) (p : Equiv.Perm (Fin n)) : ℝ :=
  if h : ∃ z, ValidDiagramColoring k p z then
    let z := h.choose
    ∏ side : Bool, ∏ j : Fin k.val,
      if z (side, ⟨degree n k + 2*j.val, by
        have hk := k.isLt
        have hj := j.isLt
        unfold degree
        omega⟩) then (-1:ℝ) else 1
  else 1

/-- PDF p.45, (A.2): unnormalized vectorization, row index first. -/
def bilinearVectorize {d : ℕ} (A : Op (Fin d)) : Fin d × Fin d → ℂ := fun p => A p.1 p.2

/-- PDF p.45, footnote 13: bilinear vectorized bra, NOT Hilbert conjugate transpose. -/
def vectorizedBra {d : ℕ} (B : Op (Fin d)) (v : Fin d × Fin d → ℂ) : ℂ :=
  ∑ p, bilinearVectorize B p * v p

/-- PDF p.45: the two-system swap in the same tensor coordinates. -/
def vectorSwap (d : ℕ) : Op (Fin d × Fin d) := fun x y => if x = (y.2,y.1) then 1 else 0

/-- PDF pp.45-46, (A.9): literal tensor contraction of a vectorized ket and bra. -/
def singleContraction {d : ℕ} (A B : Op (Fin d)) : Op (Fin d) :=
  fun a b => ∑ i, A a i * B i b

/-- PDF p.46, (A.10)-(A.12): independent tensor-network coefficient sum.
The path has L edges and L+1 vertex labels, with its two endpoints fixed.
This definition is a sum over internal tensor indices, not a matrix product. -/
def networkChain {d : ℕ} (L : ℕ) (M : Fin L → Op (Fin d)) : Op (Fin d) :=
  fun a b => ∑ z : Fin (L+1) → Fin d,
    if z 0 = a ∧ z ⟨L, by omega⟩ = b then
      ∏ j : Fin L, M j (z ⟨j.val, by omega⟩) (z ⟨j.val+1, by omega⟩)
    else 0

/-- PDF p.46: alternating factors, with k A/B pairs and optionally a final A. -/
def alternatingFactors {d : ℕ} (k extra : ℕ)
    (A : Fin (k+1) → Op (Fin d)) (B : Fin (k+1) → Op (Fin d))
    (j : Fin (2*k+extra)) : Op (Fin d) :=
  if h : j.val / 2 < k+1 then
    if j.val % 2 = 0 then A ⟨j.val/2,h⟩ else B ⟨j.val/2,h⟩
  else 0

/-- PDF p.46: ordered product A_1 B_1 ... A_k B_k. -/
def alternatingMatrixProduct {d : ℕ} (k : ℕ) (A B : Fin (k+1) → Op (Fin d)) : Op (Fin d) :=
  (List.ofFn (fun j : Fin k => A ⟨j.val,by omega⟩ * B ⟨j.val,by omega⟩)).prod

/-- PDF p.48, (A.24): real antisymmetric singlet matrix. -/
def singletMatrix : Op (Fin 2) := !![0,1;-1,0]

/-- PDF p.51: normalized singlet matrix, whose vectorization is |Psi^->. -/
def normalizedSingletMatrix : Op (Fin 2) := ((Real.sqrt 2)⁻¹ : ℂ) • singletMatrix

/-- PDF pp.48,51: replace selected vectorized KETS by their transposes.
Only even-position factors are kets; odd-position factors remain the bras. -/
def reversedKetFactors (k extra : ℕ) (M : Op (Fin 2))
    (reverse : Fin (k+1) → Bool) (j : Fin (2*k+extra)) : Op (Fin 2) :=
  if h : j.val/2 < k+1 then
    if j.val%2 = 0 ∧ reverse ⟨j.val/2,h⟩ = true then M.transpose else M
  else 0

/-- Count reversed kets actually present (k in the even chain; k+1 otherwise). -/
def reversalCount (k extra : ℕ) (reverse : Fin (k+1) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin (2*k+extra))).filter (fun j =>
    if h : j.val/2 < k+1 then j.val%2 = 0 ∧ reverse ⟨j.val/2,h⟩ = true else False)).card

example {d : ℕ} (A : Op (Fin d)) (i j : Fin d) : bilinearVectorize A (i,j) = A i j := by rfl

example : vectorizedBra (!![Complex.I,0;0,0] : Op (Fin 2))
    (bilinearVectorize (!![Complex.I,0;0,0] : Op (Fin 2))) = -1 := by
  norm_num [vectorizedBra, bilinearVectorize, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- PDF pp.83-85: literal shared row layout of the eight printed 16x16
matrices. Each named matrix below supplies all eight integer entries and its
printed scale; no channel or optimality assumption enters this construction. -/
def appendixMatrixLayout (a b c d e f g q : ℂ) : Op (Fin 16) :=
  !![a,0,0,0,0,0,0,0,0,b,b,0,b,0,0,0;
     0,c,q,0,q,0,0,0,0,0,0,d,0,d,e,0;
     0,q,c,0,q,0,0,0,0,0,0,d,0,e,d,0;
     0,0,0,f,0,-q,-q,0,0,0,0,0,0,0,0,b;
     0,q,q,0,c,0,0,0,0,0,0,e,0,d,d,0;
     0,0,0,-q,0,f,-q,0,0,0,0,0,0,0,0,b;
     0,0,0,-q,0,-q,f,0,0,0,0,0,0,0,0,b;
     0,0,0,0,0,0,0,g,0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0,g,0,0,0,0,0,0,0;
     b,0,0,0,0,0,0,0,0,f,-q,0,-q,0,0,0;
     b,0,0,0,0,0,0,0,0,-q,f,0,-q,0,0,0;
     0,d,d,0,e,0,0,0,0,0,0,c,0,q,q,0;
     b,0,0,0,0,0,0,0,0,-q,-q,0,f,0,0,0;
     0,d,e,0,d,0,0,0,0,0,0,q,0,c,q,0;
     0,e,d,0,d,0,0,0,0,0,0,q,0,q,c,0;
     0,0,0,b,0,b,b,0,0,0,0,0,0,0,0,a]

/-- PDF p.82, G.1: literal identity Choi matrix. -/
def optimalChoiID : Op (Fin 4) := !![1,0,0,1;0,0,0,0;0,0,0,0;1,0,0,1]

/-- PDF p.82, G.1: literal optimal NOT Choi matrix, scale 1/3. -/
def optimalChoiNOT : Op (Fin 4) := (1/3:ℂ) • !![1,0,0,-1;0,2,0,0;0,0,2,0;-1,0,0,1]

/-- PDF p.83, G.1: literal MAJ3 Choi matrix, scale 1/9. -/
def optimalChoiMAJ3 := (1/9:ℂ) • appendixMatrixLayout 9 3 8 5 (-4) 1 0 (-1)

/-- PDF p.83, G.1: literal PAR3 Choi matrix, scale 1/15. -/
def optimalChoiPAR3 := (1/15:ℂ) • appendixMatrixLayout 9 1 6 (-1) 4 9 6 1

/-- PDF p.83, G.1: literal NPAR3 Choi matrix, scale 1/5. -/
def optimalChoiNPAR3 := (1/5:ℂ) • appendixMatrixLayout 1 (-1) 4 1 (-4) 1 4 (-1)

/-- PDF p.84, G.1: literal NMAJ3 Choi matrix, scale 1/45. -/
def optimalChoiNMAJ3 := (1/45:ℂ) • appendixMatrixLayout 9 (-9) 16 (-11) 4 29 36 1

/-- PDF p.84, G.2: literal ideal identity matrix, scale 1. -/
def idealChoiID := optimalChoiID

/-- PDF p.84, G.2: literal ideal NOT matrix, scale 1. -/
def idealChoiNOT : Op (Fin 4) := !![0,0,0,-1;0,1,0,0;0,0,1,0;-1,0,0,0]

/-- PDF p.84, G.2: literal ideal MAJ3 matrix, scale 1/6. -/
def idealChoiMAJ3 := (1/6:ℂ) • appendixMatrixLayout 6 2 6 4 (-4) 0 0 (-1)

/-- PDF p.85, G.2: literal ideal PAR3 matrix, scale 1/3. -/
def idealChoiPAR3 := (1/3:ℂ) • appendixMatrixLayout 3 1 0 (-1) 4 3 0 1

/-- PDF p.85, G.2: literal ideal NPAR3 matrix, scale 1/3. -/
def idealChoiNPAR3 := (1/3:ℂ) • appendixMatrixLayout 0 (-1) 3 1 (-4) 0 3 (-1)

/-- PDF p.85, G.2: literal ideal NMAJ3 matrix, scale 1/6. -/
def idealChoiNMAJ3 := (1/6:ℂ) • appendixMatrixLayout 0 (-2) 0 (-4) 4 6 6 1

/-- Output-first lexicographic one-input coordinate order, PDF pp.82,84. -/
def flatOne (a : Fin 2 × Word 1 2) : Fin 4 :=
  ⟨2*a.1.val+(a.2 0).val, by have := a.1.isLt; have := (a.2 0).isLt; omega⟩

/-- Output-first lexicographic three-input coordinate order, PDF pp.83-85. -/
def flatThree (a : Fin 2 × Word 3 2) : Fin 16 :=
  ⟨8*a.1.val+4*(a.2 0).val+2*(a.2 1).val+(a.2 2).val, by
    have := a.1.isLt; have := (a.2 0).isLt; have := (a.2 1).isLt; have := (a.2 2).isLt; omega⟩

/-- PDF pp.82-85: inverse Choi applied to the literal one-input matrices. -/
def appendixOneChannel (ideal : Bool) (mask : Fin 2) : Superop (Word 1 2) (Fin 2) :=
  ofChoi ((if ideal then ![idealChoiID, idealChoiNOT] mask
    else ![optimalChoiID, optimalChoiNOT] mask).submatrix flatOne flatOne)

/-- PDF pp.83-85: inverse Choi applied to the literal three-input matrices. -/
def appendixThreeChannel (ideal : Bool) (mask : Fin 4) : Superop (Word 3 2) (Fin 2) :=
  ofChoi ((if ideal then ![idealChoiMAJ3, idealChoiPAR3, idealChoiNPAR3, idealChoiNMAJ3] mask
    else ![optimalChoiMAJ3, optimalChoiPAR3, optimalChoiNPAR3, optimalChoiNMAJ3] mask).submatrix flatThree flatThree)

example : idealChoiNOT 0 3 = -1 := by rfl

example : optimalChoiNMAJ3 7 7 = (4/5:ℂ) := by
  change (1 / 45 : ℂ) * 36 = (4 / 5 : ℂ)
  norm_num

/-- PDF p.33: exactly arbitrary unitary one-qubit gates and CNOT, with named
wires supplied by the accepted Circuit syntax. No coefficient oracle is a gate. -/
def elementaryGateSet : Set Gate :=
  {g | ∃ M : Matrix Bool Bool ℂ, M ∈ Matrix.unitaryGroup Bool ℂ ∧ g = Gate.ofMatrix1 M} ∪
  {Gate.ofMatrix2 cnot}

/-- PDF pp.11,33,78-79: initialize zero ancillas, apply a finite chronological
list of the specified gates, retain a named output qubit and discard the rest. -/
structure OneOutputCircuit (inputWires : ℕ) where
  added : ℕ
  circuit : Circuit elementaryGateSet (inputWires + added)
  output : Fin (inputWires + added)

/-- PDF p.11: exact mixed-input channel semantics, after the specified binary
embedding J. Equality is on all operators, including entangled-input extensions. -/
def circuitOutput {n : ℕ} {I : Type*} [Fintype I]
    (C : OneOutputCircuit n) (J : Matrix (Qubits n) I ℂ) : Superop I (Fin 2) :=
  fun rho => QAlgorithms.Papers.Independent.Support21.P18.siteReduction
    (conjSuperop C.circuit.unitary (withZeroAncillas (J * rho * Jᴴ) C.added)) C.output

/-- PDF p.33: coordinate identification of the source Fin-2 word with Bool wires. -/
def wordBinaryEmbedding (n : ℕ) : Matrix (Qubits n) (Word n 2) ℂ :=
  fun z x => if (fun i => QAlgorithms.Papers.Independent.Support21.P18.bitIndex (z i)) = x then 1 else 0

/-- PDF pp.78-79: binary embedding of a qubit and a (ell+1)-dimensional label. -/
def controlledBinaryEmbedding (ell : ℕ) :
    Matrix (Qubits (1+Nat.clog 2 (ell+1))) (Fin 2 × Fin (ell+1)) ℂ :=
  fun z a => if (QAlgorithms.Papers.Independent.Support21.P18.bitIndex ((qubitsAppendEquiv 1 (Nat.clog 2 (ell+1)) z).1 0)) = a.1 then
    finiteRegisterEmbedding (ell+1) (qubitsAppendEquiv 1 (Nat.clog 2 (ell+1)) z).2 a.2 else 0

/-- PDF p.78, (E.58)-(E.60): label-controlled real rotation, with no oracle. -/
def controlledRotation (ell : ℕ) : Op (Fin 2 × Fin (ell+1)) :=
  fun a b => if a.2 = b.2 then
    ((!![(Real.sqrt (((ell:ℝ)-b.2.val)/ell) : ℂ), -(Real.sqrt ((b.2.val:ℝ)/ell) : ℂ);
         (Real.sqrt ((b.2.val:ℝ)/ell) : ℂ), (Real.sqrt (((ell:ℝ)-b.2.val)/ell) : ℂ)] : Op (Fin 2)) a.1 b.1)
  else 0

/-- PDF p.78, (E.61): decrement label modulo ell+1 if qubit is one. -/
def controlledDecrement (ell : ℕ) : Op (Fin 2 × Fin (ell+1)) :=
  fun a b => if a.1 = b.1 ∧ a.2.val = (b.2.val + (ell+1) - b.1.val) % (ell+1) then 1 else 0

/-- PDF p.79, (E.64): increment label modulo ell+2 if qubit is zero. -/
def controlledIncrement (ell : ℕ) : Op (Fin 2 × Fin (ell+2)) :=
  fun a b => if a.1 = b.1 ∧ a.2.val = (b.2.val + 1 - b.1.val) % (ell+2) then 1 else 0

/-- PDF pp.78-79: binary padding is identity outside valid labels. -/
def paddedRotation (ell : ℕ) := extendEncodedUnitary (controlledBinaryEmbedding ell) (controlledRotation ell)

/-- PDF pp.78-79: decrement padding is identity outside valid labels. -/
def paddedDecrement (ell : ℕ) := extendEncodedUnitary (controlledBinaryEmbedding ell) (controlledDecrement ell)

/-- PDF p.79: increment padding is identity outside valid labels. -/
def paddedIncrement (ell : ℕ) := extendEncodedUnitary (controlledBinaryEmbedding (ell+1)) (controlledIncrement ell)

example : Gate.ofMatrix2 cnot ∈ elementaryGateSet := Set.mem_union_right _ rfl

example (ell : ℕ) (z : Qubits (1+Nat.clog 2 (ell+1)))
    (hz : ∀ a, controlledBinaryEmbedding ell z a = 0) (y : Qubits (1+Nat.clog 2 (ell+1))) :
    paddedRotation ell z y = (1 : Op (Qubits (1+Nat.clog 2 (ell+1)))) z y := by
  simp [paddedRotation, extendEncodedUnitary, Matrix.mul_apply, hz]

end QAlgorithms.Papers.Independent.Gap48.P23


