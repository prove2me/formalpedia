-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22
-- name    : QAlgorithms_Papers_Independent_Extend50_P22
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T17:10:47.227722+00:00
-- url     : https://prove2.me/theorems/74c935e0-6300-43a3-b66b-cbbf78b7b5c3
-- title:
--   Definitions for Continuous symmetries and approximate quantum error correction
-- statement:
--   The objects the formalized statements of *Continuous symmetries and approximate quantum error correction* (arXiv:1902.07714) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `entangledInputRootFidelity`: PDF p.6, (6): root fidelity on one fixed reference-entangled unit input.
--   - `fixedFidelity`: PDF p.6, (8a), and pp.27,67: optimize over all CPTP recoveries for a fixed input. On the channels and unit inputs used below this set is nonempty and bounded in [0,1].
--   - `worstFidelity`: PDF p.6, (7),(8b): one recovery is chosen before the minimum over unit inputs.
--   - `errorE`: PDF p.6, (9a): the average-entanglement error, not average pure-state error.
--   - `errorWorst`: PDF p.6, (9b): optimal worst-case entanglement infidelity parameter.
--   - `TensorBasis`: Finite tensor-product computational coordinates (PDF p.5).
--   - `CovariantErasureCodeData`: PDF p.5, isometric code with positive logical and local dimensions and n>0.
--   - `splice`: PDF p.6, (11b): splice erased coordinates back into a remaining configuration.
--   - `erase`: PDF p.6, (11b): erasure resets the chosen sites to fixed normalized pure vectors.
--   - `CovariantErasureCodeData.reset`: The coordinate choice for the arbitrary fixed pure resets in (10), PDF p.6.
--   - `locationFlaggedChannel`: PDF p.6, (11a): orthogonal location flag, including all off-diagonal input blocks.
--   - `CovariantErasureCodeData.noise`: PDF pp.6,8: composite encoding and single located erasure, with probabilities q.
--   - `CovariantErasureCodeData.uniformNoise`: PDF p.8: uniform single erasure qi=1/n.
--   - `finiteMax`: PDF p.8: finite maximum, always used with an explicitly positive number of sites.
--   - `chargeRange`: PDF p.8: spectral range, from the actual Hermitian eigenvalues with multiplicity. Its uses below have positive dimension, so both finite extrema are attained.
--   - `meanSpread`: PDF pp.8,36: the trace-norm mean-centered charge spread, with factor 1/(2d).
--   - `liftLocal`: PDF p.8: lift one local observable, with identity on every other site.
--   - `ChargeCovariant`: PDF pp.7–8, (21): exact charge covariance, including the allowed scalar offset.
--   - `localTensorProduct`: PDF pp.8,15: tensor product of local physical operators.
--   - `Transversal`: PDF p.53: pointwise transversality; no continuity of individual factor choices is asserted.
--   - `SUCovariant`: PDF pp.14,56: continuous transversal representations of SU(d), defining logical action.
--   - `FullAction`: PDF p.15, (53): actual continuous local U(d) representations implementing the logical U.
--   - `CovariantErasureCodeData.maxDim`: PDF pp.14–16: largest local dimension; never the total physical dimension.
--   - `CovariantErasureCodeData.logDim`: PDF p.14: max_i ln(di), equivalently ln(max_i di) since all di are positive.
--   - `chargeEvolution`: PDF p.7, (17): the source's negative-sign one-parameter unitary action.
--   - `hilbertRootFidelity`: PDF pp.5,68: root fidelity on general Hilbert-space density operators. The accepted trace-class model supplies the basis trace. On positive trace-class inputs the square-root sandwich has trace-class square root, so this series is absolutely summable; a finite-dimensional cutoff is not imposed.
--   - `gaussianNormalization`: PDF pp.12,41: the same Gaussian normalization c_w as (39),(D.13).
--   - `theta3Imaginary`: PDF p.46: DLMF nome convention theta3(i*b,q); every summand is real for imaginary z.
--   - `theta2Zero`: PDF p.46: theta2(0,q) in the source's nome convention.
--   - `normalizedWeylDimension`: PDF p.55, (E.8): finite-row adapter to the accepted Weyl dimension formula. The zero extension outside d is never read by the product.
--   - `symmetricRows`: PDF p.55: nonnegative rows of the accepted symmetric highest weight. Int.toNat is lossless because every entry of this weight is nonnegative.
--   - `upSpins`: PDF p.49, (D.60): number of up-spins at magnetization m (used only at admissible parity).
--   - `dickeMarginalWeight`: PDF p.49, (D.60): hypergeometric weights in the common d-spin Dicke eigenbasis. The explicit k<=upSpins branch prevents truncated subtraction from inventing a binomial term.
--   - `dickeMarginalRootFidelity`: PDF p.49, (D.61): root fidelity of the actual commuting magnetization marginals.
--   - `basisMapMatrix`: PDF pp.17–19: matrix of a computational-basis map, with output index first. The definition accepts any function; the group actions used below are bijective.
--   - `uniformErase`: PDF p.6, (11b): uniform-coordinate erasure with an arbitrary fixed basis reset.
--   - `groupErase`: PDF pp.17–19: erase a subset of uniformly G-labelled sites, resetting them to |1>.
--   - `CorrectsGroupErasure`: PDF p.18: exact correctability is existence of one CPTP recovery acting on every operator. The recovery is chosen before the input; no performance predicate is assumed as a hypothesis.
--   - `orbitEncoding`: PDF p.18: normalized finite-group orbit sum. The displayed constructions make g recoverable from their first output coordinate, so there are |G| distinct terms.
--   - `groupFourEncoding`: PDF p.18, (65): preserve the order of all four noncommutative group products.
--   - `stabilizedFourEncoding`: PDF p.18, (67): the distinct stabilized four-site code.
--   - `groupAt`: PDF pp.18–19: total indexing helper for the alternating even-length word. The default is used only outside the logical index interval, at the separately handled endpoints.
--   - `evenWord`: PDF pp.18–19, (68): the general word, with (68) its m=4 example. m=k+2, so endpoints and the nontrivial logical system are present. The second coordinate is handled separately to avoid truncated 1-2 subtraction.
--   - `evenEncoding`: PDF pp.18–19: normalized collective-left orbit of the alternating word.
--   - `evenPhysical`: PDF p.19, (69): right multipliers on adjacent pairs of physical sites.
--   - `evenLogical`: PDF p.19, (70): the independent odd-numbered logical right multipliers.
--   - `bitEncoding`: PDF p.17, (60a): the three-site bit code.
--   - `groupPhaseEncoding`: PDF p.17, (60b): the three-site phase code, with ordered group product.
--   - `shiftError`: PDF p.17: one local left shift, including the identity error.
--   - `diagonalError`: PDF p.17: arbitrary diagonal error on the specified site.
--   - `CorrectsOperators`: PDF pp.17–18: exact Knill–Laflamme criterion for the span of a specified error family.
--   - `baconShorEncoding`: PDF p.18: concatenate m-fold phase encoding with an m-fold bit encoding of each factor. The first member k=0 is the one-site identity code.
--   - `cyclicEncoding`: PDF p.19, (72): the finite cyclic candidate, normalized for every positive modulus.
--   - `wEncoding`: PDF p.16, (55): normalized W-code isometry, vacancy labelled d in each local Fin(d+1).
--   - `sharpDims`: PDF p.11: finite interval embeddings containing the complete support of (36), including the x-dependent second and third coordinate ranges.
--   - `sharpEncoding`: PDF p.11, (36): the sharp code, without discarding any amplitude outside [-m,m] in the second and third physical coordinates.
--   - `CorrectsUniformErasure`: PDF pp.12,18,23: exact recovery of a uniform-coordinate erased set, with fixed reset.
--   - `fiveQuditEncoding`: PDF p.12, (42),(43): normalized cyclic five-qudit tensor; phases are evaluated modulo D.
--   - `quditCharge`: PDF p.12: natural integer charge on one qudit, distinguished from its value modulo D.
--   - `twoLocalEncoding`: PDF p.23: standard [[4,2,2]] basis, ordered so XXII flips the first logical bit.
--   - `twoLocalQ`: PDF p.23: Q=X tensor X tensor I tensor I, supported on the first two physical qubits.
--   - `firstLogicalX`: PDF p.23: the nontrivial first-logical-qubit Pauli X.
--   - `tensorCartan`: PDF p.56: the specified Cartan generator diag(1,0,...,0,-1) on tensor space. It is the sum of the one-cell generators, with the inherited Hilbert inner product.
--   - `schurCartan`: PDF p.56: actual generator on the constructed Schur module. Restriction is expressed using orthogonal projection, as in the accepted polynomial representation; tensorCartan preserves the Young-symmetrizer image. Its norm is the Hilbert operator norm.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, https://arxiv.org/abs/1902.07714v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_SchurModules
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P65
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

/-!
Statements from Faist et al., arXiv:1902.07714v1. All page numbers are PDF pages.
The finite-dimensional model uses arbitrary CPTP recovery maps and root fidelity.
The reference is a copy of the logical register. Fixed reset vectors are computational
basis vectors: choosing these is a coordinate convention for the fixed pure resets
in (10), which the receiver can replace freely. Infinite-dimensional results whose
full interfaces are not completed are explicitly inventoried in HARD.md and GAPS.json.
Compilation is pending the batch mechanical stage.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)
open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)
open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.6, (6): root fidelity on one fixed reference-entangled unit input. -/
def entangledInputRootFidelity {d : ℕ} (K : Superop (Fin d) (Fin d))
    (psi : EuclideanSpace ℂ (Fin d × Fin d)) : ℝ :=
  rootFidelity (pureDensity psi) (idTensorSuperop K (pureDensity psi))

/-- PDF p.6, (8a), and pp.27,67: optimize over all CPTP recoveries for a fixed input.
On the channels and unit inputs used below this set is nonempty and bounded in [0,1]. -/
def fixedFidelity {d : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (C : Superop (Fin d) B) (psi : EuclideanSpace ℂ (Fin d × Fin d)) : ℝ :=
  sSup {f | ∃ R : Superop B (Fin d), IsChannel R ∧ f = entangledInputRootFidelity (R ∘ C) psi}

/-- PDF p.6, (7),(8b): one recovery is chosen before the minimum over unit inputs. -/
def worstFidelity {d : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (C : Superop (Fin d) B) : ℝ :=
  sSup {f | ∃ R : Superop B (Fin d), IsChannel R ∧
    f = sInf {g | ∃ psi : EuclideanSpace ℂ (Fin d × Fin d),
      IsState psi ∧ g = entangledInputRootFidelity (R ∘ C) psi}}

/-- PDF p.6, (9a): the average-entanglement error, not average pure-state error. -/
def errorE {d : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (C : Superop (Fin d) B) : ℝ :=
  Real.sqrt (1 - fixedFidelity C (bell (Fin d)) ^ 2)

/-- PDF p.6, (9b): optimal worst-case entanglement infidelity parameter. -/
def errorWorst {d : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (C : Superop (Fin d) B) : ℝ :=
  Real.sqrt (1 - worstFidelity C ^ 2)

/-- Finite tensor-product computational coordinates (PDF p.5). -/
abbrev TensorBasis {n : ℕ} (dims : Fin n → ℕ) := (i : Fin n) → Fin (dims i)

/-- PDF p.5, isometric code with positive logical and local dimensions and n>0. -/
structure CovariantErasureCodeData (d n : ℕ) where
  logicalPositive : 0 < d
  sitesPositive : 0 < n
  dims : Fin n → ℕ
  dimsPositive : ∀ i, 0 < dims i
  V : Matrix (TensorBasis dims) (Fin d) ℂ
  isometry : Vᴴ * V = 1

/-- PDF p.6, (11b): splice erased coordinates back into a remaining configuration. -/
def splice {n : ℕ} {dims : Fin n → ℕ} (S : Finset (Fin n))
    (y : TensorBasis dims) (a : (i : S) → Fin (dims i)) : TensorBasis dims :=
  fun i => if h : i ∈ S then a ⟨i, h⟩ else y i

/-- PDF p.6, (11b): erasure resets the chosen sites to fixed normalized pure vectors. -/
def erase {n : ℕ} {dims : Fin n → ℕ} (S : Finset (Fin n))
    (reset : (i : Fin n) → Fin (dims i)) : Superop (TensorBasis dims) (TensorBasis dims) :=
  fun X y z => if (∀ i ∈ S, y i = reset i ∧ z i = reset i) then
    ∑ a : (i : S) → Fin (dims i), X (splice S y a) (splice S z a) else 0

/-- The coordinate choice for the arbitrary fixed pure resets in (10), PDF p.6. -/
def CovariantErasureCodeData.reset {d n : ℕ} (c : CovariantErasureCodeData d n) (i : Fin n) : Fin (c.dims i) :=
  ⟨0, c.dimsPositive i⟩

/-- PDF p.6, (11a): orthogonal location flag, including all off-diagonal input blocks. -/
def locationFlaggedChannel {K A B : Type*} [Fintype K] (q : K → ℝ) (C : K → Superop A B) :
    Superop A (K × B) :=
  fun X y z => if y.1 = z.1 then (q y.1 : ℂ) * C y.1 X y.2 z.2 else 0

/-- PDF pp.6,8: composite encoding and single located erasure, with probabilities q. -/
def CovariantErasureCodeData.noise {d n : ℕ} (c : CovariantErasureCodeData d n) (q : Fin n → ℝ) :
    Superop (Fin d) (Fin n × TensorBasis c.dims) :=
  locationFlaggedChannel q (fun i => erase {i} c.reset ∘ conjSuperop c.V)

/-- PDF p.8: uniform single erasure qi=1/n. -/
def CovariantErasureCodeData.uniformNoise {d n : ℕ} (c : CovariantErasureCodeData d n) := c.noise (fun _ => (n : ℝ)⁻¹)

/-- PDF p.8: finite maximum, always used with an explicitly positive number of sites. -/
def finiteMax {B : Type*} [LinearOrder B] {n : ℕ} (hn : 0 < n) (f : Fin n → B) : B :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ f

/-- PDF p.8: spectral range, from the actual Hermitian eigenvalues with multiplicity.
Its uses below have positive dimension, so both finite extrema are attained. -/
def chargeRange {I : Type*} [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) : ℝ :=
  sSup (Set.range (ascEigenvalues T)) - sInf (Set.range (ascEigenvalues T))

/-- PDF pp.8,36: the trace-norm mean-centered charge spread, with factor 1/(2d). -/
def meanSpread {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  traceNorm (T - (T.trace / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) / (2 * d)

/-- PDF p.8: lift one local observable, with identity on every other site. -/
def liftLocal {n : ℕ} {dims : Fin n → ℕ} (i : Fin n)
    (T : Matrix (Fin (dims i)) (Fin (dims i)) ℂ) : Matrix (TensorBasis dims) (TensorBasis dims) ℂ :=
  fun y z => T (y i) (z i) * ∏ j ∈ Finset.univ.erase i, if y j = z j then 1 else 0

/-- PDF pp.7–8, (21): exact charge covariance, including the allowed scalar offset. -/
def ChargeCovariant {d n : ℕ} (c : CovariantErasureCodeData d n) (TL : Matrix (Fin d) (Fin d) ℂ)
    (Ti : (i : Fin n) → Matrix (Fin (c.dims i)) (Fin (c.dims i)) ℂ) : Prop :=
  TL.IsHermitian ∧ (∀ i, (Ti i).IsHermitian) ∧ ∃ nu : ℝ,
    (∑ i, liftLocal i (Ti i)) * c.V = c.V * (TL - (nu : ℂ) • 1)

/-- PDF pp.8,15: tensor product of local physical operators. -/
def localTensorProduct {n : ℕ} {dims : Fin n → ℕ}
    (U : (i : Fin n) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ) :
    Matrix (TensorBasis dims) (TensorBasis dims) ℂ := fun y z => ∏ i, U i (y i) (z i)

/-- PDF p.53: pointwise transversality; no continuity of individual factor choices is asserted. -/
def Transversal {n : ℕ} {dims : Fin n → ℕ} (U : Matrix (TensorBasis dims) (TensorBasis dims) ℂ) : Prop :=
  ∃ u : (i : Fin n) → Matrix.unitaryGroup (Fin (dims i)) ℂ,
    U = localTensorProduct (fun i => (u i : Matrix _ _ ℂ))

/-- PDF pp.14,56: continuous transversal representations of SU(d), defining logical action. -/
def SUCovariant {d n : ℕ} (c : CovariantErasureCodeData d n) : Prop :=
  ∃ r : (i : Fin n) → Matrix.specialUnitaryGroup (Fin d) ℂ →*
      Matrix.unitaryGroup (Fin (c.dims i)) ℂ,
    (∀ i, Continuous (r i)) ∧ ∀ U,
      localTensorProduct (fun i => (r i U : Matrix _ _ ℂ)) * c.V =
        c.V * (U : Matrix (Fin d) (Fin d) ℂ)

/-- PDF p.15, (53): actual continuous local U(d) representations implementing the logical U. -/
structure FullAction {d n : ℕ} (c : CovariantErasureCodeData d n) where
  localRep : (i : Fin n) → Matrix.unitaryGroup (Fin d) ℂ →*
    Matrix.unitaryGroup (Fin (c.dims i)) ℂ
  continuous : ∀ i, Continuous (localRep i)
  intertwines : ∀ U, localTensorProduct (fun i => (localRep i U : Matrix _ _ ℂ)) * c.V =
    c.V * (U : Matrix (Fin d) (Fin d) ℂ)

/-- PDF pp.14–16: largest local dimension; never the total physical dimension. -/
def CovariantErasureCodeData.maxDim {d n : ℕ} (c : CovariantErasureCodeData d n) : ℕ := finiteMax c.sitesPositive c.dims

/-- PDF p.14: max_i ln(di), equivalently ln(max_i di) since all di are positive. -/
def CovariantErasureCodeData.logDim {d n : ℕ} (c : CovariantErasureCodeData d n) : ℝ := Real.log (c.maxDim : ℝ)

/-- PDF p.7, (17): the source's negative-sign one-parameter unitary action. -/
def chargeEvolution {I : Type*} [Fintype I] [DecidableEq I]
    (T : Matrix I I ℂ) (theta : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-Complex.I * (theta : ℂ)) • T)

/-- PDF pp.5,68: root fidelity on general Hilbert-space density operators.
The accepted trace-class model supplies the basis trace. On positive trace-class
inputs the square-root sandwich has trace-class square root, so this series is
absolutely summable; a finite-dimensional cutoff is not imposed. -/
def hilbertRootFidelity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {I : Type*} (basis : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) : ℝ :=
  let S := cfc Real.sqrt rho
  (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace basis
    (cfc Real.sqrt (S.comp (sigma.comp S)))).re

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {I : Type*} (basis : HilbertBasis I ℂ H) :
    hilbertRootFidelity basis 0 0 = 0 := by
  simp [hilbertRootFidelity,
    QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace, cfc_zero]

/-- PDF pp.12,41: the same Gaussian normalization c_w as (39),(D.13). -/
def gaussianNormalization (w : ℝ) : ℝ := ∑' y : ℤ, Real.exp (-((y : ℝ) ^ 2) / (2 * w ^ 2))

/-- PDF p.46: DLMF nome convention theta3(i*b,q); every summand is real for imaginary z. -/
def theta3Imaginary (b q : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp ((k : ℝ) ^ 2 * Real.log q - 2 * k * b)

/-- PDF p.46: theta2(0,q) in the source's nome convention. -/
def theta2Zero (q : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (((k : ℝ) + 1 / 2) ^ 2 * Real.log q)

/-- PDF p.55, (E.8): finite-row adapter to the accepted Weyl dimension formula.
The zero extension outside d is never read by the product. -/
def normalizedWeylDimension {d : ℕ} (lambda : Fin d → ℕ) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P65.weylDimension
    (fun a => if ha : a < d then lambda ⟨a, ha⟩ else 0) d

/-- PDF p.55: nonnegative rows of the accepted symmetric highest weight.
Int.toNat is lossless because every entry of this weight is nonnegative. -/
def symmetricRows (d l : ℕ) : Fin d → ℕ :=
  fun i => (symmetricWeight d l i).toNat

/-- PDF p.49, (D.60): number of up-spins at magnetization m (used only at admissible parity). -/
def upSpins (N : ℕ) (m : ℤ) : ℕ := (((N : ℤ) + m) / 2).toNat

/-- PDF p.49, (D.60): hypergeometric weights in the common d-spin Dicke eigenbasis.
The explicit k<=upSpins branch prevents truncated subtraction from inventing a binomial term. -/
def dickeMarginalWeight (N d : ℕ) (m : ℤ) (k : Fin (d + 1)) : ℝ :=
  if k.val ≤ upSpins N m then
    (Nat.choose d k.val : ℝ) * Nat.choose (N - d) (upSpins N m - k.val) /
      Nat.choose N (upSpins N m) else 0

/-- PDF p.49, (D.61): root fidelity of the actual commuting magnetization marginals. -/
def dickeMarginalRootFidelity (N d : ℕ) (m : ℤ) : ℝ :=
  ∑ k : Fin (d + 1), Real.sqrt (dickeMarginalWeight N d m k * dickeMarginalWeight N d 0 k)

/-- Sanity examples pin normalization, flag coherences, boundary indexing, and dimensions.
They are local definition checks, not proofs of the paper's theorems. -/
example : bell (Fin 1) (0, 0) = 1 := by simp [bell]

example (d : ℕ) (i : Fin d) : bell (Fin d) (i, i) = ((Real.sqrt (d : ℝ))⁻¹ : ℂ) := by
  simp [bell]

example {K A B : Type*} [Fintype K] (q : K → ℝ) (C : K → Superop A B)
    (X : Matrix A A ℂ) (k : K) (b b' : B) :
    locationFlaggedChannel q C X (k, b) (k, b') = (q k : ℂ) * C k X b b' := by simp [locationFlaggedChannel]

example {n : ℕ} {dims : Fin n → ℕ} (y : TensorBasis dims)
    (a : (i : (∅ : Finset (Fin n))) → Fin (dims i)) : splice ∅ y a = y := by
  funext i
  simp [splice]

example {I : Type*} [Fintype I] [DecidableEq I] (T : Matrix I I ℂ) :
    chargeEvolution T 0 = 1 := by simp [chargeEvolution]

example : normalizedWeylDimension (symmetricRows 2 1) = 2 := by
  norm_num [normalizedWeylDimension,
    QAlgorithms.Papers.Independent.Information100.P65.weylDimension,
    symmetricRows, symmetricWeight, Finset.prod_range_succ]

example (N d : ℕ) (m : ℤ) (k : Fin (d + 1)) (hk : upSpins N m < k.val) :
    dickeMarginalWeight N d m k = 0 := by simp [dickeMarginalWeight, Nat.not_le.mpr hk]

/-- PDF pp.17–19: matrix of a computational-basis map, with output index first.
The definition accepts any function; the group actions used below are bijective. -/
def basisMapMatrix {I : Type*} (f : I → I) : Matrix I I ℂ :=
  fun y x => if y = f x then 1 else 0

/-- PDF p.6, (11b): uniform-coordinate erasure with an arbitrary fixed basis reset. -/
def uniformErase {J A : Type*} [Fintype J] [Fintype A] (S : Finset J) (reset : J → A) :
    Superop (J → A) (J → A) :=
  fun X y z => if (∀ i ∈ S, y i = reset i ∧ z i = reset i) then
    ∑ a : S → A,
      X (fun i => if hi : i ∈ S then a ⟨i, hi⟩ else y i)
        (fun i => if hi : i ∈ S then a ⟨i, hi⟩ else z i) else 0

/-- PDF pp.17–19: erase a subset of uniformly G-labelled sites, resetting them to |1>. -/
def groupErase {J G : Type*} [Fintype J] [Fintype G] [Group G] (S : Finset J) :
    Superop (J → G) (J → G) :=
  fun X y z => if (∀ i ∈ S, y i = 1 ∧ z i = 1) then
    ∑ a : S → G,
      X (fun i => if hi : i ∈ S then a ⟨i, hi⟩ else y i)
        (fun i => if hi : i ∈ S then a ⟨i, hi⟩ else z i) else 0

/-- PDF p.18: exact correctability is existence of one CPTP recovery acting on every operator.
The recovery is chosen before the input; no performance predicate is assumed as a hypothesis. -/
def CorrectsGroupErasure {J G L : Type*} [Fintype J] [Fintype G] [Group G]
    [Fintype L] [DecidableEq L] (V : Matrix (J → G) L ℂ) (S : Finset J) : Prop :=
  ∃ R : Superop (J → G) L, IsChannel R ∧ ∀ X, R (groupErase S (conjSuperop V X)) = X

/-- PDF p.18: normalized finite-group orbit sum. The displayed constructions make g
recoverable from their first output coordinate, so there are |G| distinct terms. -/
def orbitEncoding {G L J : Type*} [Fintype G] [Fintype J]
    (word : G → L → J → G) : Matrix (J → G) L ℂ :=
  fun y x => ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) *
    ∑ g : G, if y = word g x then 1 else 0

/-- PDF p.18, (65): preserve the order of all four noncommutative group products. -/
def groupFourEncoding (G : Type*) [Group G] [Fintype G] : Matrix (Fin 4 → G) (G × G) ℂ :=
  orbitEncoding (fun g x => ![g, g⁻¹ * x.1, g * x.2, g⁻¹ * x.1 * x.2])

/-- PDF p.18, (67): the distinct stabilized four-site code. -/
def stabilizedFourEncoding (G : Type*) [Group G] [Fintype G] :
    Matrix (Fin 4 → G) (G × G) ℂ :=
  orbitEncoding (fun g x => ![g, g * x.1, g * x.2 * x.1, g * x.2])

/-- PDF pp.18–19: total indexing helper for the alternating even-length word.
The default is used only outside the logical index interval, at the separately handled endpoints. -/
def groupAt {G : Type*} [Group G] {k : ℕ} (x : Fin k → G) (j : ℕ) : G :=
  if h : j < k then x ⟨j, h⟩ else 1

/-- PDF pp.18–19, (68): the general word, with (68) its m=4 example.
m=k+2, so endpoints and the nontrivial logical system are present.
The second coordinate is handled separately to avoid truncated 1-2 subtraction. -/
def evenWord {G : Type*} [Group G] (k : ℕ) (x : Fin (2 * (k + 2) - 2) → G) :
    Fin (2 * (k + 2)) → G :=
  fun j => if j.val = 0 then 1 else if j.val = 2 * (k + 2) - 1 then
    groupAt x (2 * (k + 2) - 3) else if j.val = 1 then groupAt x 0 else if j.val % 2 = 0 then
    groupAt x (j.val - 1) * groupAt x (j.val - 2) else
    groupAt x (j.val - 2) * groupAt x (j.val - 1)

/-- PDF pp.18–19: normalized collective-left orbit of the alternating word. -/
def evenEncoding (G : Type*) [Group G] [Fintype G] (k : ℕ) :
    Matrix (Fin (2 * (k + 2)) → G) (Fin (2 * (k + 2) - 2) → G) ℂ :=
  orbitEncoding (fun g x j => g * evenWord k x j)

/-- PDF p.19, (69): right multipliers on adjacent pairs of physical sites. -/
def evenPhysical {G : Type*} [Group G] (k : ℕ) (r : Fin (k + 1) → G)
    (y : Fin (2 * (k + 2)) → G) : Fin (2 * (k + 2)) → G :=
  fun j => if hj : 0 < j.val ∧ j.val < 2 * (k + 2) - 1 then
    y j * (r ⟨(j.val - 1) / 2, by omega⟩)⁻¹ else y j

/-- PDF p.19, (70): the independent odd-numbered logical right multipliers. -/
def evenLogical {G : Type*} [Group G] (k : ℕ) (r : Fin (k + 1) → G)
    (x : Fin (2 * (k + 2) - 2) → G) : Fin (2 * (k + 2) - 2) → G :=
  fun j => if j.val % 2 = 0 then x j * (r ⟨j.val / 2, by omega⟩)⁻¹ else x j

/-- PDF p.17, (60a): the three-site bit code. -/
def bitEncoding (G : Type*) [Group G] : Matrix (Fin 3 → G) G ℂ :=
  fun y g => if ∀ i, y i = g then 1 else 0

/-- PDF p.17, (60b): the three-site phase code, with ordered group product. -/
def groupPhaseEncoding (G : Type*) [Group G] [Fintype G] : Matrix (Fin 3 → G) G ℂ :=
  fun y g => if y 0 * y 1 * y 2 = g then ((Fintype.card G : ℂ)⁻¹) else 0

/-- PDF p.17: one local left shift, including the identity error. -/
def shiftError {G : Type*} [Group G] (i : Fin 3) (g : G) : Matrix (Fin 3 → G) (Fin 3 → G) ℂ :=
  basisMapMatrix (fun y => Function.update y i (g * y i))

/-- PDF p.17: arbitrary diagonal error on the specified site. -/
def diagonalError {G : Type*} (i : Fin 3) (f : G → ℂ) : Matrix (Fin 3 → G) (Fin 3 → G) ℂ :=
  Matrix.diagonal (fun y => f (y i))

/-- PDF pp.17–18: exact Knill–Laflamme criterion for the span of a specified error family. -/
def CorrectsOperators {A L K : Type*} [Fintype A] [Fintype L] [DecidableEq L]
    (V : Matrix A L ℂ) (E : K → Matrix A A ℂ) : Prop :=
  ∀ e f, ∃ z : ℂ, Vᴴ * (E e)ᴴ * E f * V = z • 1

/-- PDF p.18: concatenate m-fold phase encoding with an m-fold bit encoding of each factor.
The first member k=0 is the one-site identity code. -/
def baconShorEncoding (G : Type*) [Group G] [Fintype G] (k : ℕ) :
    Matrix ((Fin (k + 1) × Fin (k + 1)) → G) G ℂ :=
  fun y g => if (∀ i j, y (i, j) = y (i, 0)) ∧
      (List.ofFn (fun i : Fin (k + 1) => y (i, 0))).prod = g then
    ((Real.sqrt ((Fintype.card G : ℝ) ^ k))⁻¹ : ℂ) else 0

/-- PDF p.19, (72): the finite cyclic candidate, normalized for every positive modulus. -/
def cyclicEncoding (N : ℕ) [NeZero N] : Matrix (Fin 3 → ZMod N) (ZMod N) ℂ :=
  orbitEncoding (fun h g => ![h, g - h, g - 2 * h])

/-- PDF p.16, (55): normalized W-code isometry, vacancy labelled d in each local Fin(d+1). -/
def wEncoding (d n : ℕ) : Matrix (Fin n → Fin (d + 1)) (Fin d) ℂ :=
  fun y x => ((Real.sqrt (n : ℝ))⁻¹ : ℂ) *
    ∑ i : Fin n, ∏ j : Fin n,
      if j = i then (if (y j).val = x.val then 1 else 0)
      else (if (y j).val = d then 1 else 0)

/-- PDF p.11: finite interval embeddings containing the complete support of (36),
including the x-dependent second and third coordinate ranges. -/
def sharpDims (h m : ℕ) : Fin 3 → ℕ := ![6 * m + 1, 2 * (m + h) + 1, 4 * (m + h) + 1]

/-- PDF p.11, (36): the sharp code, without discarding any amplitude outside [-m,m]
in the second and third physical coordinates. -/
def sharpEncoding (h m : ℕ) : Matrix (TensorBasis (sharpDims h m)) (Fin (2 * h + 1)) ℂ :=
  fun y x =>
    let a : Fin 3 → ℤ := fun i => ((y i).val : ℤ) -
      (![3 * m, m + h, 2 * (m + h)] i : ℕ)
    let logical : ℤ := (x.val : ℤ) - h
    if ∃ t : ℤ, -(m : ℤ) ≤ t ∧ t ≤ m ∧
      a 0 = -3 * t ∧ a 1 = t - logical ∧ a 2 = 2 * (t + logical) then
      ((Real.sqrt (2 * (m : ℝ) + 1))⁻¹ : ℂ) else 0

example {G : Type*} [Group G] (x : G × G) :
    (![1, x.1, x.2 * x.1, x.2] : Fin 4 → G) 2 = x.2 * x.1 := rfl

example {G : Type*} [Group G] (x : Fin 6 → G) :
    evenWord 2 x = ![1, x 0, x 1 * x 0, x 1 * x 2, x 3 * x 2,
      x 3 * x 4, x 5 * x 4, x 5] := by
  funext i
  fin_cases i <;> simp [evenWord, groupAt]

example (d : ℕ) (y : Fin 1 → Fin (d + 1)) (x : Fin d) :
    wEncoding d 1 y x = if (y 0).val = x.val then 1 else 0 := by
  simp [wEncoding]

/-- PDF pp.12,18,23: exact recovery of a uniform-coordinate erased set, with fixed reset. -/
def CorrectsUniformErasure {J A L : Type*} [Fintype J] [Fintype A]
    [Fintype L] [DecidableEq L] (V : Matrix (J → A) L ℂ) (reset : J → A) (S : Finset J) : Prop :=
  ∃ R : Superop (J → A) L, IsChannel R ∧
    ∀ X, R (uniformErase S reset (conjSuperop V X)) = X

/-- PDF p.12, (42),(43): normalized cyclic five-qudit tensor; phases are evaluated modulo D. -/
def fiveQuditEncoding (D : ℕ) [NeZero D] (omega : ℂ) :
    Matrix (Fin 5 → ZMod D) (ZMod D) ℂ :=
  fun y x => if (∑ i, y i) = x then
    ((D : ℂ) ^ 2)⁻¹ * omega ^ (∑ i : Fin 5, y i * y ⟨(i.val + 1) % 5, by omega⟩).val
    else 0

/-- PDF p.12: natural integer charge on one qudit, distinguished from its value modulo D. -/
def quditCharge (D : ℕ) [NeZero D] : Matrix (ZMod D) (ZMod D) ℂ :=
  Matrix.diagonal (fun x => (x.val : ℂ))

/-- PDF p.23: standard [[4,2,2]] basis, ordered so XXII flips the first logical bit. -/
def twoLocalEncoding : Matrix (Fin 4 → Bool) (Bool × Bool) ℂ :=
  fun y x =>
    let word : Fin 4 → Bool := ![false, x.2, x.1, xor x.1 x.2]
    if y = word ∨ y = (fun i => !(word i)) then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.23: Q=X tensor X tensor I tensor I, supported on the first two physical qubits. -/
def twoLocalQ : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℂ :=
  basisMapMatrix (fun y => ![!(y 0), !(y 1), y 2, y 3])

/-- PDF p.23: the nontrivial first-logical-qubit Pauli X. -/
def firstLogicalX : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  basisMapMatrix (fun x => (!x.1, x.2))

example : twoLocalQ (![true, true, false, false]) (![false, false, false, false]) = 1 := by
  simp [twoLocalQ, basisMapMatrix]

example (D : ℕ) [NeZero D] (omega : ℂ) (y : Fin 5 → ZMod D) (x : ZMod D)
    (h : (∑ i, y i) ≠ x) : fiveQuditEncoding D omega y x = 0 := by
  simp [fiveQuditEncoding, h]

/-- PDF p.56: the specified Cartan generator diag(1,0,...,0,-1) on tensor space.
It is the sum of the one-cell generators, with the inherited Hilbert inner product. -/
def tensorCartan (d n : ℕ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.diagonal (fun w =>
    ((Finset.univ.filter (fun i => (w i).val = 0)).card : ℂ) -
    ((Finset.univ.filter (fun i => (w i).val = d - 1)).card : ℂ))

/-- PDF p.56: actual generator on the constructed Schur module. Restriction is expressed
using orthogonal projection, as in the accepted polynomial representation; tensorCartan
preserves the Young-symmetrizer image. Its norm is the Hilbert operator norm. -/
def schurCartan {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) :
    QAlgorithms.Schur.schurModule lambda →L[ℂ] QAlgorithms.Schur.schurModule lambda :=
  (QAlgorithms.Schur.schurModule lambda).orthogonalProjectionOnto.comp
    ((Matrix.toEuclideanCLM (n := Fin n → Fin d) (𝕜 := ℂ) (tensorCartan d n)).comp
      (QAlgorithms.Schur.schurModule lambda).subtypeL)

example (d : ℕ) : tensorCartan d 0 = 0 := by
  ext y x
  simp [tensorCartan]

end QAlgorithms.Papers.Independent.Extend50.P22


