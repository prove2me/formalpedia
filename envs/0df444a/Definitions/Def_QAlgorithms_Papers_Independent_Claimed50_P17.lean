-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17
-- name    : QAlgorithms_Papers_Independent_Claimed50_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:50:40.168536+00:00
-- url     : https://prove2.me/theorems/e4a178e8-f38f-426b-9cba-524dd9c89e20
-- title:
--   Definitions for Cloning of a quantum measurement
-- statement:
--   The objects the formalized statements of *Cloning of a quantum measurement* (arXiv:1103.5709) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AB`
--   - `ABC`
--   - `ABCD`
--   - `ReplicationChoiArray`
--   - `DiagonalInstrument`
--   - `measurementEffect`: PDF p.2, Eq.(7): labeled rank-one effect in the fixed basis.
--   - `classicalMeasurementAction`: PDF p.3, Eq.(16): measurement followed only by a classical basis label.
--   - `classicalOutputChoi`: PDF p.3, Eq.(17): D,C Choi matrix; the effect on C is transposed.
--   - `povmFidelity`: PDF p.2, Eq.(3): real trace overlap of two labeled POVMs.
--   - `IsRankOnePVM`: PDF p.2, proof of Lemma 1: von Neumann means a full rank-one basis PVM.
--   - `cloningTotal`: PDF pp.3-4, Eq.(18): S_ABC tensored with identity on D, in ABC,D order.
--   - `learningTotal`: PDF pp.3-4, Eq.(19): identity on A,B,D and density operator on C.
--   - `Timing`
--   - `IsReplicationStrategy`: PDF pp.3-4, Eqs.(18)-(19): full one-use operational domain, without symmetry restrictions. The instrument is chosen independently of the oracle orientation.
--   - `replica`: PDF p.4, Eq.(20): exactly one insertion of the measurement channel. The final AB transpose is the reversal of x and y in the instrument entries.
--   - `scoreIntegrand`: PDF p.2, Eq.(8): pointwise fidelity, averaged below over orientations.
--   - `haarReplicationScore`: PDF p.2, Eq.(8): normalized Haar score, rather than a worst-case success law. The integrand is a finite polynomial in the entries of U and their conjugates, hence continuous and integrable on the compact unitary group.
--   - `scoreValues`: PDF pp.2,7,9: operational score values, with feasibility retained.
--   - `diagonalBlocks`: PDF p.4, Eq.(23): diagonal blocks on the classical D wire.
--   - `liftDiagonal`: PDF p.4, Eq.(22): insert classical blocks in ABC,D order.
--   - `dephaseClassicalOutput`: PDF p.4, Eq.(23): dephasing on D, an explicit transport of instruments.
--   - `learningToCloning`: PDF p.2: the inclusion of learning instruments into cloning uses the same Choi array.
--   - `representation`: PDF p.4, Eq.(28): representation on the specifically named A,B,C factors.
--   - `BlocksCommuteWithRotations`: PDF p.4, Eq.(28): invariance is conjugate(U)_A tensor conjugate(U)_B tensor U_C.
--   - `twirlBlocks`: PDF p.4, Eq.(29): a genuine finite-dimensional continuous Haar integral.
--   - `twirl`: PDF pp.4-5: constructive dephasing followed by twirling.
--   - `RelabelInvariant`: PDF p.5, Eq.(31): simultaneous relabeling of all three classical indices.
--   - `relabelBlocks`: PDF p.5, second equality in Eq.(32), used only after covariance.
--   - `relabel`: PDF p.5: relabel transport on an already diagonal covariant instrument.
--   - `pairAction`: PDF p.5, Eq.(34): simultaneous basis rotation of A and B.
--   - `exchange`: PDF p.6, Eq.(43): A/B exchange, with C and D fixed.
--   - `symmetrize`: PDF p.6, Lemma 5: operational equal mixture of an instrument and its exchange.
--   - `outcomeClass`: PDF p.5, Eq.(35): xxx,xxy,xyx,xyy,xyz are respectively 0,1,2,3,4.
--   - `classWeight`: PDF p.6, Eq.(47): class multiplicity divided by d.
--   - `alphaEmbedding`: PDF pp.5-6, Eqs.(40),(42): the two actual representation embeddings. The minus copy uses (sum_a |a,m,a> - sum_a |m,a,a>)/sqrt(2(d-1)).
--   - `pairProjector`: PDF p.6: projectors P^+ and P^- on A,B, tensored with I_C.
--   - `residualProjector`: PDF p.6, Eq.(42), with the tensor order corrected to P_AB tensor I_C.
--   - `BlockArray`
--   - `coordinateProjector`: PDF p.6, Eq.(54): the two supported one-dimensional multiplicity projections.
--   - `BlockShape`: PDF pp.5-7: actual sector and class support, including absent gamma and xyz at d=2. Beta and gamma are supported diagonal 2 by 2 matrices, not free 2 by 2 blocks.
--   - `blockOperator`: PDF pp.5-6, Eqs.(38)-(42): actual Schur operator from multiplicity coefficients.
--   - `expandBlocks`: PDF p.6, Eq.(47): recover r from s=n r/d, then expand the classical D blocks.
--   - `sectorScore`: PDF p.6, Eqs.(45)-(46): score computed by the actual basis contractions. No use is made of the defective numerical Delta table (48).
--   - `replicationSectorDimension`: PDF p.6: dimensions d_alpha, d_beta and d_gamma; gamma has dimension zero at d=2.
--   - `pairDimension`: PDF pp.6-7: dimensions of symmetric and antisymmetric A,B spaces.
--   - `cloningBlockSet`: PDF p.7, Eq.(55): the unswapped cloning block set, not an assumed operational domain.
--   - `IsPerturbation`: PDF p.7, Definition 1: corrected positive two-sided radius, not the printed epsilon>=0.
--   - `blockSupport`: PDF p.7, Lemma 7: count nonzero sector/class blocks, not coefficients or eigenvalues.
--   - `learningBlockSet`: PDF p.9, Eq.(71): learning normalization, with absent gamma at d=2.
--   - `learningBlocks`: PDF p.9, Eqs.(73),(76): the learning block family, including its swap partner. The missing alpha_xy,y in (76) is supplied by the already stated Eq.(44).
--   - `learningParameter`: PDF p.9, Eq.(77): maximizing scalar parameter.
--   - `learningAlphaBound`: PDF p.9, Eq.(75), divided by d to give F_alpha itself.
--   - `learningValue`: PDF p.9, Eq.(78) and the following exceptional d=2 value.
--   - `controlVector`: PDF p.8: the normalized computational control vectors |+> and |->.
--   - `controlEffectVector`: PDF p.8, Eq.(66): subnormalized effect vectors, not input states. Source basis correction: printed P3=sigma_z |psi><psi| sigma_z is read with Z_pm=|+><+|-|-><-| (Pauli X in the computational basis), explicitly reflected in the minus sign below. Computational Pauli Z would not normalize the POVM; Eqs.(64),(69) require this (+,-)-basis reflection. All coefficients are retained.
--   - `controlPOVM`: PDF p.8, Eq.(66): all three control effects, with the explicit Z_pm reflection documented in controlEffectVector in place of the ambiguous sigma_z.
--   - `postprocess`: PDF p.8, Eq.(67): stochastic postprocessing; the other label is uniform.
--   - `postprocessPOVM`: PDF p.8, Eq.(68): Q on the classical D wire and the control L.
--   - `controlledSwap`: PDF p.8, Eq.(65): full controlled SWAP, from A,B,L to C,K,L.
--   - `preparedSwap`: PDF p.8: compose the actual controlled SWAP with the prepared |+> control.
--   - `networkInstrument`: PDF p.8, Eq.(69): evaluate the Choi link of preparation, controlled SWAP, Q on D,L, and the trace over K. This is a coordinate contraction, not a placeholder.
--   - `printedPhi`: PDF p.8, Eq.(64): phi with the printed coefficients, including their square roots.
--   - `printedInstrument`: PDF p.8, Eq.(64): the printed instrument itself; no optimality is asserted.
--   - `learningReplicaFilter`: PDF p.9, after Eq.(78): Q-prime-plus and Q-prime-minus in the replica formula.
--   - `learningReplicaFormula`: PDF p.9, after Eq.(78): complete printed optimal-learning replica formula. Its domain is d>=3; the d-2 denominators are not interpreted at d=2. The plan's proposed d=3 counterexample had a mistaken diagonal overlap: the printed value is 25/54, giving the correct total haarReplicationScore 7/27, not 11/54.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, https://arxiv.org/abs/1103.5709v2

import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Measurement replication, arXiv:1103.5709v2. Wire order is ((A,B),C),D throughout.
All Choi operators use the unnormalized maximally entangled vector. The oracle has
only its classical D output; no postmeasurement quantum output is included.

We integrate over the accepted normalized Haar law on U(d). This is exactly the
paper's SU(d) measurement law: central scalar phases cancel in E_i, in the replica
contraction, and in conjugation by conjugate(U) tensor conjugate(U) tensor U.
Every U(d) matrix has a scalar multiple in SU(d), and the two Haar measures induce
the same normalized invariant measure on the space of labeled basis measurements.
No additional operational strategies or oracle access are introduced by this choice.

The three deferred source claims listed in HARD.md are deliberately not asserted.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

-- Reuse the pinned operator abbreviation and fixed-basis permutation convention.
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

abbrev AB (d : ℕ) := Fin d × Fin d

abbrev ABC (d : ℕ) := AB d × Fin d

abbrev ABCD (d : ℕ) := ABC d × Fin d

abbrev ReplicationChoiArray (d : ℕ) := Fin d → Fin d → Op (ABCD d)

abbrev DiagonalInstrument (d : ℕ) := Fin d → Fin d → Fin d → Op (ABC d)

/-- PDF p.2, Eq.(7): labeled rank-one effect in the fixed basis. -/
def measurementEffect {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i : Fin d) : Op (Fin d) :=
  fun a b => (U : Op (Fin d)) a i * conj ((U : Op (Fin d)) b i)

/-- PDF p.3, Eq.(16): measurement followed only by a classical basis label. -/
def classicalMeasurementAction {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) (X : Op (Fin d)) : Op (Fin d) :=
  Matrix.diagonal (fun i => Matrix.trace (measurementEffect U i * X))

/-- PDF p.3, Eq.(17): D,C Choi matrix; the effect on C is transposed. -/
def classicalOutputChoi {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Op (Fin d × Fin d) :=
  fun x y => QAlgorithms.Papers.Independent.Information100.P34.choi
    (classicalMeasurementAction U) (x.2,x.1) (y.2,y.1)

/-- PDF p.2, Eq.(3): real trace overlap of two labeled POVMs. -/
def povmFidelity {d : ℕ} (P Q : Fin d → Op (Fin d)) : ℝ :=
  (1 / (d : ℝ)) * ∑ i, (Matrix.trace (P i * Q i)).re

/-- PDF p.2, proof of Lemma 1: von Neumann means a full rank-one basis PVM. -/
def IsRankOnePVM {d : ℕ} (P : Fin d → Op (Fin d)) : Prop :=
  ∃ U : (Matrix.unitaryGroup (Fin d) ℂ), P = measurementEffect U

/-- PDF pp.3-4, Eq.(18): S_ABC tensored with identity on D, in ABC,D order. -/
def cloningTotal {d : ℕ} (S : Op (ABC d)) : Op (ABCD d) :=
  Matrix.kronecker S 1

/-- PDF pp.3-4, Eq.(19): identity on A,B,D and density operator on C. -/
def learningTotal {d : ℕ} (rho : Op (Fin d)) : Op (ABCD d) :=
  fun x y => if x.1.1 = y.1.1 ∧ x.2 = y.2 then rho x.1.2 y.1.2 else 0

inductive Timing where
  | cloning
  | learning
  deriving DecidableEq

/-- PDF pp.3-4, Eqs.(18)-(19): full one-use operational domain, without symmetry
restrictions. The instrument is chosen independently of the oracle orientation. -/
def IsReplicationStrategy {d : ℕ} (timing : Timing) (R : ReplicationChoiArray d) : Prop :=
  (∀ i j, (R i j).PosSemidef) ∧
  match timing with
  | .cloning => ∃ S : Op (ABC d), S.PosSemidef ∧ traceRight S = 1 ∧
      (∑ i, ∑ j, R i j) = cloningTotal S
  | .learning => ∃ rho : Op (Fin d), rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
      (∑ i, ∑ j, R i j) = learningTotal rho

/-- PDF p.4, Eq.(20): exactly one insertion of the measurement channel.
The final AB transpose is the reversal of x and y in the instrument entries. -/
def replica {d : ℕ} (R : ReplicationChoiArray d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i j : Fin d) : Op (AB d) :=
  fun x y => ∑ k, ∑ c, ∑ e,
    conj ((U : Op (Fin d)) c k) * R i j ((y,c),k) ((x,e),k) *
      (U : Op (Fin d)) e k

/-- PDF p.2, Eq.(8): pointwise fidelity, averaged below over orientations. -/
def scoreIntegrand {d : ℕ} (R : ReplicationChoiArray d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) : ℝ :=
  (1 / (d : ℝ)^2) * ∑ i, ∑ j,
    (Matrix.trace (replica R U i j *
      Matrix.kronecker (measurementEffect U i) (measurementEffect U j))).re

/-- PDF p.2, Eq.(8): normalized Haar score, rather than a worst-case success law.
The integrand is a finite polynomial in the entries of U and their conjugates,
hence continuous and integrable on the compact unitary group. -/
def haarReplicationScore {d : ℕ} (R : ReplicationChoiArray d) : ℝ :=
  ∫ U, scoreIntegrand R U ∂QAlgorithms.Schur.unitaryHaar d

/-- PDF pp.2,7,9: operational score values, with feasibility retained. -/
def scoreValues (d : ℕ) (timing : Timing) : Set ℝ :=
  {v | ∃ R : ReplicationChoiArray d, IsReplicationStrategy timing R ∧ haarReplicationScore R = v}

/-- PDF p.4, Eq.(23): diagonal blocks on the classical D wire. -/
def diagonalBlocks {d : ℕ} (R : ReplicationChoiArray d) : DiagonalInstrument d :=
  fun i j k x y => R i j (x,k) (y,k)

/-- PDF p.4, Eq.(22): insert classical blocks in ABC,D order. -/
def liftDiagonal {d : ℕ} (B : DiagonalInstrument d) : ReplicationChoiArray d :=
  fun i j x y => if x.2 = y.2 then B i j x.2 x.1 y.1 else 0

/-- PDF p.4, Eq.(23): dephasing on D, an explicit transport of instruments. -/
def dephaseClassicalOutput {d : ℕ} (R : ReplicationChoiArray d) : ReplicationChoiArray d :=
  fun i j => QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput (R i j)

/-- PDF p.2: the inclusion of learning instruments into cloning uses the same Choi array. -/
def learningToCloning {d : ℕ} (R : ReplicationChoiArray d) : ReplicationChoiArray d := R

/-- PDF p.4, Eq.(28): representation on the specifically named A,B,C factors. -/
def representation {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Op (ABC d) :=
  Matrix.kronecker (Matrix.kronecker ((U : Op (Fin d)).map conj)
    ((U : Op (Fin d)).map conj)) (U : Op (Fin d))

/-- PDF p.4, Eq.(28): invariance is conjugate(U)_A tensor conjugate(U)_B tensor U_C. -/
def BlocksCommuteWithRotations {d : ℕ} (B : DiagonalInstrument d) : Prop :=
  ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ i j k,
    B i j k * representation U = representation U * B i j k

/-- PDF p.4, Eq.(29): a genuine finite-dimensional continuous Haar integral. -/
def twirlBlocks {d : ℕ} (B : DiagonalInstrument d) : DiagonalInstrument d :=
  fun i j k => ∫ U, representation U * B i j k * (representation U).conjTranspose
    ∂QAlgorithms.Schur.unitaryHaar d

/-- PDF pp.4-5: constructive dephasing followed by twirling. -/
def twirl {d : ℕ} (R : ReplicationChoiArray d) : ReplicationChoiArray d :=
  liftDiagonal (twirlBlocks (diagonalBlocks R))

/-- PDF p.5, Eq.(31): simultaneous relabeling of all three classical indices. -/
def RelabelInvariant {d : ℕ} (B : DiagonalInstrument d) : Prop :=
  ∀ sigma : Equiv.Perm (Fin d), ∀ i j k, B i j k = B (sigma i) (sigma j) (sigma k)

/-- PDF p.5, second equality in Eq.(32), used only after covariance. -/
def relabelBlocks {d : ℕ} (B : DiagonalInstrument d) : DiagonalInstrument d :=
  fun i j k => ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) •
    ∑ sigma : Equiv.Perm (Fin d), B (sigma i) (sigma j) (sigma k)

/-- PDF p.5: relabel transport on an already diagonal covariant instrument. -/
def relabel {d : ℕ} (R : ReplicationChoiArray d) : ReplicationChoiArray d :=
  liftDiagonal (relabelBlocks (diagonalBlocks R))

/-- PDF p.5, Eq.(34): simultaneous basis rotation of A and B. -/
def pairAction {d : ℕ} (V : Op (Fin d)) : Op (AB d) := Matrix.kronecker V V

/-- PDF p.6, Eq.(43): A/B exchange, with C and D fixed. -/
def exchange {d : ℕ} (R : ReplicationChoiArray d) : ReplicationChoiArray d :=
  fun i j x y => R j i (((x.1.1.2,x.1.1.1),x.1.2),x.2)
    (((y.1.1.2,y.1.1.1),y.1.2),y.2)

/-- PDF p.6, Lemma 5: operational equal mixture of an instrument and its exchange. -/
def symmetrize {d : ℕ} (R : ReplicationChoiArray d) : ReplicationChoiArray d :=
  (1/2 : ℂ) • (R + exchange R)

/-- PDF p.5, Eq.(35): xxx,xxy,xyx,xyy,xyz are respectively 0,1,2,3,4. -/
def outcomeClass {d : ℕ} (i j k : Fin d) : Fin 5 :=
  if i = j then (if j = k then 0 else 1)
  else if i = k then 2 else if j = k then 3 else 4

/-- PDF p.6, Eq.(47): class multiplicity divided by d. -/
def classWeight (d : ℕ) (l : Fin 5) : ℝ :=
  if l = 0 then 1 else if l = 4 then ((d : ℝ)-1)*((d : ℝ)-2) else (d : ℝ)-1

/-- PDF pp.5-6, Eqs.(40),(42): the two actual representation embeddings.
The minus copy uses (sum_a |a,m,a> - sum_a |m,a,a>)/sqrt(2(d-1)). -/
def alphaEmbedding (d : ℕ) (s : Fin 2) : Matrix (ABC d) (Fin d) ℂ :=
  fun x m => (((if x.1.1 = x.2 ∧ x.1.2 = m then 1 else 0) +
    (if s = 0 then 1 else -1) * (if x.1.1 = m ∧ x.1.2 = x.2 then 1 else 0) : ℝ) /
      Real.sqrt (2 * ((d : ℝ) + if s = 0 then 1 else -1)) : ℝ)

/-- PDF p.6: projectors P^+ and P^- on A,B, tensored with I_C. -/
def pairProjector (d : ℕ) (s : Fin 2) : Op (AB d) :=
  fun x y => (1/2 : ℂ) * ((if x = y then 1 else 0) +
    (if s = 0 then 1 else -1) * (if x = (y.2,y.1) then 1 else 0))

/-- PDF p.6, Eq.(42), with the tensor order corrected to P_AB tensor I_C. -/
def residualProjector (d : ℕ) (s : Fin 2) : Op (ABC d) :=
  Matrix.kronecker (pairProjector d s) 1 -
    alphaEmbedding d s * (alphaEmbedding d s).conjTranspose

abbrev BlockArray := Fin 5 → Fin 3 → Op (Fin 2)

/-- PDF p.6, Eq.(54): the two supported one-dimensional multiplicity projections. -/
def coordinateProjector (s : Fin 2) : Op (Fin 2) :=
  fun a b => if a = s ∧ b = s then 1 else 0

/-- PDF pp.5-7: actual sector and class support, including absent gamma and xyz at d=2.
Beta and gamma are supported diagonal 2 by 2 matrices, not free 2 by 2 blocks. -/
def BlockShape (d : ℕ) (b : BlockArray) : Prop :=
  (∀ l v, (b l v).PosSemidef) ∧
  (∀ l, b l 1 = (b l 1 0 0) • coordinateProjector 0) ∧
  (∀ l, b l 2 = (b l 2 1 1) • coordinateProjector 1) ∧
  (d = 2 → (∀ l, b l 2 = 0) ∧ (∀ v, b 4 v = 0))

/-- PDF pp.5-6, Eqs.(38)-(42): actual Schur operator from multiplicity coefficients. -/
def blockOperator (d : ℕ) (b : BlockArray) (l : Fin 5) : Op (ABC d) :=
  (∑ a : Fin 2, ∑ c : Fin 2, (b l 0 a c) •
    (alphaEmbedding d a * (alphaEmbedding d c).conjTranspose)) +
  (b l 1 0 0) • residualProjector d 0 + (b l 2 1 1) • residualProjector d 1

/-- PDF p.6, Eq.(47): recover r from s=n r/d, then expand the classical D blocks. -/
def expandBlocks (d : ℕ) (b : BlockArray) : ReplicationChoiArray d :=
  liftDiagonal (fun i j k => ((classWeight d (outcomeClass i j k) : ℂ)⁻¹) •
    blockOperator d b (outcomeClass i j k))

/-- PDF p.6, Eqs.(45)-(46): score computed by the actual basis contractions.
No use is made of the defective numerical Delta table (48). -/
def sectorScore (d : ℕ) (b : BlockArray) (v : Fin 3) : ℝ :=
  (1/(d : ℝ)^2) * ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
    let l := outcomeClass i j k
    let bv : BlockArray := fun l w => if w = v then b l w else 0
    ((classWeight d l)⁻¹) * (blockOperator d bv l ((i,j),k) ((i,j),k)).re

/-- PDF p.6: dimensions d_alpha, d_beta and d_gamma; gamma has dimension zero at d=2. -/
def replicationSectorDimension (d : ℕ) (v : Fin 3) : ℝ :=
  if v = 0 then d else if v = 1 then
    (d : ℝ)*((d : ℝ)-1)*((d : ℝ)+2)/2
  else (d : ℝ)*((d : ℝ)+1)*((d : ℝ)-2)/2

/-- PDF pp.6-7: dimensions of symmetric and antisymmetric A,B spaces. -/
def pairDimension (d : ℕ) (s : Fin 2) : ℝ :=
  (d : ℝ) * ((d : ℝ) + if s = 0 then 1 else -1) / 2

/-- PDF p.7, Eq.(55): the unswapped cloning block set, not an assumed operational domain. -/
def cloningBlockSet (d : ℕ) : Set BlockArray :=
  {b | BlockShape d b ∧ ∀ s : Fin 2,
    (∑ l : Fin 5, ∑ v : Fin 3, (replicationSectorDimension d v : ℂ) * b l v s s) =
      (pairDimension d s : ℂ)}

/-- PDF p.7, Definition 1: corrected positive two-sided radius, not the printed epsilon>=0. -/
def IsPerturbation (d : ℕ) (b z : BlockArray) : Prop :=
  (∀ l v, (z l v).IsHermitian) ∧
  ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ h : ℝ, h ∈ Set.Icc (-epsilon) epsilon →
    b + h • z ∈ cloningBlockSet d

/-- PDF p.7, Lemma 7: count nonzero sector/class blocks, not coefficients or eigenvalues. -/
def blockSupport (b : BlockArray) : Finset (Fin 5 × Fin 3) :=
  Finset.univ.filter (fun p => b p.1 p.2 ≠ 0)

/-- PDF p.9, Eq.(71): learning normalization, with absent gamma at d=2. -/
def learningBlockSet (d : ℕ) : Set BlockArray :=
  {b | BlockShape d b ∧ (∑ l : Fin 5, b l 0) = ((1/(d : ℝ) : ℝ) : ℂ) • 1 ∧
    (∑ l : Fin 5, b l 1 0 0) = (1/(d : ℝ) : ℂ) ∧
    (∑ l : Fin 5, b l 2 1 1) = (if d = 2 then 0 else (1/(d : ℝ) : ℂ))}

/-- PDF p.9, Eqs.(73),(76): the learning block family, including its swap partner.
The missing alpha_xy,y in (76) is supplied by the already stated Eq.(44). -/
def learningBlocks (d : ℕ) (a : ℝ) : BlockArray :=
  fun l v =>
    if v = 0 then
      if l = 0 then ((1/(d : ℝ)-2*a : ℝ) : ℂ) • coordinateProjector 0
      else if l = 2 ∨ l = 3 then
        let w : Fin 2 → ℂ := fun s => if s = 0 then Real.sqrt a
          else (if l = 2 then 1 else -1 : ℝ) * Real.sqrt (1/(2*(d : ℝ)))
        fun x y => w x * conj (w y)
      else 0
    else if v = 1 ∧ l = 1 then (1/(d : ℝ) : ℂ) • coordinateProjector 0
    else if v = 2 ∧ l = 4 ∧ d ≠ 2 then (1/(d : ℝ) : ℂ) • coordinateProjector 1
    else 0

/-- PDF p.9, Eq.(77): maximizing scalar parameter. -/
def learningParameter (d : ℕ) : ℝ := ((d : ℝ)+1)/(18*(d : ℝ)*((d : ℝ)-1))

/-- PDF p.9, Eq.(75), divided by d to give F_alpha itself. -/
def learningAlphaBound (d : ℕ) (a : ℝ) : ℝ :=
  ((5*(d : ℝ)-3)/(2*(d : ℝ)*((d : ℝ)^2-1)) - 3*a/((d : ℝ)+1) +
    2*Real.sqrt (a/(2*(d : ℝ)*((d : ℝ)^2-1))))/(d : ℝ)

/-- PDF p.9, Eq.(78) and the following exceptional d=2 value. -/
def learningValue (d : ℕ) : ℝ :=
  if d = 2 then 7/12 else
    (9*(d : ℝ)^2+16*(d : ℝ)-17)/(6*(d : ℝ)^2*((d : ℝ)^2-1))

/-- PDF p.8: the normalized computational control vectors |+> and |->. -/
def controlVector (s : Fin 2) : Fin 2 → ℂ :=
  fun a => ((if s = 0 ∨ a = 0 then 1 else -1 : ℝ) / Real.sqrt 2 : ℝ)

/-- PDF p.8, Eq.(66): subnormalized effect vectors, not input states.
Source basis correction: printed P3=sigma_z |psi><psi| sigma_z is read with
Z_pm=|+><+|-|-><-| (Pauli X in the computational basis), explicitly reflected
in the minus sign below. Computational Pauli Z would not normalize the POVM;
Eqs.(64),(69) require this (+,-)-basis reflection. All coefficients are retained. -/
def controlEffectVector (d : ℕ) (s : Fin 2) : Fin 2 → ℂ :=
  fun a => (Real.sqrt (1/(9*(d : ℝ)*((d : ℝ)+1))) : ℂ) * controlVector 0 a +
    (if s = 0 then 1 else -1) * (Real.sqrt (1/2) : ℂ) * controlVector 1 a

/-- PDF p.8, Eq.(66): all three control effects, with the explicit
Z_pm reflection documented in controlEffectVector in place of the ambiguous sigma_z. -/
def controlPOVM (d : ℕ) (n : Fin 3) : Op (Fin 2) :=
  if n = 0 then
    ((9*(d : ℝ)*((d : ℝ)+1)-2)/(9*(d : ℝ)*((d : ℝ)+1)) : ℂ) •
      (fun a b => controlVector 0 a * conj (controlVector 0 b))
  else
    let s : Fin 2 := if n = 1 then 0 else 1
    fun a b => controlEffectVector d s a * conj (controlEffectVector d s b)

/-- PDF p.8, Eq.(67): stochastic postprocessing; the other label is uniform. -/
def postprocess {d : ℕ} (k : Fin d) (n : Fin 3) (i j : Fin d) : ℝ :=
  if n = 0 then (if i = k ∧ j = k then 1 else 0)
  else if n = 1 then (if i = k ∧ j ≠ k then 1/((d : ℝ)-1) else 0)
  else (if j = k ∧ i ≠ k then 1/((d : ℝ)-1) else 0)

/-- PDF p.8, Eq.(68): Q on the classical D wire and the control L. -/
def postprocessPOVM (d : ℕ) (i j : Fin d) : Op (Fin d × Fin 2) :=
  fun x y => if x.1 = y.1 then
    ∑ n : Fin 3, (postprocess x.1 n i j : ℂ) * controlPOVM d n x.2 y.2 else 0

/-- PDF p.8, Eq.(65): full controlled SWAP, from A,B,L to C,K,L. -/
def controlledSwap (d : ℕ) : Op (AB d × Fin 2) :=
  fun x y => if x.2 = y.2 ∧
    (if x.2 = 0 then x.1 = y.1 else x.1 = (y.1.2,y.1.1)) then 1 else 0

/-- PDF p.8: compose the actual controlled SWAP with the prepared |+> control. -/
def preparedSwap (d : ℕ) : Matrix (AB d × Fin 2) (AB d) ℂ :=
  fun x y => ∑ s : Fin 2, controlledSwap d x (y,s) * controlVector 0 s

/-- PDF p.8, Eq.(69): evaluate the Choi link of preparation, controlled SWAP,
Q on D,L, and the trace over K. This is a coordinate contraction, not a placeholder. -/
def networkInstrument (d : ℕ) : ReplicationChoiArray d :=
  fun i j x y => ∑ k : Fin d, ∑ a : Fin 2, ∑ b : Fin 2,
    preparedSwap d ((x.1.2,k),a) x.1.1 *
      conj (preparedSwap d ((y.1.2,k),b) y.1.1) *
      postprocessPOVM d i j (y.2,b) (x.2,a)

/-- PDF p.8, Eq.(64): phi with the printed coefficients, including their square roots. -/
def printedPhi (d : ℕ) (s : Fin 2) : Matrix (ABC d) (Fin d) ℂ :=
  (Real.sqrt (1/(9*(d : ℝ))) : ℂ) • alphaEmbedding d 0 +
    ((if s = 0 then 1 else -1 : ℝ) * Real.sqrt (pairDimension d 1/(d : ℝ)) : ℂ) •
      alphaEmbedding d 1

/-- PDF p.8, Eq.(64): the printed instrument itself; no optimality is asserted. -/
def printedInstrument (d : ℕ) : ReplicationChoiArray d :=
  liftDiagonal (fun i j k =>
    if i = j then
      if k = i then
        ((9*pairDimension d 0-1)/(9*(d : ℝ)) : ℂ) •
          (alphaEmbedding d 0 * (alphaEmbedding d 0).conjTranspose)
      else 0
    else
      (if k = i then (1/(2*((d : ℝ)-1)) : ℂ) •
        (printedPhi d 0 * (printedPhi d 0).conjTranspose) else 0) +
      (if k = j then (1/(2*((d : ℝ)-1)) : ℂ) •
        (printedPhi d 1 * (printedPhi d 1).conjTranspose) else 0))

/-- PDF p.9, after Eq.(78): Q-prime-plus and Q-prime-minus in the replica formula. -/
def learningReplicaFilter (d : ℕ) (s : Fin 2) : Op (AB d) :=
  ((Real.sqrt (9*(d : ℝ)*((d : ℝ)-1)))⁻¹ : ℂ) •
    (pairProjector d 0 + (if s = 0 then 3 else -3 : ℂ) • pairProjector d 1)

/-- PDF p.9, after Eq.(78): complete printed optimal-learning replica formula.
Its domain is d>=3; the d-2 denominators are not interpreted at d=2.
The plan's proposed d=3 counterexample had a mistaken diagonal overlap: the
printed value is 25/54, giving the correct total haarReplicationScore 7/27, not 11/54. -/
def learningReplicaFormula {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i j : Fin d) : Op (AB d) :=
  let Pp := pairProjector d 0
  let Pm := pairProjector d 1
  let Ei := Matrix.kronecker (measurementEffect U i) (1 : Op (Fin d))
  let Ej := Matrix.kronecker (measurementEffect U j) (1 : Op (Fin d))
  if i = j then
    ((16*(d : ℝ)-2)/(9*(d : ℝ)*((d : ℝ)^2-1)) : ℂ) • (Pp * Ei * Pp) +
    (((d : ℝ)^2-3)/((d : ℝ)*((d : ℝ)^2-1)) : ℂ) • Pp
  else
    (1/((d : ℝ)-1) : ℂ) •
      (learningReplicaFilter d 0 * Ei * learningReplicaFilter d 0 +
       learningReplicaFilter d 1 * Ej * learningReplicaFilter d 1) +
    (2/((d : ℝ)*((d : ℝ)-1)^2*((d : ℝ)-2)) : ℂ) • (Pm * (Ei+Ej) * Pm) +
    (((d : ℝ)-3)/(((d : ℝ)-1)^2*((d : ℝ)-2)) : ℂ) • Pm

/-! Small definition sanity checks. These are not proofs of the paper's results. -/

example {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i j c e : Fin d) (h : i ≠ j) :
    classicalOutputChoi U (i,c) (j,e) = 0 := by
  simp [classicalOutputChoi, QAlgorithms.Papers.Independent.Information100.P34.choi,
    classicalMeasurementAction, h]

example {d : ℕ} (R : ReplicationChoiArray d) (i j : Fin d) (x y : ABCD d) (h : x.2 ≠ y.2) :
    dephaseClassicalOutput R i j x y = 0 := by
  simp [dephaseClassicalOutput,
    QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput, h]

example : outcomeClass (0 : Fin 2) 1 0 = 2 := by decide

example : classWeight 2 4 = 0 := by
  norm_num [classWeight, show (4 : Fin 5) ≠ 0 by decide]

example : coordinateProjector 0 (0 : Fin 2) 1 = 0 := by
  simp [coordinateProjector]

example {d : ℕ} (R : ReplicationChoiArray d) : learningToCloning R = R := rfl

example {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i j : Fin d) :
    replica (0 : ReplicationChoiArray d) U i j = 0 := by
  ext x y
  simp [replica]

example {d : ℕ} (R : ReplicationChoiArray d) (h : IsReplicationStrategy .learning R) :
    ∃ r : Op (Fin d), r.PosSemidef ∧ Matrix.trace r = 1 ∧
      (∑ i, ∑ j, R i j) = learningTotal r := h.2

example (d : ℕ) (x : AB d) : controlledSwap d (x,0) (x,0) = 1 := by
  simp [controlledSwap]

example (b : BlockArray) (d : ℕ) (h : BlockShape d b) (hd : d = 2) :
    ∀ l, b l 2 = 0 := (h.2.2.2 hd).1

example {d : ℕ} (k : Fin d) : postprocess k 0 k k = 1 := by
  simp [postprocess]

end QAlgorithms.Papers.Independent.Claimed50.P17


