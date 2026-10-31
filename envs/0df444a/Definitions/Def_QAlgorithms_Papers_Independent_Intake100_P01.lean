-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01
-- name    : QAlgorithms_Papers_Independent_Intake100_P01
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:48:00.365829+00:00
-- url     : https://prove2.me/theorems/2e62a73b-16f7-467e-b9f9-839cad9008d9
-- title:
--   Definitions for Quantum state merging and negative information
-- statement:
--   The objects the formalized statements of *Quantum state merging and negative information* (arXiv:quant-ph/0512247) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `branchRA`: PDF p.5, (6)--(10): the unnormalized RA1 branch, with R a spectator.
--   - `decoupled`: PDF p.5, (10): rho_R tensor tau_L, in reference-first order.
--   - `mergingBranchProbability`: PDF p.5, (7): Born weight of the computed subnormalized RA1 branch.
--   - `mergingDecouplingError`: PDF p.5, (10): homogeneous weighted trace norms. For a positive branch, ||omega-p tau tensor rho_R||_1=p||omega/p-tau tensor rho_R||_1. A zero-weight positive branch is zero, so no division or nonstate occurs.
--   - `completedMap`: PDF p.6, (14), corrected: sum UNNORMALIZED branches, including their weights.
--   - `CompletedMerging`: PDF pp.5--6, (9),(15),(16): Bob's conditional isometries complete the specified measurement; full source/reference and Phi_L are tested jointly. No initial entanglement is supplied, so the cost is -log2 L.
--   - `blockRow`: PDF pp.6,8: N full coordinate blocks, followed by the residual block, embedded in the same L-dimensional output; at d%L=0 the last branch is zero.
--   - `randomBlocks`: PDF p.8: a single Haar unitary rotates all orthogonal blocks.
--   - `oneShotBound`: PDF p.6, (17): the exact one-shot quantum-error bound.
--   - `randomOmega`: PDF p.7: omega for a fixed coisometry P0 followed by Haar U.
--   - `UnassistedMerging`: PDF pp.8--9: no supplied entanglement, complete transferred source and output Bell state, actual LOCC map; eps is the full trace-norm error.
--   - `BitLOCC`: PDF pp.10--11: arbitrary finite adaptive LOCC with a maximum binary transcript budget. Uncommunicated local channels/private Kraus labels cost zero. A public bit costs one in EITHER direction. Padding makes branch maxima equal; it is an upper budget, not a sum over counterfactual branches.
--   - `CbitFeasible`: PDF p.10, Theorem 8: both cost coordinates and fidelity computed from one actual code. Positive n only; finite entanglement rate is not fixed optimal.
--   - `ClassicalMergingAchievable`: PDF pp.10--11: optimize classical cost over every finite signed EPR rate; full-output fidelity tends to one. No optimal-ebit hypothesis.
--   - `QubitMergingBlockCode`: PDF pp.10--11, (44): one counted Alice-to-Bob qubit message and local CPTP maps; no initial shared ebits and no classical channel. The retained Alice register and Bob output Bell half are separate from the relocated source.
--   - `MotherAchievable`: PDF p.10, (44): source-preserving fully quantum rates, independently computed from actual codes; zero rates allow sublinear nonzero resources.
--   - `typicalOmega`: PDF pp.8--9, (29): compute the jointly projected IID vector, in R,A,B order. Printed normalization 1/<Omega|Omega> is corrected in normalizedTypicalSource to 1/||Omega||.
--   - `normalizedTypicalSource`: PDF p.9, (29), normalization as required by the proof. Zero Omega maps to zero by total division; the covering theorem asserts eventual nonzero mass.
--   - `coveringRows`: PDF p.15: Haar rank-one basis on the actual typical A subspace. V identifies that subspace with Fin d; the reference is never compressed away.
--   - `quantumConditionedCoherent`: PDF p.17, (65): quantum conditional coherent information, in the order A1,A2,B. This is S(B|A2)-S(A1 B|A2), not an average over a classical flag.
--   - `twoCopyTwirl`: PDF pp.8,21, (24),(B1): probability Haar conjugation by U tensor U.
--   - `symmetryProjector`: PDF p.21, (B2): symmetric and antisymmetric projectors.
--   - `embeddedSwap`: PDF pp.8,21: F_L extended by zero through the chosen rank-L subspace.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, https://arxiv.org/abs/quant-ph/0512247v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

/-!
Horodecki, Oppenheim and Winter, quant-ph/0512247v1.
PDF page numbers throughout. The independent-paper override permits the pinned
accepted-paper imports. All new definitions are local to this paper.
Full-output unhalved trace norm and squared fidelity are kept distinct.
Compilation is pending the separate mechanical stage.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
open MeasureTheory
open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)
open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)
open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)
open QAlgorithms.Papers.Independent.Information100.P32 (purity)
open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-!
Repair reuse assessment (exact accepted bodies inspected):
Claimed50.P38.branchWeight takes a flag-diagonal block, whereas
mergingBranchProbability traces an Alice Kraus branch with a passive reference.
Support50.P38.quantumError is an average HALF trace-norm compression error,
whereas mergingDecouplingError is the FULL weighted decoupling norm of (10).
Dependency50.P19.MotherCode is a source/rate/slack feasibility proposition;
QubitMergingBlockCode is an explicit pair of CPTP maps with an integer qubit
message, needed to compute both limiting rates and the same output error.
Its motherOutput, motherTarget and sourceCopies are reused without change.
Dependency50.P45.typicalState is the normalized projector on a frequency-typical
subspace, whereas normalizedTypicalSource is the pure jointly projected IID
source of (29), using the accepted weakTypicalProjector.
Claimed50.P20.conditionalCoherent and Support50.P02.CQMacData.conditionalCoherent
average a classical flag; quantumConditionedCoherent is the quantum-conditioned
entropy difference (65). Substituting those frozen namesakes changes the source
objects. The distinct names below record those differences; no frozen body is
copied, modified, or silently substituted.
-/

/-- PDF p.5, (6)--(10): the unnormalized RA1 branch, with R a spectator. -/
def branchRA {L : ℕ} {A R : Type} [Fintype A] (P : Matrix (Fin L) A ℂ)
    (rho : Matrix (R × A) (R × A) ℂ) : Matrix (R × Fin L) (R × Fin L) ℂ :=
  idTensorSuperop (conjSuperop P) rho

/-- PDF p.5, (10): rho_R tensor tau_L, in reference-first order. -/
def decoupled {R : Type} (L : ℕ) (rhoR : Matrix R R ℂ) :
    Matrix (R × Fin L) (R × Fin L) ℂ :=
  Matrix.kronecker rhoR (((L : ℂ)⁻¹) • (1 : Matrix (Fin L) (Fin L) ℂ))

/-- PDF p.5, (7): Born weight of the computed subnormalized RA1 branch. -/
def mergingBranchProbability {L : ℕ} {A R : Type} [Fintype A] [Fintype R]
    (P : Matrix (Fin L) A ℂ) (rhoRA : Matrix (R × A) (R × A) ℂ) : ℝ :=
  (branchRA P rhoRA).trace.re

/-- PDF p.5, (10): homogeneous weighted trace norms. For a positive branch,
||omega-p tau tensor rho_R||_1=p||omega/p-tau tensor rho_R||_1.
A zero-weight positive branch is zero, so no division or nonstate occurs. -/
def mergingDecouplingError {L : ℕ} {A B R J : Type} [Fintype A] [Fintype B] [Fintype R] [Fintype J]
    (rho : Matrix (R × (A × B)) (R × (A × B)) ℂ)
    (P : J → Matrix (Fin L) A ℂ) : ℝ :=
  let ar := marginalRA rho
  ∑ j, traceNorm (branchRA (P j) ar -
    (mergingBranchProbability (P j) ar : ℂ) • decoupled L (traceRight rho))

/-- PDF p.6, (14), corrected: sum UNNORMALIZED branches, including their weights. -/
def completedMap {L : ℕ} {A B J : Type} [Fintype A] [Fintype B] [Fintype J]
    (P : J → Matrix (Fin L) A ℂ)
    (V : J → Matrix (Fin L × (A × B)) B ℂ) :
    Superop (A × B) (Fin L × (Fin L × (A × B))) :=
  fun rho => ∑ j, productApply (conjSuperop (P j)) (conjSuperop (V j)) rho

/-- PDF pp.5--6, (9),(15),(16): Bob's conditional isometries complete the
specified measurement; full source/reference and Phi_L are tested jointly.
No initial entanglement is supplied, so the cost is -log2 L. -/
def CompletedMerging {L : ℕ} {A B R J : Type} [Fintype A] [Fintype B] [Fintype R] [Fintype J]
    (rho : Matrix (R × (A × B)) (R × (A × B)) ℂ)
    (P : J → Matrix (Fin L) A ℂ) (eps : ℝ) : Prop :=
  ∃ V : J → Matrix (Fin L × (A × B)) B ℂ,
    (∀ j, (V j)ᴴ * V j = 1) ∧ IsLOCC (completedMap P V) ∧
    IsChannel (completedMap P V) ∧
    1 - eps ≤ (rootFidelity (idTensorSuperop (completedMap P V) rho)
      (motherTarget L rho)) ^ 2 ∧
    traceNorm (idTensorSuperop (completedMap P V) rho - motherTarget L rho) ≤
      2 * Real.sqrt eps

/-- PDF pp.6,8: N full coordinate blocks, followed by the residual block,
embedded in the same L-dimensional output; at d%L=0 the last branch is zero. -/
def blockRow (d L : ℕ) (j : Fin (d / L + 1)) : Matrix (Fin L) (Fin d) ℂ :=
  fun i a => if j.val < d / L then
    (if a.val = j.val * L + i.val then 1 else 0)
  else if i.val < d % L ∧ a.val = (d / L) * L + i.val then 1 else 0

/-- PDF p.8: a single Haar unitary rotates all orthogonal blocks. -/
def randomBlocks (d L : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Fin (d / L + 1) → Matrix (Fin L) (Fin d) ℂ :=
  fun j => blockRow d L j * (U : Matrix (Fin d) (Fin d) ℂ)

/-- PDF p.6, (17): the exact one-shot quantum-error bound. -/
def oneShotBound (d L r : ℕ) (D : ℝ) : ℝ :=
  2 * Real.sqrt ((L : ℝ) * r / D) + 2 * L / d

/-- PDF p.7: omega for a fixed coisometry P0 followed by Haar U. -/
def randomOmega {d L : ℕ} {R : Type} [Fintype R] (P0 : Matrix (Fin L) (Fin d) ℂ)
    (rhoRA : Matrix (R × Fin d) (R × Fin d) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :=
  branchRA (P0 * (U : Matrix (Fin d) (Fin d) ℂ)) rhoRA

/-- PDF pp.8--9: no supplied entanglement, complete transferred source and
output Bell state, actual LOCC map; eps is the full trace-norm error. -/
def UnassistedMerging {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (rho : Matrix (R × (A × B)) (R × (A × B)) ℂ) (L : ℕ) (eps : ℝ) : Prop :=
  0 < L ∧ ∃ M : Superop (A × B) (Fin L × (Fin L × (A × B))),
    IsLOCC M ∧ IsChannel M ∧
    traceNorm (idTensorSuperop M rho - motherTarget L rho) ≤ eps

/-- PDF pp.10--11: arbitrary finite adaptive LOCC with a maximum binary
transcript budget. Uncommunicated local channels/private Kraus labels cost zero.
A public bit costs one in EITHER direction. Padding makes branch maxima equal;
it is an upper budget, not a sum over counterfactual branches. -/
inductive BitLOCC : {a b c d : ℕ} → ℕ →
    Superop (Fin a × Fin b) (Fin c × Fin d) → Prop
  | identity (a b : ℕ) : BitLOCC 0 (fun X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ => X)
  | pad {a b c d n : ℕ} {M : Superop (Fin a × Fin b) (Fin c × Fin d)}
      (h : BitLOCC n M) : BitLOCC (n+1) M
  | aliceLocal {a b c d h n : ℕ} (F : Superop (Fin a) (Fin h)) (hF : IsChannel F)
      (M : Superop (Fin h × Fin b) (Fin c × Fin d)) (hM : BitLOCC n M) :
      BitLOCC n (fun X => M (productApply F id X))
  | bobLocal {a b c d h n : ℕ} (F : Superop (Fin b) (Fin h)) (hF : IsChannel F)
      (M : Superop (Fin a × Fin h) (Fin c × Fin d)) (hM : BitLOCC n M) :
      BitLOCC n (fun X => M (productApply id F X))
  | aliceBit {a b c d h e n : ℕ}
      (E : Bool × Fin e → Matrix (Fin h) (Fin a) ℂ) (hE : IsKrausFamily E)
      (next : Bool → Superop (Fin h × Fin b) (Fin c × Fin d))
      (valid : ∀ j, BitLOCC n (next j)) :
      BitLOCC (n+1) (fun X => ∑ j : Bool,
        next j (productApply (krausApply (fun k => E (j,k))) id X))
  | bobBit {a b c d h e n : ℕ}
      (E : Bool × Fin e → Matrix (Fin h) (Fin b) ℂ) (hE : IsKrausFamily E)
      (next : Bool → Superop (Fin a × Fin h) (Fin c × Fin d))
      (valid : ∀ j, BitLOCC n (next j)) :
      BitLOCC (n+1) (fun X => ∑ j : Bool,
        next j (productApply id (krausApply (fun k => E (j,k))) X))

/-- PDF p.10, Theorem 8: both cost coordinates and fidelity computed from
one actual code. Positive n only; finite entanglement rate is not fixed optimal. -/
def CbitFeasible {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (n : ℕ) (c e f : ℝ) : Prop :=
  ∃ P : RankMergingCode A B n, ∃ bits : ℕ,
    BitLOCC bits (finTransport P.operation) ∧
    c = (bits : ℝ) / n ∧ e = P.rate ∧
    f = mergingFidelity psi n P.K P.L P.operation

/-- PDF pp.10--11: optimize classical cost over every finite signed EPR
rate; full-output fidelity tends to one. No optimal-ebit hypothesis. -/
def ClassicalMergingAchievable {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (c : ℝ) : Prop :=
  ∃ e : ℝ, ∃ cs es fs : ℕ → ℝ,
    (∀ n, 0 < n → CbitFeasible psi n (cs n) (es n) (fs n)) ∧
    Filter.Tendsto cs Filter.atTop (nhds c) ∧
    Filter.Tendsto es Filter.atTop (nhds e) ∧
    Filter.Tendsto fs Filter.atTop (nhds 1)

/-- PDF pp.10--11, (44): one counted Alice-to-Bob qubit message and local
CPTP maps; no initial shared ebits and no classical channel. The retained
Alice register and Bob output Bell half are separate from the relocated source. -/
structure QubitMergingBlockCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  qubits : ℕ
  L : ℕ
  L_pos : 0 < L
  encoder : Superop (Fin n → A) (Fin L × Fin (2 ^ qubits))
  decoder : Superop (Fin (2 ^ qubits) × (Fin n → B))
    (Fin L × ((Fin n → A) × (Fin n → B)))
  encoder_channel : IsChannel encoder
  decoder_channel : IsChannel decoder

/-- PDF p.10, (44): source-preserving fully quantum rates, independently
computed from actual codes; zero rates allow sublinear nonzero resources. -/
def MotherAchievable {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (q e : ℝ) : Prop :=
  ∃ P : (n : ℕ) → QubitMergingBlockCode A B (n+1),
    Filter.Tendsto (fun n => ((P n).qubits : ℝ) / (n+1 : ℕ)) Filter.atTop (nhds q) ∧
    Filter.Tendsto (fun n => Real.logb 2 ((P n).L : ℝ) / (n+1 : ℕ))
      Filter.atTop (nhds e) ∧
    Filter.Tendsto (fun n => traceNorm
      (motherOutput (P n).encoder (P n).decoder (sourceCopies (n+1) (pureDensity psi)) -
        motherTarget (P n).L (sourceCopies (n+1) (pureDensity psi))))
      Filter.atTop (nhds 0)

/-- PDF pp.8--9, (29): compute the jointly projected IID vector, in R,A,B order.
Printed normalization 1/<Omega|Omega> is corrected in normalizedTypicalSource to 1/||Omega||. -/
def typicalOmega {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (delta : ℝ) (n : ℕ) :=
  let rho := pureDensity psi
  let v : EuclideanSpace ℂ ((Fin n → R) × ((Fin n → A) × (Fin n → B))) :=
    WithLp.toLp 2 fun x => tensorPow n psi (fun t => (x.1 t,(x.2.1 t,x.2.2 t)))
  act (Matrix.kronecker (weakTypicalProjector (traceRight rho) delta n)
    (Matrix.kronecker (weakTypicalProjector (traceRight (traceLeft rho)) delta n)
      (weakTypicalProjector (traceLeft (traceLeft rho)) delta n))) v

/-- PDF p.9, (29), normalization as required by the proof. Zero Omega maps
to zero by total division; the covering theorem asserts eventual nonzero mass. -/
def normalizedTypicalSource {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (delta : ℝ) (n : ℕ) :=
  ((‖typicalOmega psi delta n‖⁻¹ : ℝ) : ℂ) • typicalOmega psi delta n

/-- PDF p.15: Haar rank-one basis on the actual typical A subspace.
V identifies that subspace with Fin d; the reference is never compressed away. -/
def coveringRows {d : ℕ} {A : Type} [Fintype A] (V : Matrix (Fin d) A ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Fin d → Matrix (Fin 1) A ℂ :=
  fun j _ a => ((U : Matrix (Fin d) (Fin d) ℂ) * V) j a

/-- PDF p.17, (65): quantum conditional coherent information, in the order
A1,A2,B. This is S(B|A2)-S(A1 B|A2), not an average over a classical flag. -/
def quantumConditionedCoherent {A1 A2 B : Type} [Fintype A1] [Fintype A2] [Fintype B]
    (rho : Matrix (A1 × (A2 × B)) (A1 × (A2 × B)) ℂ) : ℝ :=
  (vnEntropy (traceLeft rho) - vnEntropy (traceRight (traceLeft rho))) -
    (vnEntropy rho - vnEntropy (traceRight (traceLeft rho)))

/-- PDF pp.8,21, (24),(B1): probability Haar conjugation by U tensor U. -/
def twoCopyTwirl (d : ℕ) (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    (Matrix.kronecker (U : Matrix (Fin d) (Fin d) ℂ)
      (U : Matrix (Fin d) (Fin d) ℂ))ᴴ * X *
      Matrix.kronecker (U : Matrix (Fin d) (Fin d) ℂ)
        (U : Matrix (Fin d) (Fin d) ℂ) ∂(Schur.unitaryHaar d)

/-- PDF p.21, (B2): symmetric and antisymmetric projectors. -/
def symmetryProjector (d : ℕ) (symmetric : Bool) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1/2 : ℂ) • (if symmetric then 1 + swap (Fin d) else 1 - swap (Fin d))

/-- PDF pp.8,21: F_L extended by zero through the chosen rank-L subspace. -/
def embeddedSwap {d L : ℕ} (P0 : Matrix (Fin L) (Fin d) ℂ) :=
  (Matrix.kronecker P0 P0)ᴴ * swap (Fin L) * Matrix.kronecker P0 P0

/-- Sanity: zero-probability branches contribute zero, without normalizing zero. -/
example {L : ℕ} {A R : Type} [Fintype A] [Fintype R]
    (rho : Matrix (R × A) (R × A) ℂ) :
    mergingBranchProbability (0 : Matrix (Fin L) A ℂ) rho = 0 := by
  have hzero : branchRA (0 : Matrix (Fin L) A ℂ) rho = 0 := by
    ext p q
    simp [branchRA, idTensorSuperop, conjSuperop, Matrix.of_apply]
  simp [mergingBranchProbability, hzero]

/-- Sanity: exactly divisible dimensions have a zero residual operator. -/
example : blockRow 2 1 (2 : Fin (2 / 1 + 1)) = 0 := by
  ext i a
  simp [blockRow]

/-- Sanity: (17) has no factor d_A under its square root. -/
example : oneShotBound 2 1 1 1 = 3 := by
  norm_num [oneShotBound]

/-- Sanity: no transcript or communication in the identity protocol. -/
example : BitLOCC 0 (fun X : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ => X) :=
  BitLOCC.identity 1 1

/-- Sanity: the squared norms and rank bound include the zero operator. -/
example : traceNorm (0 : Matrix (Fin 1) (Fin 1) ℂ)^2 ≤
    (Matrix.rank (0 : Matrix (Fin 1) (Fin 1) ℂ) : ℝ) *
      frobNorm (0 : Matrix (Fin 1) (Fin 1) ℂ)^2 := by
  simp [traceNorm, cfc_zero]

/-- Sanity: the antisymmetric sector vanishes on a one-dimensional register. -/
example : symmetryProjector 1 false = 0 := by
  ext x y
  have h1 : x.1 = y.2 := Subsingleton.elim _ _
  have h2 : x.2 = y.1 := Subsingleton.elim _ _
  have h3 : x = y := Subsingleton.elim _ _
  have h4 : y.1 = y.2 := Subsingleton.elim _ _
  simp [symmetryProjector, swap, Matrix.one_apply, h1, h2, h3, h4]

end QAlgorithms.Papers.Independent.Intake100.P01


