-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P56
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P56
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T06:36:59.397993+00:00
-- url     : https://prove2.me/theorems/88a3d449-6c72-4e99-9f48-f41d1c86556a
-- title:
--   Definitions for Rényi squashed entanglement, discord, and relative entropy differences
-- statement:
--   The objects the formalized statements of *Rényi squashed entanglement, discord, and relative entropy differences* (arXiv:1410.1443) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RenyiOrder`: PDF p.6: positive orders other than one.
--   - `DPOrder`: PDF p.7: data-processing range, including two.
--   - `embedAC`: PDF p.7: AC embedded with identity on B.
--   - `cmiOne`: PDF pp.2,7: ordinary CMI in nats, conditioned on C.
--   - `renyiCMI`: PDF p.7, (3.18): OPTIMIZED Petz CMI with von Neumann endpoint at one. Valid normalized states give a strictly positive scalar logarithm argument. All spectral powers, including exponent zero, vanish on the kernel (p.5).
--   - `renyiSquashed`: PDF p.8, (4.1): half the extended infimum over ALL finite normalized extensions. The ancillary dimension e+1 is arbitrary, with no cardinality cap.
--   - `LocalMonotonicityConjecture`: PDF p.7, Conjecture 1: uniformly quantified FIRST-register monotonicity of actual (3.18), not a theorem or a hypothesis of squashed monotonicity itself.
--   - `PetzParameterConjecture`: PDF pp.7,11,19: optimized Petz CMI parameter conjecture, including one.
--   - `flagLeft`: PDF p.8, (4.4): label held by Alice.
--   - `flagBoth`: PDF p.8, (4.4): same classical label copied to both parties.
--   - `flagRight`: PDF p.8, (4.4): label held by Bob.
--   - `renyiEntropySupportNats`: PDF pp.5–6, (3.9): reuse the accepted natural-log entropy at positive orders; only its order-zero endpoint is replaced by log support rank, as required by Proposition 13 on p.13. The frozen ordinary zeroth power is the identity.
--   - `renyiConditionalEntropy`: PDF p.6, (3.14): optimized Petz conditional entropy H_alpha(A|B).
--   - `FinitePureDecomposition`: PDF p.12, (4.35): the accepted finite pure ensembles constrained to represent rho. This finite subtype differs from Next46.P42.PureDecomposition, which is countably indexed and has a trace-norm barycenter. Unit vectors are required even in zero-weight branches; the weights exclude an empty ensemble.
--   - `ensembleAX`: PDF p.12: AX marginal of the ensemble's actual classical extension.
--   - `renyiFormation`: PDF p.12, Definition 11: infimum of conditional entropy, independently of the formula and attainment asserted in Proposition 12.
--   - `formationObjective`: PDF p.12, (4.38): outer weight p_x, never p_x^alpha.
--   - `maxEntangledKet`: PDF p.5, (3.3): maximally entangled ket in arbitrary orthonormal Schmidt families, represented by columns of rectangular isometries.
--   - `measurementOutput`: PDF p.16, (5.2): measurement dilation A -> E X with E=(X,A). Off-diagonal outcome coherence is retained in the environment and output.
--   - `renyiDiscord`: PDF p.16, Definition 16: unrestricted POVM infimum. The identical formula is used beyond order two in Propositions 18–19; the alpha=1 branch is ordinary discord, through the ordinary CMI branch of renyiCMI.
--   - `KetPOVM`: PDF pp.17–20: arbitrary, unnormalized rank-one POVM kets. Null effects are allowed as removable entries, without changing either infimum.
--   - `rankOneDiscord`: PDF p.17: restricted infimum; zero kets may be deleted. Neither attainment nor optimality of every projective measurement is asserted.
--   - `IsClassicalOnA`: PDF p.16, (5.3): cq in any orthonormal basis of the measured register A.
--   - `conditionalKet`: PDF p.20, (5.28): unnormalized conditional ket on B.
--   - `pureDiscordObjective`: PDF p.20, (5.27): omit zero-probability branches; retain the sign-changing prefactor inside the infimum.
--   - `sandwichedCMI`: PDF p.21, (5.42): fixed-reference SANDWICHED CMI. The Schatten expression is equivalently log Tr(K^alpha)/(alpha-1) for this positive K.
--   - `SandwichedParameterConjecture`: PDF p.21, (5.41): separate sandwiched parameter conjecture, including one.
--   - `measurementRecovery`: PDF pp.22,29: one common measure-and-prepare map computed from the marginal. A zero-probability branch prepares the supplied fixed density; its contribution on the source joint state is zero, independently of completion.
--   - `applyFirstSuperop`: PDF p.22: a map acts on A, leaving B untouched, including off-diagonal blocks.
--   - `relativeReal`: PDF p.23, (6.1): real Umegaki formula on the full-rank domain.
--   - `relativeEntropyDifference`: PDF p.23, (6.1): computed relativeEntropyDifference, finite on its full-rank domain.
--   - `StrictChannel`: PDF p.5: strict CPTP with reference-stable positive definiteness.
--   - `differencePetz`: PDF p.25, (6.12): actual Petz relativeEntropyDifference, not a relativeEntropyDifference of Renyi divergences. The branch at one is the continuous Umegaki endpoint.
--   - `differenceSandwiched`: PDF p.25, (6.13), read using well-typed (6.18): remove printed Tr before a scalar Schatten norm. For positive K the intended value is log Tr(K^a)/(a-1).
--   - `DifferenceParameterConjecture`: PDF p.25, Conjecture 26: positive-order comparisons of BOTH computed functionals, including one. No zero-order expression is needed by the targets.
--   - `RecoveryRemainder`: PDF p.26, (6.24): UNIVERSAL recovery inequality with the original full-rank strict-channel domain. Singular applications remain conclusions.
--   - `jointRecovered`: PDF p.27, (6.28): branch recovered positive operator, not necessarily a state.
--   - `JointRemainderAt`: PDF p.27: joint-convexity remainder with square root INSIDE the sum.
--   - `JointRemainder`: PDF pp.27–29: universal joint-convexity remainder scheme.
--   - `differenceVariance`: PDF p.35, (B.14): FULL variance including the final Kadison–Schwarz correction.
--   - `cmiReference`: PDF p.25, (6.16): rho_B tensor rho_AC in ABC ordering.
--   - `fixedPetzCMI`: PDF p.25, (6.17): FIXED-reference Petz CMI with both rho_B^0 factors. It is deliberately not identified with optimized (3.18).
--   - `fixedSandwichedCMI`: PDF p.25, (6.18): fixed-reference sandwiched expression with support projectors.
--   - `addAncillas`: PDF p.32, (A.1): three independent arbitrary mixed ancillary states.
--   - `conditionedFlag`: PDF p.33, (A.11): append classical X to conditioning system C.
--   - `SquashedLOCC`: PDF p.10: complete-output monotonicity under every finite adaptive LOCC protocol, with arbitrary positive input/output dimensions and local memories.
--   - `SquashedConvex`: PDF p.10: convexity for all normalized finite ensembles.
--   - `discordRecoveryCost`: PDF p.22, (5.47): cost of the specified EB recovery map, completed on zero-probability branches with rho_A itself.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, https://arxiv.org/abs/1410.1443v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

/-! arXiv:1410.1443v3. PDF page citations, natural logarithms, arbitrary finite bases.
All conjectures remain premises. All local definitions have complete bodies.
Imports of pinned accepted paper modules use the independent-paper workflow override.
Three source ambiguities are deferred in HARD.md. Compilation is pending batch handoff. -/

noncomputable section

open Filter Topology
open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw entropy average holevo)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz extendedLog marginalAB)
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)
open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartiteProduct)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)
open QAlgorithms.Papers.Independent.Advance50.P25 (renyiEntropyNats)

variable {A B C D E X : Type}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype X]
variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E] [Nonempty X]

/-- Sanity helper for PDF pp.5,13: accept the singleton matrix and its
DecidableEq instance explicitly, so the frozen support power uses exactly the
same instance as the caller. Identify the matrix entrywise before evaluation. -/
private lemma supportPower_unit_zero [decEqUnit : DecidableEq Unit] (M : Op Unit)
    (hM : ∀ i j, M i j = 1) :
    Real.log (@supportPower Unit PUnit.fintype decEqUnit M 0).trace.re = 0 := by
  have hIdentity : M = (1 : Op Unit) := by
    ext i j
    simpa [Matrix.one_apply, Subsingleton.elim i j] using hM i j
  have hPower : @supportPower Unit PUnit.fintype decEqUnit (1 : Op Unit) 0 = 1 := by
    unfold supportPower
    rw [cfc_apply_one (R := ℝ) (A := Op Unit)
      (f := fun x : ℝ => if x = 0 then 0 else Real.rpow x 0)]
    norm_num
  rw [hIdentity, hPower]
  norm_num [Matrix.trace, Matrix.one_apply]

open scoped Matrix.Norms.L2Operator

/-- PDF p.6: positive orders other than one. -/
def RenyiOrder (a : ℝ) : Prop := 0 < a ∧ a ≠ 1

/-- PDF p.7: data-processing range, including two. -/
def DPOrder (a : ℝ) : Prop := RenyiOrder a ∧ a ≤ 2

/-- PDF p.7: AC embedded with identity on B. -/
def embedAC (M : Op (A × C)) : Op (A × (B × C)) :=
  fun i j => if i.2.1 = j.2.1 then M (i.1,i.2.2) (j.1,j.2.2) else 0

/-- PDF pp.2,7: ordinary CMI in nats, conditioned on C. -/
def cmiOne (rho : Op (A × (B × C))) : ℝ :=
  entropy (marginalAC rho) + entropy (traceLeft rho) -
    entropy (traceLeft (traceLeft rho)) - entropy rho

/-- PDF p.7, (3.18): OPTIMIZED Petz CMI with von Neumann endpoint at one.
Valid normalized states give a strictly positive scalar logarithm argument.
All spectral powers, including exponent zero, vanish on the kernel (p.5). -/
def renyiCMI (a : ℝ) (rho : Op (A × (B × C))) : ℝ :=
  if a = 1 then cmiOne rho else
    let R := embedAC (B := B) (supportPower (marginalAC rho) ((1-a)/2))
    let S := Matrix.kronecker (1 : Op B)
      (supportPower (traceLeft (traceLeft rho)) ((a-1)/2))
    a/(a-1) * Real.log (supportPower
      (S * traceLeft (R * supportPower rho a * R) * S) (1/a)).trace.re

/-- PDF p.8, (4.1): half the extended infimum over ALL finite normalized
extensions. The ancillary dimension e+1 is arbitrary, with no cardinality cap. -/
def renyiSquashed (a : ℝ) (rho : Op (A × B)) : EReal :=
  (1/2 : EReal) * sInf {v : EReal | ∃ e : ℕ,
    ∃ omega : Op (A × (B × Fin (e+1))), IsDensityMatrix omega ∧
      marginalAB omega = rho ∧ v = (renyiCMI a omega : EReal)}

/-- PDF p.7, Conjecture 1: uniformly quantified FIRST-register monotonicity
of actual (3.18), not a theorem or a hypothesis of squashed monotonicity itself. -/
def LocalMonotonicityConjecture : Prop :=
  ∀ (A B C D : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (a : ℝ), DPOrder a → ∀ rho : Op (A × (B × C)), IsDensityMatrix rho →
    ∀ N : Superop A D, IsChannel N →
      renyiCMI a (fun i j => N (fun k l => rho (k,i.2) (l,j.2)) i.1 j.1) ≤ renyiCMI a rho

/-- PDF pp.7,11,19: optimized Petz CMI parameter conjecture, including one. -/
def PetzParameterConjecture : Prop :=
  ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C] (rho : Op (A × (B × C))),
    IsDensityMatrix rho → ∀ a b : ℝ, 0 < a → a ≤ b → renyiCMI a rho ≤ renyiCMI b rho

/-- PDF p.8, (4.4): label held by Alice. -/
def flagLeft (p : X → ℝ) (rho : X → Op (A × B)) : Op ((A × X) × B) :=
  fun i j => if i.1.2 = j.1.2 then (p i.1.2 : ℂ) * rho i.1.2 (i.1.1,i.2) (j.1.1,j.2) else 0

/-- PDF p.8, (4.4): same classical label copied to both parties. -/
def flagBoth (p : X → ℝ) (rho : X → Op (A × B)) : Op ((A × X) × (B × X)) :=
  fun i j => if i.1.2 = i.2.2 ∧ j.1.2 = j.2.2 ∧ i.1.2 = j.1.2 then
    (p i.1.2 : ℂ) * rho i.1.2 (i.1.1,i.2.1) (j.1.1,j.2.1) else 0

/-- PDF p.8, (4.4): label held by Bob. -/
def flagRight (p : X → ℝ) (rho : X → Op (A × B)) : Op (A × (B × X)) :=
  fun i j => if i.2.2 = j.2.2 then (p i.2.2 : ℂ) * rho i.2.2 (i.1,i.2.1) (j.1,j.2.1) else 0

/-- PDF pp.5–6, (3.9): reuse the accepted natural-log entropy at positive
orders; only its order-zero endpoint is replaced by log support rank, as required
by Proposition 13 on p.13. The frozen ordinary zeroth power is the identity. -/
def renyiEntropySupportNats (a : ℝ) (rho : Op A) : ℝ :=
  if a = 0 then Real.log (supportPower rho 0).trace.re else renyiEntropyNats a rho

/-- PDF p.6, (3.14): optimized Petz conditional entropy H_alpha(A|B). -/
def renyiConditionalEntropy (a : ℝ) (rho : Op (A × B)) : ℝ :=
  if a = 1 then entropy rho - entropy (traceLeft rho) else
    a/(1-a) * Real.log (supportPower (traceLeft (supportPower rho a)) (1/a)).trace.re

/-- PDF p.12, (4.35): the accepted finite pure ensembles constrained to
represent rho. This finite subtype differs from Next46.P42.PureDecomposition,
which is countably indexed and has a trace-norm barycenter. Unit vectors are
required even in zero-weight branches; the weights exclude an empty ensemble. -/
def FinitePureDecomposition (rho : Op (A × B)) :=
  {ens : QAlgorithms.Papers.Independent.Information100.P08.PureEnsemble (A × B) //
    average (fun x => pureDensity (ens.vector x)) ens.prob = rho}

/-- PDF p.12: AX marginal of the ensemble's actual classical extension. -/
def ensembleAX {rho : Op (A × B)} (ens : FinitePureDecomposition rho) : Op (A × Fin ens.val.size) :=
  fun i j => if i.2 = j.2 then
    (ens.val.prob i.2 : ℂ) * traceRight (pureDensity (ens.val.vector i.2)) i.1 j.1 else 0

/-- PDF p.12, Definition 11: infimum of conditional entropy, independently
of the formula and attainment asserted in Proposition 12. -/
def renyiFormation (a : ℝ) (rho : Op (A × B)) : EReal :=
  sInf {v : EReal | ∃ ens : FinitePureDecomposition rho,
    v = (renyiConditionalEntropy a (ensembleAX ens) : EReal)}

/-- PDF p.12, (4.38): outer weight p_x, never p_x^alpha. -/
def formationObjective (a : ℝ) {rho : Op (A × B)} (ens : FinitePureDecomposition rho) : ℝ :=
  a/(1-a) * Real.log (∑ x, ens.val.prob x *
    ((supportPower (traceRight (pureDensity (ens.val.vector x))) a).trace.re) ^ (1/a))

/-- PDF p.5, (3.3): maximally entangled ket in arbitrary orthonormal Schmidt
families, represented by columns of rectangular isometries. -/
def maxEntangledKet (d : ℕ) (U : Matrix A (Fin d) ℂ) (V : Matrix B (Fin d) ℂ) :
    EuclideanSpace ℂ (A × B) :=
  WithLp.toLp 2 fun i => ((Real.sqrt d)⁻¹ : ℂ) * ∑ k, U i.1 k * V i.2 k

/-- PDF p.16, (5.2): measurement dilation A -> E X with E=(X,A).
Off-diagonal outcome coherence is retained in the environment and output. -/
def measurementOutput {m : ℕ} (M : Fin m → Op A) (rho : Op (A × B)) :
    Op ((Fin m × A) × (B × Fin m)) :=
  fun i j => if i.1.1 = i.2.2 ∧ j.1.1 = j.2.2 then
    ∑ k, ∑ l, (cfc Real.sqrt (M i.1.1)) i.1.2 k *
      rho (k,i.2.1) (l,j.2.1) * conj ((cfc Real.sqrt (M j.1.1)) j.1.2 l)
  else 0

/-- PDF p.16, Definition 16: unrestricted POVM infimum. The identical
formula is used beyond order two in Propositions 18–19; the alpha=1 branch
is ordinary discord, through the ordinary CMI branch of renyiCMI. -/
def renyiDiscord (a : ℝ) (rho : Op (A × B)) : EReal :=
  sInf {v : EReal | ∃ m : ℕ, 0 < m ∧ ∃ M : Fin m → Op A,
    IsPOVM M ∧ v = (renyiCMI a (measurementOutput M rho) : EReal)}

/-- PDF pp.17–20: arbitrary, unnormalized rank-one POVM kets.
Null effects are allowed as removable entries, without changing either infimum. -/
def KetPOVM {m : ℕ} (phi : Fin m → EuclideanSpace ℂ A) : Prop :=
  IsPOVM (fun x => pureDensity (phi x))

/-- PDF p.17: restricted infimum; zero kets may be deleted.
Neither attainment nor optimality of every projective measurement is asserted. -/
def rankOneDiscord (a : ℝ) (rho : Op (A × B)) : EReal :=
  sInf {v : EReal | ∃ m : ℕ, 0 < m ∧ ∃ phi : Fin m → EuclideanSpace ℂ A,
    KetPOVM phi ∧ v = (renyiCMI a (measurementOutput (fun x => pureDensity (phi x)) rho) : EReal)}

/-- PDF p.16, (5.3): cq in any orthonormal basis of the measured register A. -/
def IsClassicalOnA (rho : Op (A × B)) : Prop :=
  ∃ U : Matrix.unitaryGroup A ℂ, ∃ p : A → ℝ, ∃ states : A → Op B,
    IsLaw p ∧ (∀ x, IsDensityMatrix (states x)) ∧
    rho = fun i j => ∑ x, (p x : ℂ) * (U : Op A) i.1 x *
      conj ((U : Op A) j.1 x) * states x i.2 j.2

/-- PDF p.20, (5.28): unnormalized conditional ket on B. -/
def conditionalKet (psi : EuclideanSpace ℂ (A × B)) (phi : EuclideanSpace ℂ A) :
    EuclideanSpace ℂ B := WithLp.toLp 2 fun b => ∑ a, conj (phi a) * psi (a,b)

/-- PDF p.20, (5.27): omit zero-probability branches; retain the
sign-changing prefactor inside the infimum. -/
def pureDiscordObjective (a : ℝ) {m : ℕ} (psi : EuclideanSpace ℂ (A × B))
    (phi : Fin m → EuclideanSpace ℂ A) : ℝ :=
  a/(a-1) * Real.log (∑ x,
    let z := conditionalKet psi (phi x)
    let p := ‖z‖^2
    if 0 < p then
      let xi := ((Real.sqrt p)⁻¹ : ℂ) • z
      p * ((inner ℂ xi (act (supportPower (traceLeft (pureDensity psi)) (1-a)) xi)).re) ^ (1/a)
    else 0)

/-- PDF p.21, (5.42): fixed-reference SANDWICHED CMI.
The Schatten expression is equivalently log Tr(K^alpha)/(alpha-1) for this positive K. -/
def sandwichedCMI (a : ℝ) (rho : Op (A × (B × C))) : ℝ :=
  if a = 1 then cmiOne rho else
    let R := embedAC (B := B) (supportPower (marginalAC rho) ((1-a)/(2*a)))
    let S := Matrix.kronecker (1 : Op B)
      (supportPower (traceLeft (traceLeft rho)) ((a-1)/(2*a)))
    let T := supportPower (traceLeft rho) ((1-a)/a)
    let L := supportPower rho (1/2)
    Real.log (supportPower
      (L * R * Matrix.kronecker (1 : Op A) (S * T * S) * R * L) a).trace.re / (a-1)

/-- PDF p.21, (5.41): separate sandwiched parameter conjecture, including one. -/
def SandwichedParameterConjecture : Prop :=
  ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C] (rho : Op (A × (B × C))),
    IsDensityMatrix rho → ∀ a b : ℝ, 0 < a → a ≤ b → sandwichedCMI a rho ≤ sandwichedCMI b rho

/-- PDF pp.22,29: one common measure-and-prepare map computed from the
marginal. A zero-probability branch prepares the supplied fixed density;
its contribution on the source joint state is zero, independently of completion. -/
def measurementRecovery {m : ℕ} (rho fallback : Op A)
    (phi : Fin m → EuclideanSpace ℂ A) : Superop A A :=
  fun Z => ∑ x,
    let P := pureDensity (phi x)
    let q := effectProb P rho
    ((P * Z).trace) •
      (if 0 < q then ((q⁻¹ : ℝ) : ℂ) • (cfc Real.sqrt rho * P * cfc Real.sqrt rho) else fallback)

/-- PDF p.22: a map acts on A, leaving B untouched, including off-diagonal blocks. -/
def applyFirstSuperop (N : Superop A C) (rho : Op (A × B)) : Op (C × B) :=
  fun i j => N (fun k l => rho (k,i.2) (l,j.2)) i.1 j.1

/-- PDF p.23, (6.1): real Umegaki formula on the full-rank domain. -/
def relativeReal (rho sigma : Op A) : ℝ :=
  (rho * (cfc Real.log rho - cfc Real.log sigma)).trace.re

/-- PDF p.23, (6.1): computed relativeEntropyDifference, finite on its full-rank domain. -/
def relativeEntropyDifference (rho sigma : Op A) (N : Superop A B) : ℝ :=
  relativeReal rho sigma - relativeReal (N rho) (N sigma)

/-- PDF p.5: strict CPTP with reference-stable positive definiteness. -/
def StrictChannel (N : Superop A B) : Prop :=
  IsChannel N ∧ ∀ n : ℕ, ∀ Z : Op (Fin n × A), Z.PosDef → (idTensorSuperop N Z).PosDef

/-- PDF p.25, (6.12): actual Petz relativeEntropyDifference, not a relativeEntropyDifference of Renyi divergences.
The branch at one is the continuous Umegaki endpoint. -/
def differencePetz (a : ℝ) (rho sigma : Op A) (N : Superop A B) : ℝ :=
  if a = 1 then relativeEntropyDifference rho sigma N else
    let S := supportPower sigma ((1-a)/2)
    let T := supportPower (N sigma) ((a-1)/2)
    Real.log (supportPower rho a * S *
      channelAdjoint N (T * supportPower (N rho) (1-a) * T) * S).trace.re / (a-1)

/-- PDF p.25, (6.13), read using well-typed (6.18): remove printed Tr
before a scalar Schatten norm. For positive K the intended value is log Tr(K^a)/(a-1). -/
def differenceSandwiched (a : ℝ) (rho sigma : Op A) (N : Superop A B) : ℝ :=
  if a = 1 then relativeEntropyDifference rho sigma N else
    let S := supportPower sigma ((1-a)/(2*a))
    let T := supportPower (N sigma) ((a-1)/(2*a))
    let R := supportPower rho (1/2)
    let K := R * S * channelAdjoint N (T * supportPower (N rho) ((1-a)/a) * T) * S * R
    Real.log (supportPower K a).trace.re / (a-1)

/-- PDF p.25, Conjecture 26: positive-order comparisons of BOTH computed
functionals, including one. No zero-order expression is needed by the targets. -/
def DifferenceParameterConjecture : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (rho sigma : Op A) (N : Superop A B),
    IsDensityMatrix rho → rho.PosDef → IsDensityMatrix sigma → sigma.PosDef → StrictChannel N →
    ∀ a b : ℝ, 0 < a → a ≤ b →
      differencePetz a rho sigma N ≤ differencePetz b rho sigma N ∧
      differenceSandwiched a rho sigma N ≤ differenceSandwiched b rho sigma N

/-- PDF p.26, (6.24): UNIVERSAL recovery inequality with the original
full-rank strict-channel domain. Singular applications remain conclusions. -/
def RecoveryRemainder : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (rho sigma : Op A) (N : Superop A B),
    IsDensityMatrix rho → rho.PosDef → IsDensityMatrix sigma → sigma.PosDef → StrictChannel N →
      -extendedLog (squaredFidelity rho (petz sigma N (N rho))) ≤ (relativeEntropyDifference rho sigma N : EReal)

/-- PDF p.27, (6.28): branch recovered positive operator, not necessarily a state. -/
def jointRecovered (sigma barSigma barRho : Op A) : Op A :=
  let S := supportPower sigma (1/2)
  let T := supportPower barSigma (-1/2)
  S * T * barRho * T * S

/-- PDF p.27: joint-convexity remainder with square root INSIDE the sum. -/
def JointRemainderAt (p : X → ℝ) (rho sigma : X → Op A) : Prop :=
  -(2 * extendedLog (∑ x, p x * Real.sqrt
    (squaredFidelity (rho x) (jointRecovered (sigma x) (average sigma p) (average rho p))))) ≤
      (((∑ x, p x * relativeReal (rho x) (sigma x)) -
        relativeReal (average rho p) (average sigma p) : ℝ) : EReal)

/-- PDF pp.27–29: universal joint-convexity remainder scheme. -/
def JointRemainder : Prop :=
  ∀ (A X : Type) [Fintype A] [Fintype X] [Nonempty A] [Nonempty X]
    (p : X → ℝ) (rho sigma : X → Op A), IsLaw p →
    (∀ x, IsDensityMatrix (rho x) ∧ (rho x).PosDef) →
    (∀ x, IsDensityMatrix (sigma x) ∧ (sigma x).PosDef) → JointRemainderAt p rho sigma

/-- PDF p.35, (B.14): FULL variance including the final Kadison–Schwarz correction. -/
def differenceVariance (rho sigma : Op A) (N : Superop A B) : ℝ :=
  let L := cfc Real.log (N rho) - cfc Real.log (N sigma)
  let H := cfc Real.log rho - cfc Real.log sigma - channelAdjoint N L
  let d := relativeEntropyDifference rho sigma N
  (rho * (H - (d : ℂ) • (1 : Op A)) ^ 2).trace.re +
    (N rho * L ^ 2).trace.re - (rho * (channelAdjoint N L) ^ 2).trace.re

/-- PDF p.25, (6.16): rho_B tensor rho_AC in ABC ordering. -/
def cmiReference (rho : Op (A × (B × C))) : Op (A × (B × C)) :=
  fun i j => traceRight (traceLeft rho) i.2.1 j.2.1 *
    marginalAC rho (i.1,i.2.2) (j.1,j.2.2)

/-- PDF p.25, (6.17): FIXED-reference Petz CMI with both rho_B^0 factors.
It is deliberately not identified with optimized (3.18). -/
def fixedPetzCMI (a : ℝ) (rho : Op (A × (B × C))) : ℝ :=
  let P := Matrix.kronecker (1 : Op A)
    (Matrix.kronecker (supportPower (traceRight (traceLeft rho)) 0) (1 : Op C))
  let R := embedAC (B := B) (supportPower (marginalAC rho) ((1-a)/2))
  let S := Matrix.kronecker (1 : Op B) (supportPower (traceLeft (traceLeft rho)) ((a-1)/2))
  Real.log (supportPower rho a * P * R *
    Matrix.kronecker (1 : Op A) (S * supportPower (traceLeft rho) (1-a) * S) * R * P).trace.re / (a-1)

/-- PDF p.25, (6.18): fixed-reference sandwiched expression with support projectors. -/
def fixedSandwichedCMI (a : ℝ) (rho : Op (A × (B × C))) : ℝ :=
  let P := Matrix.kronecker (1 : Op A)
    (Matrix.kronecker (supportPower (traceRight (traceLeft rho)) 0) (1 : Op C))
  let R := embedAC (B := B) (supportPower (marginalAC rho) ((1-a)/(2*a)))
  let S := Matrix.kronecker (1 : Op B) (supportPower (traceLeft (traceLeft rho)) ((a-1)/(2*a)))
  let L := supportPower rho (1/2)
  Real.log (supportPower (L * P * R *
    Matrix.kronecker (1 : Op A) (S * supportPower (traceLeft rho) ((1-a)/a) * S) * R * P * L) a).trace.re / (a-1)

/-- PDF p.32, (A.1): three independent arbitrary mixed ancillary states. -/
def addAncillas {A1 B1 C1 : Type} (rho : Op (A × (B × C)))
    (sigma : Op A1) (tau : Op B1) (gamma : Op C1) :
    Op ((A × A1) × ((B × B1) × (C × C1))) :=
  fun i j => rho (i.1.1,(i.2.1.1,i.2.2.1)) (j.1.1,(j.2.1.1,j.2.2.1)) *
    sigma i.1.2 j.1.2 * tau i.2.1.2 j.2.1.2 * gamma i.2.2.2 j.2.2.2

/-- PDF p.33, (A.11): append classical X to conditioning system C. -/
def conditionedFlag (p : X → ℝ) (rho : X → Op (A × (B × C))) : Op (A × (B × (C × X))) :=
  fun i j => if i.2.2.2 = j.2.2.2 then
    (p i.2.2.2 : ℂ) * rho i.2.2.2 (i.1,(i.2.1,i.2.2.1)) (j.1,(j.2.1,j.2.2.1)) else 0

/-! Small sanity instances: no proofs of paper targets. -/

example : RenyiOrder 2 := by norm_num [RenyiOrder]

example : ¬ RenyiOrder 1 := by simp [RenyiOrder]

example {rho : Op (A × B)} (ens : FinitePureDecomposition rho) :
    (∀ x, 0 ≤ ens.val.prob x) ∧ ∑ x, ens.val.prob x = 1 := ⟨ens.val.nonneg, ens.val.total⟩

example (rho : Op (A × (B × C))) : renyiCMI 1 rho = cmiOne rho := by simp [renyiCMI]

example (rho sigma : Op A) (N : Superop A B) :
    differencePetz 1 rho sigma N = relativeEntropyDifference rho sigma N := by simp [differencePetz]

example (rho sigma : Op A) (N : Superop A B) :
    differenceSandwiched 1 rho sigma N = relativeEntropyDifference rho sigma N := by simp [differenceSandwiched]

example : -extendedLog 0 = (⊤ : EReal) := by simp [extendedLog]

example {m : ℕ} (phi : Fin m → EuclideanSpace ℂ A) :
    KetPOVM phi ↔ IsPOVM (fun x => pureDensity (phi x)) := Iff.rfl

/-- Sanity: the unit basis gives the one-dimensional normalized maximally entangled ket. -/
example : maxEntangledKet 1 (1 : Op (Fin 1)) (1 : Op (Fin 1)) = ket (0,0) := by
  ext i
  have hi : i = (0, 0) := Subsingleton.elim _ _
  subst i
  simp [maxEntangledKet, ket, Matrix.one_apply]

/-- Sanity: the copied flag cannot disagree between the two parties. -/
example (p : X → ℝ) (rho : X → Op (A × B))
    (aa : A) (bb : B) (x y : X) (h : x ≠ y) :
    flagBoth p rho ((aa,x),(bb,y)) ((aa,x),(bb,y)) = 0 := by
  simp [flagBoth, h]

/-- Sanity: an ancillary matrix unit contributes its actual diagonal entry. -/
example (rho : Op (A × (B × C))) (sigma : Op D) (tau : Op E) (gamma : Op X)
    (a : A) (b : B) (c : C) (d : D) (e : E) (x : X) :
    addAncillas rho sigma tau gamma ((a,d),((b,e),(c,x))) ((a,d),((b,e),(c,x))) =
      rho (a,(b,c)) (a,(b,c)) * sigma d d * tau e e * gamma x x := rfl

/-- Sanity: partial contraction on a product computational ket conjugates the bra. -/
example (a : A) (b : B) : conditionalKet (ket (a,b)) (ket a) = ket b := by
  ext j
  by_cases hj : j = b
  · subst j
    simp [conditionalKet, ket]
  · simp [conditionalKet, ket, hj]

/-- Sanity: the final correction in B.14 cancels for identical inputs. -/
example (rho : Op A) (N : Superop A B) : differenceVariance rho rho N = 0 := by
  simp [differenceVariance, relativeEntropyDifference, relativeReal, channelAdjoint]

/-- Sanity: no output-state normalization is hidden in fidelity. -/
example : squaredFidelity (1 : Op Unit) (1 : Op Unit) = 1 := by
  have hs : cfc Real.sqrt (1 : Op Unit) = 1 := by
    simpa using (cfc_apply_one (R := ℝ) (A := Op Unit) (f := Real.sqrt))
  simp [squaredFidelity, rootFidelity, hs, Matrix.trace, Matrix.one_apply]

/-- Sanity: entropy at the identity has value zero in nats. -/
example : renyiEntropySupportNats 0 (1 : Op Unit) = 0 := by
  simp only [renyiEntropySupportNats, if_pos rfl, ite_true]
  apply supportPower_unit_zero (decEqUnit := Classical.decEq Unit)
  intro i j
  simp [Matrix.one_apply, Subsingleton.elim i j]

/-- Sanity: the ordinary endpoint is the imported von Neumann entropy. -/
example (rho : Op A) : renyiEntropySupportNats 1 rho = entropy rho := by
  simp [renyiEntropySupportNats, renyiEntropyNats]

/-- Sanity: a zero-q branch uses the chosen density, with the complex
trace coefficient needed on off-diagonal blocks of an entangled input. -/
example (fallback Z : Op A) {m : ℕ} (phi : Fin m → EuclideanSpace ℂ A) :
    measurementRecovery (0 : Op A) fallback phi Z =
      ∑ x, ((pureDensity (phi x) * Z).trace) • fallback := by
  simp [measurementRecovery, effectProb]

/-- Sanity: the fixed-reference support-projector expressions have value zero
on the zero matrix. This helper default is excluded by every state hypothesis. -/
example (a : ℝ) : fixedPetzCMI a (0 : Op (A × (B × C))) = 0 := by
  simp [fixedPetzCMI, supportPower, marginalAC, traceLeft, traceRight, embedAC, cfc_zero]

/-- PDF p.10: complete-output monotonicity under every finite adaptive LOCC
protocol, with arbitrary positive input/output dimensions and local memories. -/
def SquashedLOCC (a : ℝ) : Prop :=
  ∀ k l m n : ℕ, ∀ rho : Op (Fin (k+1) × Fin (l+1)), IsDensityMatrix rho →
    ∀ N : Superop (Fin (k+1) × Fin (l+1)) (Fin (m+1) × Fin (n+1)),
      FiniteLOCC N → renyiSquashed a (N rho) ≤ renyiSquashed a rho

/-- PDF p.10: convexity for all normalized finite ensembles. -/
def SquashedConvex (a : ℝ) : Prop :=
  ∀ (A B X : Type) [Fintype A] [Fintype B] [Fintype X]
    [Nonempty A] [Nonempty B] [Nonempty X] (p : X → ℝ) (rho : X → Op (A × B)),
    IsLaw p → (∀ x, IsDensityMatrix (rho x)) →
      renyiSquashed a (average rho p) ≤ ∑ x, (p x : EReal) * renyiSquashed a (rho x)

/-- PDF p.22, (5.47): cost of the specified EB recovery map, completed on
zero-probability branches with rho_A itself. -/
def discordRecoveryCost {m : ℕ} (rho : Op (A × B))
    (phi : Fin m → EuclideanSpace ℂ A) : EReal :=
  -extendedLog (squaredFidelity rho
    (applyFirstSuperop (measurementRecovery (traceRight rho) (traceRight rho) phi) rho))

end QAlgorithms.Papers.Independent.Intakenext100.P56


