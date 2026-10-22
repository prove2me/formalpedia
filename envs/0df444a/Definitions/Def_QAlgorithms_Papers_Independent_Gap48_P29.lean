-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29
-- name    : QAlgorithms_Papers_Independent_Gap48_P29
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T04:09:08.317519+00:00
-- url     : https://prove2.me/theorems/0f3af1c7-b2bb-4000-b8ff-e7a7728401b1
-- title:
--   Definitions for On Quantum Fidelities and Channel Capacities
-- statement:
--   The objects the formalized statements of *On Quantum Fidelities and Channel Capacities* (arXiv:quant-ph/9809010) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Represents`: PDF p.2, Eq.(1): an operator-sum representation, with equality on all matrices.
--   - `FiniteCPMap`: PDF pp.1--2: adapt the accepted complete-positivity predicate to unbundled superoperators, preserving its linear map on EVERY matrix and every amplification. No trace constraint is imposed.
--   - `TraceNonincreasingCPMap`: PDF p.2, Eqs.(1)--(2): a CP trace-nonincreasing operation.
--   - `fe`: PDF p.2, Eq.(11), expanded through matrix units to make Fe independent of a chosen Kraus representation. This equals sum_a |Tr(K_a rho)|^2 for every CP map. There is no division by the output trace.
--   - `operatorFe`: PDF p.2, single-operator convention following Eq.(6): Fe(rho,{B}).
--   - `projectionDimension`: PDF pp.2--3: actual range dimension, counting every eigenvalue multiplicity.
--   - `IsPartialIsometry`: PDF p.2: the partial-isometry identity WW†W=W (equivalent to projector initial and final spaces); rectangular matrices permit either order of dimensions.
--   - `IsMaximalPartialIsometry`: PDF p.2: a maximal partial isometry fills the smaller of its two spaces.
--   - `SourceRegister`: PDF p.3: the coordinate index of n tensor factors of a d-dimensional space.
--   - `BlockQuantumSource`: PDF p.3, before Eq.(12): a source is an arbitrary sequence of block density matrices on tensor powers of one nonzero finite single-letter Hilbert space. The unique zero-block state is harmless; all quantitative bounds use positive n.
--   - `sourceEntropyRate`: PDF p.3, Eq.(12): limsup entropy rate. The sequence is bounded between zero and log2(dimension), so the real limsup has no empty/unbounded default.
--   - `qaepSpectralProjector`: PDF p.3, Eq.(19): full spectral projector for the CLOSED typical window.
--   - `qaepRetainedMass`: PDF p.3, Eq.(21): retained probability.
--   - `QAEP`: PDF p.3, Definition 1: all positive spectral windows and all positive mass errors, with the eventual threshold after both tolerances. No iid assumption.
--   - `typicalRestriction`: PDF p.6, Eq.(53): normalized typical restriction; used only with retained mass positive (or eventually positive by QAEP). Its total zero-mass value is zero.
--   - `IsCompression`: PDF p.6, Eq.(50): compression into a projector range, containing the exact projection branch plus another CP branch, and trace preserving overall.
--   - `SourceTransmissionCode`: PDF p.3, Eq.(14): actual physical encoders and decoders, without assistance.
--   - `SourceTransmissionCode.effective`: PDF p.3, Eqs.(13)--(15): decoding after independent channel uses after encoding.
--   - `Reliable`: PDF p.3, Eq.(15): entanglement reliability for a specified source and code.
--   - `Transmissible`: PDF p.3, Eq.(15): existence of a reliable physical code.
--   - `SubspaceReliable`: PDF p.3, Eqs.(16),(18): uniform fidelity on ALL normalized superpositions in a family of subspaces. For channel families this is exactly convergence of Fp to one.
--   - `subspaceRate`: PDF p.3, Eq.(17): limsup logarithmic subspace dimension per use.
--   - `SubspaceAchievable`: PDF p.3, Eqs.(17)--(18): transmitted subspaces in channel-input tensor powers, with a single code acting uniformly on the whole subspace.
--   - `qe`: PDF pp.1,3: entanglement capacity restricted to the paper's QAEP source class. For nonzero finite-dimensional channels the set is nonempty and bounded by log2 c.
--   - `qs`: PDF p.3: subspace capacity, with the source's LIMSUP rate convention. The set is nonempty and bounded for nonzero finite-dimensional channels.
--   - `ForwardCode`: PDF p.11, Eq.(97): arbitrary finitely many forward messages at each block size. Encodings are CP TNI branches summing to a TP channel; each decoder is TP. There is no feedback or pre-shared entanglement in this model.
--   - `ForwardReliable`: PDF p.11, Eq.(98): sum UNNORMALIZED branch fidelities, which includes the branch probabilities, rather than an unweighted average of normalized fidelities.
--   - `qeForward`: PDF p.11: entanglement capacity with forward classical communication.
--   - `uniformOn`: PDF p.9, Corollary 1: uniform state on a nonzero projector range.
--   - `coherentBlockMaximum`: PDF p.12, Eq.(113): maximum over ALL block input densities, including entangled ones. The continuous finite-dimensional objective attains this bounded supremum.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, https://arxiv.org/abs/quant-ph/9809010v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

/-!
Statements from Barnum--Knill--Nielsen, arXiv:quant-ph/9809010v1.
All Hilbert spaces are nonzero finite dimensional coordinate spaces. Block registers
are tensor powers of a fixed single-letter space, including correlated sources.
Entropy and logarithms are in bits; fidelity is squared and unrenormalized.
Lemmas 3 and 4 are deferred because their printed estimates are false.
Compilation is pending the explicitly requested batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.2, Eq.(1): an operator-sum representation, with equality on all matrices. -/
def Represents {I J : Type*} [Fintype I] {m : ℕ}
    (K : Fin m → Matrix J I ℂ) (A : Superop I J) : Prop :=
  ∀ X, A X = krausApply K X

/-- PDF pp.1--2: adapt the accepted complete-positivity predicate to unbundled
superoperators, preserving its linear map on EVERY matrix and every amplification.
No trace constraint is imposed. -/
def FiniteCPMap {I J : Type*} [Fintype I] [Fintype J] (A : Superop I J) : Prop :=
  ∃ L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ,
    (∀ X, L X = A X) ∧ QAlgorithms.Entanglement.IsCompletelyPositive L

/-- PDF p.2, Eqs.(1)--(2): a CP trace-nonincreasing operation. -/
def TraceNonincreasingCPMap {I J : Type*} [Fintype I] [Fintype J] (A : Superop I J) : Prop :=
  FiniteCPMap A ∧ ∀ X, X.PosSemidef → (A X).trace.re ≤ X.trace.re

/-- PDF p.2, Eq.(11), expanded through matrix units to make Fe independent of a
chosen Kraus representation. This equals sum_a |Tr(K_a rho)|^2 for every CP map.
There is no division by the output trace. -/
def fe {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (A : Superop I I) : ℝ :=
  (∑ i, ∑ j, ∑ k, ∑ l,
    rho j i * conj (rho l k) * A (Matrix.single j l 1) i k).re

/-- PDF p.2, single-operator convention following Eq.(6): Fe(rho,{B}). -/
def operatorFe {I : Type*} [Fintype I] (rho B : Matrix I I ℂ) : ℝ :=
  Complex.normSq (B * rho).trace

/-- PDF pp.2--3: actual range dimension, counting every eigenvalue multiplicity. -/
def projectionDimension {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin P))

/-- PDF p.2: the partial-isometry identity WW†W=W (equivalent to projector initial
and final spaces); rectangular matrices permit either order of dimensions. -/
def IsPartialIsometry {I J : Type*} [Fintype I] [Fintype J]
    (W : Matrix J I ℂ) : Prop := W * Wᴴ * W = W

/-- PDF p.2: a maximal partial isometry fills the smaller of its two spaces. -/
def IsMaximalPartialIsometry {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (W : Matrix J I ℂ) : Prop :=
  IsPartialIsometry W ∧ (Wᴴ * W = 1 ∨ W * Wᴴ = 1)

/-- PDF p.3: the coordinate index of n tensor factors of a d-dimensional space. -/
abbrev SourceRegister (d n : ℕ) := Fin n → Fin d

/-- PDF p.3, before Eq.(12): a source is an arbitrary sequence of block density
matrices on tensor powers of one nonzero finite single-letter Hilbert space.
The unique zero-block state is harmless; all quantitative bounds use positive n. -/
structure BlockQuantumSource where
  dimension : ℕ
  dimension_pos : 0 < dimension
  rho : (n : ℕ) → Matrix (SourceRegister dimension n) (SourceRegister dimension n) ℂ
  density : ∀ n, IsDensityMatrix (rho n)

/-- PDF p.3, Eq.(12): limsup entropy rate. The sequence is bounded between zero and
log2(dimension), so the real limsup has no empty/unbounded default. -/
def sourceEntropyRate (S : BlockQuantumSource) : ℝ :=
  Filter.limsup (fun n : ℕ => vnEntropy (S.rho n) / (n : ℝ)) atTop

/-- PDF p.3, Eq.(19): full spectral projector for the CLOSED typical window. -/
def qaepSpectralProjector (S : BlockQuantumSource) (window : ℝ) (n : ℕ) :
    Matrix (SourceRegister S.dimension n) (SourceRegister S.dimension n) ℂ :=
  cfc (fun x : ℝ => if (2 : ℝ) ^ (-(n : ℝ) * (sourceEntropyRate S + window)) ≤ x ∧
      x ≤ (2 : ℝ) ^ (-(n : ℝ) * (sourceEntropyRate S - window)) then 1 else 0) (S.rho n)

/-- PDF p.3, Eq.(21): retained probability. -/
def qaepRetainedMass (S : BlockQuantumSource) (window : ℝ) (n : ℕ) : ℝ :=
  ((qaepSpectralProjector S window n * S.rho n * qaepSpectralProjector S window n).trace).re

/-- PDF p.3, Definition 1: all positive spectral windows and all positive mass
errors, with the eventual threshold after both tolerances. No iid assumption. -/
def QAEP (S : BlockQuantumSource) : Prop :=
  ∀ window > (0 : ℝ), ∀ delta > (0 : ℝ),
    ∀ᶠ n : ℕ in atTop, 1 - delta < qaepRetainedMass S window n

/-- PDF p.6, Eq.(53): normalized typical restriction; used only with retained mass
positive (or eventually positive by QAEP). Its total zero-mass value is zero. -/
def typicalRestriction (S : BlockQuantumSource) (window : ℝ) (n : ℕ) :
    Matrix (SourceRegister S.dimension n) (SourceRegister S.dimension n) ℂ :=
  ((qaepRetainedMass S window n : ℂ)⁻¹) •
    (qaepSpectralProjector S window n * S.rho n * qaepSpectralProjector S window n)

/-- PDF p.6, Eq.(50): compression into a projector range, containing the exact
projection branch plus another CP branch, and trace preserving overall. -/
def IsCompression {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (C : Superop I I) : Prop :=
  IsChannel C ∧ (∃ G : Superop I I, FiniteCPMap G ∧
    ∀ X, C X = conjSuperop P X + G X) ∧ ∀ X, P * C X * P = C X

/-- PDF p.3, Eq.(14): actual physical encoders and decoders, without assistance. -/
structure SourceTransmissionCode (S : BlockQuantumSource) (c o : ℕ) where
  enc : (n : ℕ) → Superop (SourceRegister S.dimension n) (SourceRegister c n)
  dec : (n : ℕ) → Superop (SourceRegister o n) (SourceRegister S.dimension n)
  enc_channel : ∀ n, IsChannel (enc n)
  dec_channel : ∀ n, IsChannel (dec n)

/-- PDF p.3, Eqs.(13)--(15): decoding after independent channel uses after encoding. -/
def SourceTransmissionCode.effective {S : BlockQuantumSource} {c o : ℕ} (C : SourceTransmissionCode S c o)
    (N : Superop (Fin c) (Fin o)) (n : ℕ) :
    Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n) :=
  C.dec n ∘ piSuperop (fun _ : Fin n => N) ∘ C.enc n

/-- PDF p.3, Eq.(15): entanglement reliability for a specified source and code. -/
def Reliable {S : BlockQuantumSource} {c o : ℕ} (N : Superop (Fin c) (Fin o))
    (C : SourceTransmissionCode S c o) : Prop :=
  Tendsto (fun n => fe (S.rho n) (C.effective N n)) atTop (nhds 1)

/-- PDF p.3, Eq.(15): existence of a reliable physical code. -/
def Transmissible (S : BlockQuantumSource) {c o : ℕ} (N : Superop (Fin c) (Fin o)) : Prop :=
  ∃ C : SourceTransmissionCode S c o, Reliable N C

/-- PDF p.3, Eqs.(16),(18): uniform fidelity on ALL normalized superpositions in
a family of subspaces. For channel families this is exactly convergence of Fp to one. -/
def SubspaceReliable {d : ℕ}
    (P : (n : ℕ) → Matrix (SourceRegister d n) (SourceRegister d n) ℂ)
    (A : (n : ℕ) → Superop (SourceRegister d n) (SourceRegister d n)) : Prop :=
  ∀ epsilon > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ psi : EuclideanSpace ℂ (SourceRegister d n), ‖psi‖ = 1 → act (P n) psi = psi →
      1 - epsilon ≤ effectProb (pureDensity psi) (A n (pureDensity psi))

/-- PDF p.3, Eq.(17): limsup logarithmic subspace dimension per use. -/
def subspaceRate {d : ℕ}
    (P : (n : ℕ) → Matrix (SourceRegister d n) (SourceRegister d n) ℂ) : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (projectionDimension (P n) : ℝ) / n) atTop

/-- PDF p.3, Eqs.(17)--(18): transmitted subspaces in channel-input tensor powers,
with a single code acting uniformly on the whole subspace. -/
def SubspaceAchievable {c o : ℕ} (N : Superop (Fin c) (Fin o)) (R : ℝ) : Prop :=
  ∃ S : BlockQuantumSource, S.dimension = c ∧ ∃ C : SourceTransmissionCode S c o,
    ∃ P : (n : ℕ) → Matrix (SourceRegister S.dimension n) (SourceRegister S.dimension n) ℂ,
      (∀ n, IsProjection (P n) ∧ 0 < projectionDimension (P n)) ∧
      subspaceRate P = R ∧ SubspaceReliable P (C.effective N)

/-- PDF pp.1,3: entanglement capacity restricted to the paper's QAEP source class.
For nonzero finite-dimensional channels the set is nonempty and bounded by log2 c. -/
def qe {c o : ℕ} (N : Superop (Fin c) (Fin o)) : ℝ :=
  sSup {R : ℝ | ∃ S : BlockQuantumSource, QAEP S ∧ sourceEntropyRate S = R ∧ Transmissible S N}

/-- PDF p.3: subspace capacity, with the source's LIMSUP rate convention. The set
is nonempty and bounded for nonzero finite-dimensional channels. -/
def qs {c o : ℕ} (N : Superop (Fin c) (Fin o)) : ℝ :=
  sSup {R : ℝ | SubspaceAchievable N R}

/-- PDF p.11, Eq.(97): arbitrary finitely many forward messages at each block size.
Encodings are CP TNI branches summing to a TP channel; each decoder is TP.
There is no feedback or pre-shared entanglement in this model. -/
structure ForwardCode (S : BlockQuantumSource) (c o : ℕ) where
  messages : ℕ → ℕ
  enc : (n : ℕ) → Fin (messages n) → Superop (SourceRegister S.dimension n) (SourceRegister c n)
  dec : (n : ℕ) → Fin (messages n) → Superop (SourceRegister o n) (SourceRegister S.dimension n)
  enc_operation : ∀ n m, TraceNonincreasingCPMap (enc n m)
  enc_channel : ∀ n, IsChannel (fun X => ∑ m, enc n m X)
  dec_channel : ∀ n m, IsChannel (dec n m)

/-- PDF p.11, Eq.(98): sum UNNORMALIZED branch fidelities, which includes the
branch probabilities, rather than an unweighted average of normalized fidelities. -/
def ForwardReliable {S : BlockQuantumSource} {c o : ℕ} (N : Superop (Fin c) (Fin o))
    (C : ForwardCode S c o) : Prop :=
  Tendsto (fun n => ∑ m, fe (S.rho n)
    (C.dec n m ∘ piSuperop (fun _ : Fin n => N) ∘ C.enc n m)) atTop (nhds 1)

/-- PDF p.11: entanglement capacity with forward classical communication. -/
def qeForward {c o : ℕ} (N : Superop (Fin c) (Fin o)) : ℝ :=
  sSup {R : ℝ | ∃ S : BlockQuantumSource, QAEP S ∧ sourceEntropyRate S = R ∧
    ∃ C : ForwardCode S c o, ForwardReliable N C}

/-- PDF p.9, Corollary 1: uniform state on a nonzero projector range. -/
def uniformOn {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) : Matrix I I ℂ :=
  ((projectionDimension P : ℂ)⁻¹) • P

/-- PDF p.12, Eq.(113): maximum over ALL block input densities, including entangled
ones. The continuous finite-dimensional objective attains this bounded supremum. -/
def coherentBlockMaximum {c o : ℕ} (N : Superop (Fin c) (Fin o)) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ rho : Matrix (SourceRegister c n) (SourceRegister c n) ℂ,
    IsDensityMatrix rho ∧ QAlgorithms.Papers.Independent.Information100.P22.coherentInformation
      (piSuperop (fun _ : Fin n => N)) rho = r}

/-- Sanity: zero operation has zero unrenormalized entanglement fidelity. -/
example {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    fe rho (fun _ => 0) = 0 := by simp [fe]

/-- Sanity: the zero Kraus operator is an allowed CP operation, including Fe=0. -/
example {I J : Type*} [Fintype I] [Fintype J] :
    FiniteCPMap (fun _ : Matrix I I ℂ => (0 : Matrix J J ℂ)) := by
  refine ⟨0, (by intro X; rfl), ?_⟩
  intro r X _
  change (0 : Matrix (Fin r × J) (Fin r × J) ℂ).PosSemidef
  exact Matrix.PosSemidef.zero

/-- Sanity: identity is a maximal partial isometry, including equal dimensions. -/
example {I : Type*} [Fintype I] [DecidableEq I] :
    IsMaximalPartialIsometry (1 : Matrix I I ℂ) := by
  simp [IsMaximalPartialIsometry, IsPartialIsometry]

/-- Sanity: Eq.(11) in dimension one is |rho|^2 times the scalar operation. -/
example : fe (1 : Matrix (Fin 1) (Fin 1) ℂ) (fun X => X) = 1 := by
  simp [fe, Matrix.single, Matrix.one_apply]

/-- Sanity: the zero subspace has no uniform-state probability mass. -/
example {I : Type*} [Fintype I] [DecidableEq I] :
    uniformOn (0 : Matrix I I ℂ) = 0 := by simp [uniformOn]

end QAlgorithms.Papers.Independent.Gap48.P29


