-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39
-- name    : QAlgorithms_Papers_Independent_Support50_P39
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:57:15.169176+00:00
-- url     : https://prove2.me/theorems/3b4be886-10bb-4c3d-8379-08b97cc3d9eb
-- title:
--   Definitions for Classical capacity of a noiseless quantum channel assisted by noisy entanglement
-- statement:
--   The objects the formalized statements of *Classical capacity of a noiseless quantum channel assisted by noisy entanglement* (arXiv:quant-ph/0106080) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `noisyResourceCopies`: PDF pp.2--4: independent copies, regrouped as A^n:B^n, with all matrix entries, including off-diagonal entries, retained.
--   - `aliceAction`: PDF p.4: Lambda tensor id_B, with Alice the first factor. This is the linear action on every Bob block, rather than an action just on marginals.
--   - `clippedCoherentInformation`: PDF p.2: the paper's coherent information is clipped at zero.
--   - `quantumMutualInformation`: PDF p.8, Eq. (16): quantum mutual information in bits.
--   - `Preprocessing`: PDF pp.2,7: arbitrary positive block length and positive finite output dimension, with an actual CPTP map. Neither integer is bounded in the optimization.
--   - `processedResource`: PDF pp.2,7: the computed preprocessed resource, not a free state parameter.
--   - `mutualRatios`: PDF p.2, Eq. (4), on its actual domain S(A)>0. The missing unassisted baseline is supplied separately in the capacity theorem. For normalized density inputs this set contains 0 (mixed replacement output) and is contained in [0,2]. Invalid inputs are never used in theorems.
--   - `coherentRatios`: PDF p.7, Eq. (15): positive processed-entropy quotients of the clipped coherent information. The set contains 0 and is contained in [0,1] for states.
--   - `NoisyResourceBlockCode`: PDF p.3, Eq. (6): a finite protocol consuming nk copies and sending a register of dimension d^k. Every message has a CPTP encoder. The SINGLE POVM is chosen before the universal message quantifier. Local ancillas and disposal are subsumed by CPTP maps; no side communication or feedback is supplied.
--   - `FixedRate`: PDF p.3, Eq. (6): fixed-(d,n) achievable rate R, already normalized to bits per qubit. d,n are fixed BEFORE error and rate-slack limits. Arbitrary large block encoders are allowed; this is not an independent-letter restriction. Only positive k are tested, and epsilon ranges over (0,1).
--   - `operationalRates`: PDF p.3, Eq. (6): rates obtainable with one chosen d>=2 and n>=1. In finite positive dimensions the set contains [0,1] and is bounded by 2; these guards are included in the full capacity statement.
--   - `denseCodingCapacity`: PDF p.3, Eq. (6): operational capacity, in classical bits per qubit. This definition contains no entropic capacity identity. On nonphysical input the real supremum can have a junk value; all results require a density matrix.
--   - `ReliableFamily`: PDF p.3, Eq. (6): an arbitrary reliable fixed-(d,n) block family. Only the errors must converge; message lengths and rates may oscillate. Encoders and the common decoder are witnessed by NoisyResourceBlockCode at each positive k. This predicate is used only with d>=2 and n>=1.
--   - `IsEncoding`: PDF p.4, Eq. (9): an admissible finite ensemble of encoding channels.
--   - `encodingHolevo`: PDF p.4, Eqs. (8),(9): the Holevo score computed from an encoding ensemble. No clipping occurs in this per-ensemble expression.
--   - `denseCodingHolevoValue`: PDF p.4, RHS of Eq. (9): the finite-ensemble objective H_d, deliberately separate from the operational C_d in Eq. (6). It is nonempty and bounded for d>=1 and normalized input. Attainment is part of the optimization theorem.
--   - `finiteCoherentOpt`: PDF p.4, Eq. (10): the fixed-output-dimensional optimized clipped coherent information. For normalized input and d>=1 this is a nonempty, bounded real supremum, attained by an actual channel.
--   - `uniformWeight`: PDF p.5: probabilities d^(-2) on the d^2 encoding letters, used for d>=1.
--   - `unitaryEncoders`: PDF p.5: unitary encoders Ad(U_i) after a given preprocessing channel.
--   - `TracelessTwirling`: PDF p.5: the source's unnormalized traceless-matrix twirling property.
--   - `IsDistillable`: PDF p.3, citing Ref. 11 (quant-ph/9801069, Eqs. (4)--(10) and the necessary-and-sufficient criterion following Eq. (9)): distillability means some positive finite tensor power has an entangled two-qubit local-filter output. Filters are arbitrary linear maps: they can be rescaled to physical Kraus contractions without changing positivity of the trace or the PPT test. In 2x2, failure of the PPT test is exactly inseparability. Transposing Alice instead of Bob gives the same positivity test by full transposition.
--   - `IsBoundEntangled`: PDF p.3: bound entangled means normalized, entangled AND nondistillable; this is not restricted to PPT states or to no-communication distillation.
--   - `productFactor`: PDF p.6, Bennett's example: tau tensor sigma regrouped as (T,A):B. Alice owns both T and A.
--   - `discardFirstAlice`: PDF p.6: actually discard T, one part of Alice's register.
-- source:
--   Classical capacity of a noiseless quantum channel assisted by noisy entanglement, arXiv:quant-ph/0106080v3, https://arxiv.org/abs/quant-ph/0106080v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Horodecki--Horodecki--Horodecki--Leung--Terhal, arXiv:quant-ph/0106080v3.
All page references are PDF pages; all entropies and rates are in bits.
The operational capacity below is defined from actual worst-message block codes,
not from an entropy formula or the unregularized Holevo objective.

Source corrections: Eq. (3) needs the unassisted baseline when Eq. (4) is
restricted to its positive-denominator domain; Eq. (5) needs the processed
Alice entropy from Eq. (15), rather than the printed S(rho_A). These corrections
require independent moderation; see the unit's DISCREPANCIES.md.
The fixed-(d,n) operational/single-letter identification in Eqs. (7),(9)
is deferred and is not an assumption of any declaration here.
-/

namespace QAlgorithms.Papers.Independent.Support50.P39

/-! Accepted-library comparison for this repair: the four original short names
matched different frozen concepts, not reusable definitions of these objects.
Dependency50.P45.resourceCopies is a tensor power of a pure vector, whereas
noisyResourceCopies takes an arbitrary mixed density matrix. Information100.P39
coherentInformation is signed Renyi information in nats; Information100.P22
coherentInformation takes a channel and a purified input. Neither is the paper's
clipped bipartite entropy difference in bits. Frontier30.P06.BlockCode describes
feedback executions with average error, whereas NoisyResourceBlockCode uses a
fixed noisy resource, no feedback, and worst-message success. Claimed50.P13
finiteHolevo is an extended nonnegative relative-entropy score of one ensemble,
whereas denseCodingHolevoValue optimizes all finite CPTP encoding ensembles into
a fixed finite output dimension. These complete paper-local bodies are retained
under distinct names; no frozen definition or theorem meaning is changed. -/

noncomputable section

open QAlgorithms
open Filter Topology
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--4: independent copies, regrouped as A^n:B^n, with all
matrix entries, including off-diagonal entries, retained. -/
def noisyResourceCopies {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun i j => ∏ t, rho (i.1 t, i.2 t) (j.1 t, j.2 t)

/-- PDF p.4: Lambda tensor id_B, with Alice the first factor. This is the
linear action on every Bob block, rather than an action just on marginals. -/
def aliceAction {A B C : Type*} (Phi : Superop A C) :
    Superop (A × B) (C × B) :=
  fun X i j => Phi (fun a a2 => X (a,i.2) (a2,j.2)) i.1 j.1

/-- PDF p.2: the paper's coherent information is clipped at zero. -/
def clippedCoherentInformation {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  max (vnEntropy (traceLeft rho) - vnEntropy rho) 0

/-- PDF p.8, Eq. (16): quantum mutual information in bits. -/
def quantumMutualInformation {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy (traceRight rho) + vnEntropy (traceLeft rho) - vnEntropy rho

/-- PDF pp.2,7: arbitrary positive block length and positive finite output
dimension, with an actual CPTP map. Neither integer is bounded in the optimization. -/
structure Preprocessing (A : Type*) [Fintype A] [DecidableEq A] where
  copies : ℕ
  copies_pos : 0 < copies
  outputDim : ℕ
  outputDim_pos : 0 < outputDim
  channel : Superop (Fin copies → A) (Fin outputDim)
  valid : IsChannel channel

/-- PDF pp.2,7: the computed preprocessed resource, not a free state parameter. -/
def processedResource {A B : Type*} [Fintype A] [DecidableEq A]
    (rho : Matrix (A × B) (A × B) ℂ) (P : Preprocessing A) :
    Matrix (Fin P.outputDim × (Fin P.copies → B))
      (Fin P.outputDim × (Fin P.copies → B)) ℂ :=
  aliceAction P.channel (noisyResourceCopies rho P.copies)

/-- PDF p.2, Eq. (4), on its actual domain S(A)>0.
The missing unassisted baseline is supplied separately in the capacity theorem.
For normalized density inputs this set contains 0 (mixed replacement output)
and is contained in [0,2]. Invalid inputs are never used in theorems. -/
def mutualRatios {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : Set ℝ :=
  {r | ∃ P : Preprocessing A,
    0 < vnEntropy (traceRight (processedResource rho P)) ∧
    r = quantumMutualInformation (processedResource rho P) /
      vnEntropy (traceRight (processedResource rho P))}

/-- PDF p.7, Eq. (15): positive processed-entropy quotients of the clipped
coherent information. The set contains 0 and is contained in [0,1] for states. -/
def coherentRatios {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : Set ℝ :=
  {r | ∃ P : Preprocessing A,
    0 < vnEntropy (traceRight (processedResource rho P)) ∧
    r = clippedCoherentInformation (processedResource rho P) /
      vnEntropy (traceRight (processedResource rho P))}

/-- PDF p.3, Eq. (6): a finite protocol consuming nk copies and sending a
register of dimension d^k. Every message has a CPTP encoder. The SINGLE POVM
is chosen before the universal message quantifier. Local ancillas and disposal
are subsumed by CPTP maps; no side communication or feedback is supplied. -/
def NoisyResourceBlockCode {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (d n k m : ℕ) (epsilon : ℝ) : Prop :=
  ∃ Enc : Qubits m → Superop (Fin (n*k) → A) (Fin (d^k)),
    (∀ x, IsChannel (Enc x)) ∧
    ∃ Dec : Qubits m → Matrix (Fin (d^k) × (Fin (n*k) → B))
      (Fin (d^k) × (Fin (n*k) → B)) ℂ,
      IsPOVM Dec ∧ ∀ x, 1-epsilon ≤
        effectProb (Dec x) (aliceAction (Enc x) (noisyResourceCopies rho (n*k)))

/-- PDF p.3, Eq. (6): fixed-(d,n) achievable rate R, already normalized to
bits per qubit. d,n are fixed BEFORE error and rate-slack limits. Arbitrary
large block encoders are allowed; this is not an independent-letter restriction.
Only positive k are tested, and epsilon ranges over (0,1). -/
def FixedRate {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (d n : ℕ) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      ∃ m : ℕ, (R-delta) * (k : ℝ) * Real.logb 2 d ≤ m ∧
        NoisyResourceBlockCode rho d n k m epsilon

/-- PDF p.3, Eq. (6): rates obtainable with one chosen d>=2 and n>=1.
In finite positive dimensions the set contains [0,1] and is bounded by 2;
these guards are included in the full capacity statement. -/
def operationalRates {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : Set ℝ :=
  {R | ∃ d n : ℕ, 2 ≤ d ∧ 0 < n ∧ FixedRate rho d n R}

/-- PDF p.3, Eq. (6): operational capacity, in classical bits per qubit.
This definition contains no entropic capacity identity. On nonphysical input
the real supremum can have a junk value; all results require a density matrix. -/
def denseCodingCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup (operationalRates rho)

/-- PDF p.3, Eq. (6): an arbitrary reliable fixed-(d,n) block family.
Only the errors must converge; message lengths and rates may oscillate.
Encoders and the common decoder are witnessed by NoisyResourceBlockCode at each positive k.
This predicate is used only with d>=2 and n>=1. -/
def ReliableFamily {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (d n : ℕ) (m : ℕ → ℕ) (epsilon : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, 0 < k → 0 ≤ epsilon k ∧ epsilon k ≤ 1 ∧
    NoisyResourceBlockCode rho d n k (m k) (epsilon k)) ∧
    Tendsto epsilon atTop (nhds 0)

/-- PDF p.4, Eq. (9): an admissible finite ensemble of encoding channels. -/
def IsEncoding {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A]
    {l : ℕ} (p : Fin l → ℝ) (E : Fin l → Superop A C) : Prop :=
  0 < l ∧ (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ ∀ i, IsChannel (E i)

/-- PDF p.4, Eqs. (8),(9): the Holevo score computed from an encoding ensemble.
No clipping occurs in this per-ensemble expression. -/
def encodingHolevo {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] {l : ℕ}
    (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ)
    (p : Fin l → ℝ) (E : Fin l → Superop (Fin n → A) C) : ℝ :=
  vnEntropy (∑ i, (p i : ℂ) • aliceAction (E i) (noisyResourceCopies rho n)) -
    ∑ i, p i * vnEntropy (aliceAction (E i) (noisyResourceCopies rho n))

/-- PDF p.4, RHS of Eq. (9): the finite-ensemble objective H_d, deliberately
separate from the operational C_d in Eq. (6). It is nonempty and bounded for
d>=1 and normalized input. Attainment is part of the optimization theorem. -/
def denseCodingHolevoValue {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (n d : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ l : ℕ, ∃ p : Fin l → ℝ,
    ∃ E : Fin l → Superop (Fin n → A) (Fin d),
      IsEncoding p E ∧ r = encodingHolevo rho n p E}

/-- PDF p.4, Eq. (10): the fixed-output-dimensional optimized clipped
coherent information. For normalized input and d>=1 this is a nonempty,
bounded real supremum, attained by an actual channel. -/
def finiteCoherentOpt {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (n d : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ Phi : Superop (Fin n → A) (Fin d), IsChannel Phi ∧
    r = clippedCoherentInformation (aliceAction Phi (noisyResourceCopies rho n))}

/-- PDF p.5: probabilities d^(-2) on the d^2 encoding letters, used for d>=1. -/
def uniformWeight (d : ℕ) : Fin (d*d) → ℝ := fun _ => ((d : ℝ)^2)⁻¹

/-- PDF p.5: unitary encoders Ad(U_i) after a given preprocessing channel. -/
def unitaryEncoders {A : Type*} [Fintype A] {d : ℕ}
    (Phi : Superop A (Fin d)) (U : Fin (d*d) → Matrix.unitaryGroup (Fin d) ℂ) :
    Fin (d*d) → Superop A (Fin d) :=
  fun i => conjSuperop (U i : Matrix (Fin d) (Fin d) ℂ) ∘ Phi

/-- PDF p.5: the source's unnormalized traceless-matrix twirling property. -/
def TracelessTwirling {d : ℕ} (U : Fin (d*d) → Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  ∀ M : Matrix (Fin d) (Fin d) ℂ, M.trace = 0 →
    ∑ i, conjSuperop (U i : Matrix (Fin d) (Fin d) ℂ) M = 0

/-- PDF p.3, citing Ref. 11 (quant-ph/9801069, Eqs. (4)--(10) and the
necessary-and-sufficient criterion following Eq. (9)): distillability means
some positive finite tensor power has an entangled two-qubit local-filter
output. Filters are arbitrary linear maps: they can be rescaled to physical
Kraus contractions without changing positivity of the trace or the PPT test.
In 2x2, failure of the PPT test is exactly inseparability. Transposing Alice
instead of Bob gives the same positivity test by full transposition. -/
def IsDistillable {A B : Type*} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ n : ℕ, 0 < n ∧
    ∃ F : Matrix (Fin 2) (Fin n → A) ℂ,
    ∃ G : Matrix (Fin 2) (Fin n → B) ℂ,
      let X := Matrix.kronecker F G * noisyResourceCopies rho n * (Matrix.kronecker F G)ᴴ
      0 < X.trace.re ∧ ¬ (QAlgorithms.Entanglement.partialTransposeFirst X).PosSemidef

/-- PDF p.3: bound entangled means normalized, entangled AND nondistillable;
this is not restricted to PPT states or to no-communication distillation. -/
def IsBoundEntangled {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ) : Prop :=
  IsDensityMatrix rho ∧ ¬ QAlgorithms.Entanglement.IsSeparableDensity rho ∧
    ¬ IsDistillable rho

/-- PDF p.6, Bennett's example: tau tensor sigma regrouped as (T,A):B.
Alice owns both T and A. -/
def productFactor {T A B : Type*} (tau : Matrix T T ℂ)
    (sigma : Matrix (A × B) (A × B) ℂ) :
    Matrix ((T × A) × B) ((T × A) × B) ℂ :=
  fun i j => tau i.1.1 j.1.1 * sigma (i.1.2,i.2) (j.1.2,j.2)

/-- PDF p.6: actually discard T, one part of Alice's register. -/
def discardFirstAlice {T A B : Type*} [Fintype T]
    (rho : Matrix ((T × A) × B) ((T × A) × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun i j => ∑ t, rho ((t,i.1),i.2) ((t,j.1),j.2)

/-- Sanity: no resource copies is the scalar unit, not a zero state. -/
example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ)
    (i j : (Fin 0 → A) × (Fin 0 → B)) : noisyResourceCopies rho 0 i j = 1 := by
  simp [noisyResourceCopies]

/-- Sanity: applying the identity to Alice retains every off-diagonal entry. -/
example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) :
    aliceAction (fun X : Matrix A A ℂ => X) rho = rho := rfl

/-- Sanity: a one-letter channel ensemble has normalized weights. -/
example {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A]
    (Phi : Superop A C) (hPhi : IsChannel Phi) :
    IsEncoding (fun _ : Fin 1 => (1 : ℝ)) (fun _ => Phi) := by
  simp [IsEncoding, hPhi]

/-- Sanity: the scalar-output unitary ensemble has one letter of weight one. -/
example : uniformWeight 1 0 = 1 := by norm_num [uniformWeight]

/-- Sanity: the clipping convention keeps negative signed coherent information at zero. -/
example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ)
    (h : vnEntropy (traceLeft rho) ≤ vnEntropy rho) : clippedCoherentInformation rho = 0 := by
  exact max_eq_right (sub_nonpos.mpr h)

/-- Sanity: discarding a scalar Alice factor returns precisely sigma. -/
example {A B : Type*} (sigma : Matrix (A × B) (A × B) ℂ) :
    discardFirstAlice (productFactor (1 : Matrix Unit Unit ℂ) sigma) = sigma := by
  ext i j
  simp [discardFirstAlice, productFactor]

end

end QAlgorithms.Papers.Independent.Support50.P39


