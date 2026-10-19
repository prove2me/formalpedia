-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P03
-- name    : QAlgorithms_Papers_Independent_Dependency50_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T07:48:25.112116+00:00
-- url     : https://prove2.me/theorems/79e35ba8-26ab-4cd9-9163-57d6b5b06ac1
-- title:
--   Definitions for Trading classical communication, quantum communication, and entanglement in quantum Shannon theory
-- statement:
--   The objects the formalized statements of *Trading classical communication, quantum communication, and entanglement in quantum Shannon theory* (arXiv:0901.3038) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AssistedQuantumCode`: PDF p.24: a rectangular instrument from A1 TA to the n channel inputs, with classical outcome M and discarded Kraus label L. The latter is retained explicitly so the common refinement on p.25 is a constructed state. Completeness is the actual trace-preservation equation, not a converse or an entropy bound. Any finite instrument can be represented with a common finite Kraus alphabet by padding branches with zero operators. All physical registers have positive dimension. Local ancillas and private randomness are absorbed in the Kraus map. Bob's decoder is conditional on M and is CPTP on B^n TB.
--   - `encoderVector`: PDF pp.24–25: the unnormalized pure branch on R TB A'^n obtained by applying K to Alice's halves of independent maximally entangled pairs of Schmidt ranks r and t. Its squared norm is the branch probability. Registers R and TB are untouched. The code's positivity guards the square root/division. Zero-probability Kraus branches remain present.
--   - `channelBranch`: PDF p.24, (106): apply exactly n independent uses of N to a pure encoder branch, leaving the reference R TB unchanged. The tensor channel acts on all operator blocks, including off-diagonal and correlated inputs.
--   - `codeState`: PDF p.24, (106): the actual code-induced cq state omega on A M B^n, where A = R TB. The classical M blocks are diagonal; all Kraus labels have been summed out. This state is computed, never supplied as free theorem data.
--   - `refinedCodeState`: PDF p.25: sigma on A X B^n with the single common classical refinement X = (M,L). Measuring the discarded Kraus environment in its defining basis is implemented by retaining its label. Each pre-channel branch is the pure vector encoderVector; no finite alphabet or reference bound is imposed. Zero-probability outcomes are retained.
--   - `marginalAX`: PDF p.25: the AX marginal of a state on A X B, tracing out B.
--   - `mutualAXB`: PDF p.25: I(AX;B) = H(AX) + H(B) - H(AXB), in bits. Only constructed normalized states are used in the theorem.
--   - `coherentABX`: PDF p.25: I(A>B X) = H(BX) - H(ABX), in bits. The joint entropy uses A X B order; entropy is invariant under the BX/XB swap.
--   - `decodedState`: PDF p.24, the conditional decoder in Fig.10: reorder each M diagonal block as R (B^n TB), apply id_R tensor D_m, and sum over M. There is no backward communication and no free additional nonlocal resource.
--   - `idealEntangled`: PDF p.24: the ideal maximally entangled vector of Schmidt rank d, (|00> + ... + |d-1,d-1>)/sqrt(d). The code requires d > 0.
--   - `quantumSize`: PDF pp.24–25: the block quantum message size log_2 dim R.
--   - `classicalSize`: PDF pp.24–25: the block noiseless classical cost log_2 dim M.
--   - `entanglementSize`: PDF pp.24–25: the block entanglement cost log_2 dim TB.
-- source:
--   Trading classical communication, quantum communication, and entanglement in quantum Shannon theory, arXiv:0901.3038v3, https://arxiv.org/abs/0901.3038v3

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
# Trading communication and entanglement: Appendix F

Source: Hsieh and Wilde, arXiv:0901.3038v3, PDF pp.24–25.
Only the finite-block result has a statement in this draft. The other assigned
nodes, including all three capacity equalities, are explicitly deferred in the
unit's HARD.md and GAPS.json. No operational capacity is defined by an entropy
formula. All new definitions below belong solely to this paper.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P03

open scoped Matrix ComplexConjugate

/-- PDF p.24: a rectangular instrument from A1 TA to the n channel inputs,
with classical outcome M and discarded Kraus label L. The latter is retained
explicitly so the common refinement on p.25 is a constructed state. Completeness
is the actual trace-preservation equation, not a converse or an entropy bound.
Any finite instrument can be represented with a common finite Kraus alphabet
by padding branches with zero operators. All physical registers have positive
dimension. Local ancillas and private randomness are absorbed in the Kraus map.
Bob's decoder is conditional on M and is CPTP on B^n TB. -/
structure AssistedQuantumCode (inputDim outputDim n : ℕ) where
  refDim : ℕ
  refDim_pos : 0 < refDim
  entDim : ℕ
  entDim_pos : 0 < entDim
  messageDim : ℕ
  messageDim_pos : 0 < messageDim
  krausDim : ℕ
  krausDim_pos : 0 < krausDim
  encoder : Fin messageDim → Fin krausDim →
    Matrix (Fin n → Fin inputDim) (Fin refDim × Fin entDim) ℂ
  encoder_complete : ∑ m, ∑ l, (encoder m l)ᴴ * encoder m l = 1
  decoder : Fin messageDim → Superop ((Fin n → Fin outputDim) × Fin entDim) (Fin refDim)
  decoder_channel : ∀ m, IsChannel (decoder m)

/-- PDF pp.24–25: the unnormalized pure branch on R TB A'^n obtained by
applying K to Alice's halves of independent maximally entangled pairs of
Schmidt ranks r and t. Its squared norm is the branch probability. Registers
R and TB are untouched. The code's positivity guards the square root/division.
Zero-probability Kraus branches remain present. -/
def encoderVector {r t i n : ℕ}
    (K : Matrix (Fin n → Fin i) (Fin r × Fin t) ℂ) :
    EuclideanSpace ℂ ((Fin r × Fin t) × (Fin n → Fin i)) :=
  WithLp.toLp 2 fun z => K z.2 z.1 / (Real.sqrt ((r : ℝ) * (t : ℝ)) : ℂ)

/-- PDF p.25: one-dimensional maximally entangled inputs have normalization 1. -/
example : encoderVector (r := 1) (t := 1) (i := 1) (n := 1)
    (Matrix.of fun _ _ => (1 : ℂ)) ((0, 0), fun _ => 0) = 1 := by
  norm_num [encoderVector]

/-- PDF p.25: a zero Kraus branch has zero amplitude, without conditioning or
normalizing a zero-probability event. -/
example {r t i n : ℕ} (z : (Fin r × Fin t) × (Fin n → Fin i)) :
    encoderVector (0 : Matrix (Fin n → Fin i) (Fin r × Fin t) ℂ) z = 0 := by
  simp [encoderVector]

/-- PDF p.24, (106): apply exactly n independent uses of N to a pure
encoder branch, leaving the reference R TB unchanged. The tensor channel
acts on all operator blocks, including off-diagonal and correlated inputs. -/
def channelBranch {i o n : ℕ} (N : Superop (Fin i) (Fin o))
    (code : AssistedQuantumCode i o n) (m : Fin code.messageDim)
    (l : Fin code.krausDim) :
    Matrix ((Fin code.refDim × Fin code.entDim) × (Fin n → Fin o))
      ((Fin code.refDim × Fin code.entDim) × (Fin n → Fin o)) ℂ :=
  idTensorSuperop (piSuperop (fun _ : Fin n => N))
    (pureDensity (encoderVector (code.encoder m l)))

/-- PDF p.24, (106): the actual code-induced cq state omega on A M B^n,
where A = R TB. The classical M blocks are diagonal; all Kraus labels have
been summed out. This state is computed, never supplied as free theorem data. -/
def codeState {i o n : ℕ} (N : Superop (Fin i) (Fin o))
    (code : AssistedQuantumCode i o n) :
    Matrix ((Fin code.refDim × Fin code.entDim) × (Fin code.messageDim × (Fin n → Fin o)))
      ((Fin code.refDim × Fin code.entDim) × (Fin code.messageDim × (Fin n → Fin o))) ℂ :=
  Matrix.of fun z w => if z.2.1 = w.2.1 then
    ∑ l, channelBranch N code z.2.1 l (z.1, z.2.2) (w.1, w.2.2) else 0

/-- PDF p.25: sigma on A X B^n with the single common classical refinement
X = (M,L). Measuring the discarded Kraus environment in its defining basis
is implemented by retaining its label. Each pre-channel branch is the pure
vector encoderVector; no finite alphabet or reference bound is imposed.
Zero-probability outcomes are retained. -/
def refinedCodeState {i o n : ℕ} (N : Superop (Fin i) (Fin o))
    (code : AssistedQuantumCode i o n) :
    Matrix ((Fin code.refDim × Fin code.entDim) ×
        ((Fin code.messageDim × Fin code.krausDim) × (Fin n → Fin o)))
      ((Fin code.refDim × Fin code.entDim) ×
        ((Fin code.messageDim × Fin code.krausDim) × (Fin n → Fin o))) ℂ :=
  Matrix.of fun z w => if z.2.1 = w.2.1 then
    channelBranch N code z.2.1.1 z.2.1.2 (z.1, z.2.2) (w.1, w.2.2) else 0

/-- PDF p.25: the AX marginal of a state on A X B, tracing out B. -/
def marginalAX {A X B : Type*} [Fintype B]
    (rho : Matrix (A × (X × B)) (A × (X × B)) ℂ) : Matrix (A × X) (A × X) ℂ :=
  Matrix.of fun z w => ∑ b, rho (z.1, (z.2, b)) (w.1, (w.2, b))

/-- Tracing a one-point final register removes precisely that register. -/
example {A X : Type*} (rho : Matrix (A × (X × Unit)) (A × (X × Unit)) ℂ)
    (z w : A × X) : marginalAX rho z w = rho (z.1, (z.2, ())) (w.1, (w.2, ())) := by
  simp [marginalAX]

/-- PDF p.25: I(AX;B) = H(AX) + H(B) - H(AXB), in bits. Only
constructed normalized states are used in the theorem. -/
def mutualAXB {A X B : Type*} [Fintype A] [Fintype X] [Fintype B]
    [DecidableEq A] [DecidableEq X] [DecidableEq B]
    (rho : Matrix (A × (X × B)) (A × (X × B)) ℂ) : ℝ :=
  vnEntropy (marginalAX rho) + vnEntropy (traceLeft (traceLeft rho)) - vnEntropy rho

/-- PDF p.25: I(A>B X) = H(BX) - H(ABX), in bits. The joint
entropy uses A X B order; entropy is invariant under the BX/XB swap. -/
def coherentABX {A X B : Type*} [Fintype A] [Fintype X] [Fintype B]
    [DecidableEq A] [DecidableEq X] [DecidableEq B]
    (rho : Matrix (A × (X × B)) (A × (X × B)) ℂ) : ℝ :=
  vnEntropy (traceLeft rho) - vnEntropy rho

/-- PDF p.24, the conditional decoder in Fig.10: reorder each M diagonal
block as R (B^n TB), apply id_R tensor D_m, and sum over M. There is no
backward communication and no free additional nonlocal resource. -/
def decodedState {i o n : ℕ} (N : Superop (Fin i) (Fin o))
    (code : AssistedQuantumCode i o n) :
    Matrix (Fin code.refDim × Fin code.refDim) (Fin code.refDim × Fin code.refDim) ℂ :=
  ∑ m : Fin code.messageDim,
    idTensorSuperop (code.decoder m)
      (Matrix.of fun z w =>
        codeState N code ((z.1, z.2.2), (m, z.2.1)) ((w.1, w.2.2), (m, w.2.1)))

/-- PDF p.24: the ideal maximally entangled vector of Schmidt rank d,
(|00> + ... + |d-1,d-1>)/sqrt(d). The code requires d > 0. -/
def idealEntangled (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun z => if z.1 = z.2 then ((Real.sqrt (d : ℝ))⁻¹ : ℂ) else 0

/-- The positive dimension-one register is allowed, and its unit vector is 1. -/
example : idealEntangled 1 (0, 0) = 1 := by
  norm_num [idealEntangled]

/-- PDF pp.24–25: the block quantum message size log_2 dim R. -/
def quantumSize {i o n : ℕ} (code : AssistedQuantumCode i o n) : ℝ :=
  Real.logb 2 (code.refDim : ℝ)

/-- PDF pp.24–25: the block noiseless classical cost log_2 dim M. -/
def classicalSize {i o n : ℕ} (code : AssistedQuantumCode i o n) : ℝ :=
  Real.logb 2 (code.messageDim : ℝ)

/-- PDF pp.24–25: the block entanglement cost log_2 dim TB. -/
def entanglementSize {i o n : ℕ} (code : AssistedQuantumCode i o n) : ℝ :=
  Real.logb 2 (code.entDim : ℝ)

end QAlgorithms.Papers.Independent.Dependency50.P03


