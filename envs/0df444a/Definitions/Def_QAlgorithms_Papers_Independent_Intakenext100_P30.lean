-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P30
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P30
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T00:56:52.75734+00:00
-- url     : https://prove2.me/theorems/df3e9441-6ce6-4171-9a07-9f8fc93500a9
-- title:
--   Definitions for Noisy channel coding via privacy amplification and information reconciliation
-- statement:
--   The objects the formalized statements of *Noisy channel coding via privacy amplification and information reconciliation* (arXiv:1012.4814) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RRDistribution`: Normalized classical law; PDF pp.2–4. Zero-probability letters are allowed.
--   - `rrUniform`: Uniform law, used only on explicitly nonempty alphabets; PDF pp.2–4.
--   - `RRIsCq`: Cq channel validity: every output is PSD and has trace one; PDF p.2.
--   - `RRCode`: A stochastic encoder with private randomness and a normalized POVM decoder; PDF pp.2–4, (1)–(3). Both maps are fixed for the whole message alphabet.
--   - `rrEncoded`: Encoded channel output, averaging only the encoder's private randomness; PDF p.2, (3).
--   - `rrCodeError`: Messagewise probability of a decoding error; PDF p.2, (1).
--   - `rrCodeLeak`: Half the trace norm to one fixed reference, not necessarily an average; PDF p.2, (2) and footnote 2. The reference is required normalized at use sites.
--   - `RRPublicGood`: Reliability for every message; PDF p.2, (1).
--   - `RRPrivateGood`: Messagewise reliability and secrecy with one normalized reference chosen before the message; PDF p.2, (1)–(2), footnote 2.
--   - `rrPublicCapacity`: Public one-shot capacity in bits, as an extended supremum over all finite nonempty message alphabets; PDF p.2. Corrects printed `log2 n` to `n` bits: (1) defines n = log2 |M|, and all subsequent formulas use that convention.
--   - `rrPrivateCapacity`: Private one-shot capacity, with arbitrary stochastic encoding and no shared key or entanglement; PDF p.2. Only the two output marginals matter.
--   - `rrCqState`: Cq state with classical first register; PDF p.3 and appendix p.7.
--   - `rrClassicalState`: Classical state with a trivial conditioning register; PDF p.7, (26).
--   - `RRSubnormalized`: Positive subnormalized smoothing candidates; PDF p.7, (29).
--   - `rrPurifiedToCenter`: Purified distance to the normalized center used in this paper; PDF p.7, (29). Root fidelity is the frozen primitive, so it is squared exactly once.
--   - `rrMinEntropy`: Extended conditional min-entropy, PDF p.7, (26). The exponent set is embedded before its supremum; the zero operator therefore has value +infinity.
--   - `rrMaxEntropy`: Extended max-entropy, PDF p.7, (25). The fidelity supremum is finite on finite-dimensional PSD states and positive for nonzero states; zero has value -infinity, not the default Real.logb value.
--   - `rrSmoothMin`: Smooth min-entropy over the full subnormalized purified-distance ball; PDF p.7, (29)–(30). Normalization of the center is supplied by its construction.
--   - `rrSmoothMax`: Smooth max-entropy; PDF p.7, (29), (31). Radius ≥ 1 includes zero and hence gives -infinity at a normalized center.
--   - `rrPreprocess`: Stochastic preprocessing T → X; PDF p.2, (6)–(7), and p.4.
--   - `rrPublicDirectInfo`: Optimized smooth public entropy difference, with the additive cost outside the optimization (it is uniform in the input law); PDF p.2, (4).
--   - `rrPublicConverseInfo`: Public converse expression, unsmoothed Hmin and smoothed Hmax; PDF p.2, (5).
--   - `rrPrivateInfo`: Private entropy difference optimized over every finite nonempty auxiliary T and stochastic map T → X; PDF p.2, (6)–(7). No attainment or bound on |T| is assumed. Fin (k+1) enumerates finite auxiliaries up to relabeling.
--   - `rrConditionalEntropy`: Conditional von Neumann entropy in bits, PDF p.7, following (28).
--   - `rrPublicInformation`: Optimized one-use public information on the fixed cq alphabet; PDF p.5, (16), (18). Extended suprema avoid junk values on unbounded sets.
--   - `rrPrivateInformation`: Private information over all finite auxiliaries and stochastic encoders, PDF p.5, (17), (19). Each entropy is computed from the same law and encoder.
--   - `rrChannelPower`: Independent uses of the fixed cq channel, with arbitrary joint classical input strings, PDF pp.5–6, (15)–(17). The empty product is one.
--   - `rrPerUse`: Reciprocal blocklength scaling; only n+1 is used in all limits below. PDF p.5, (15)–(17).
--   - `RRIsOperationalRate`: Relational form of the iterated operational rate (15), PDF p.5. Existence of both limits is part of a theorem, not a default-value definition. The punctured right neighborhood may be restricted to epsilon < 1/2 without changing the outer limit.
--   - `RRPublicRate`: Public operational rate for independent uses; PDF p.5, (15).
--   - `RRPrivateRate`: Private operational rate, with messagewise trace-distance secrecy; PDF p.5, (15). Codes and input distributions may be correlated across uses.
--   - `RRClassicalOutputs`: Simultaneous diagonalizability in a common orthonormal basis, separately for each output system; PDF p.5, before (18).
--   - `rrReconciliationError`: Information reconciliation average recovery error for a supplied law; PDF p.3, section II.B. For each c, the decompressor is a normalized POVM.
--   - `rrAffineCodeError`: Average coding error for the affine fiber a + ker(compress), with its uniform message law; PDF pp.3–4, proof of Lemma 2.
--   - `rrExtractedLaw`: Pushforward law of a deterministic extractor; PDF p.4, section II.C.
--   - `rrShapedLaw`: Output law of a stochastic shaper; PDF p.4, section II.C.
--   - `rrExtractedState`: Joint extractor-output/eavesdropper state before reversing extraction; PDF p.4, section II.C. Unattained extractor outputs have zero blocks.
--   - `rrUniformReference`: Ideal uniform classical output independent of the reference state; PDF p.4 privacy-amplification premise.
--   - `rrExampleReceiver`: Receiver's deterministic output in Figure 2, PDF p.6.
--   - `rrExampleEve`: Eve's output in Figure 2, PDF p.6: 0→0, 1→1, 2→fair bit.
--   - `rrExampleEncoder`: Figure 2 private encoder: 0 is uniformly randomized over 0,1; 1 uses 2. PDF p.6. This is a probability kernel, specified as raw weights.
--   - `rrExampleUnprocessedInformation`: Unpreprocessed private-information expression discussed below Figure 2, PDF p.6; this is not a separate deterministic operational capacity.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, https://arxiv.org/abs/1012.4814v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Intakenext100.P30

/-! All local objects below implement arXiv:1012.4814v2, pp.2–7.
Only frozen Defs modules are imported. Entropies use bits. The extended entropy
construction follows the audited formulas in Information100.P67, lines 812–833
of its Lean source, but is kept local to this paper as required by the workflow.
No theorem from that paper is imported or assumed. -/

variable {X Y Z M U V A B C : Type*}
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]
variable [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C]

attribute [local instance] Classical.propDecidable

/-- Normalized classical law; PDF pp.2–4. Zero-probability letters are allowed. -/
structure RRDistribution (X : Type*) [Fintype X] where
  prob : X → ℝ
  nonnegative : ∀ x, 0 ≤ prob x
  total : ∑ x, prob x = 1

/-- Uniform law, used only on explicitly nonempty alphabets; PDF pp.2–4. -/
def rrUniform (X : Type*) [Fintype X] : X → ℝ :=
  fun _ => (Fintype.card X : ℝ)⁻¹

/-- Cq channel validity: every output is PSD and has trace one; PDF p.2. -/
def RRIsCq (theta : X → Matrix Y Y ℂ) : Prop :=
  ∀ x, IsDensityMatrix (theta x)

/-- A stochastic encoder with private randomness and a normalized POVM decoder;
PDF pp.2–4, (1)–(3). Both maps are fixed for the whole message alphabet. -/
structure RRCode (M X Y : Type*) [Fintype M] [Fintype X] [Fintype Y]
    [DecidableEq Y] where
  encoder : M → RRDistribution X
  decoder : M → Matrix Y Y ℂ
  decoder_valid : IsPOVM decoder

/-- Encoded channel output, averaging only the encoder's private randomness;
PDF p.2, (3). -/
def rrEncoded (theta : X → Matrix Y Y ℂ) (enc : M → RRDistribution X)
    (m : M) : Matrix Y Y ℂ :=
  ∑ x, ((enc m).prob x : ℂ) • theta x

/-- Messagewise probability of a decoding error; PDF p.2, (1). -/
def rrCodeError (theta : X → Matrix Y Y ℂ) (code : RRCode M X Y) (m : M) : ℝ :=
  1 - effectProb (code.decoder m) (rrEncoded theta code.encoder m)

/-- Half the trace norm to one fixed reference, not necessarily an average;
PDF p.2, (2) and footnote 2. The reference is required normalized at use sites. -/
def rrCodeLeak (theta : X → Matrix Z Z ℂ) (enc : M → RRDistribution X)
    (reference : Matrix Z Z ℂ) (m : M) : ℝ :=
  traceNorm (rrEncoded theta enc m - reference) / 2

/-- Reliability for every message; PDF p.2, (1). -/
def RRPublicGood (theta : X → Matrix Y Y ℂ) (code : RRCode M X Y) (epsilon : ℝ) : Prop :=
  ∀ m, rrCodeError theta code m ≤ epsilon

/-- Messagewise reliability and secrecy with one normalized reference chosen
before the message; PDF p.2, (1)–(2), footnote 2. -/
def RRPrivateGood (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (code : RRCode M X Y) (epsilon : ℝ) : Prop :=
  RRPublicGood thetaY code epsilon ∧
    ∃ reference : Matrix Z Z ℂ, IsDensityMatrix reference ∧
      ∀ m, rrCodeLeak thetaZ code.encoder reference m ≤ epsilon

/-- Public one-shot capacity in bits, as an extended supremum over all finite
nonempty message alphabets; PDF p.2. Corrects printed `log2 n` to `n` bits:
(1) defines n = log2 |M|, and all subsequent formulas use that convention. -/
def rrPublicCapacity (theta : X → Matrix Y Y ℂ) (epsilon : ℝ) : EReal :=
  sSup {r | ∃ k : ℕ, ∃ code : RRCode (Fin (k + 1)) X Y,
    RRPublicGood theta code epsilon ∧ r = (Real.logb 2 (k + 1 : ℝ) : EReal)}

/-- Private one-shot capacity, with arbitrary stochastic encoding and no
shared key or entanglement; PDF p.2. Only the two output marginals matter. -/
def rrPrivateCapacity (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (epsilon : ℝ) : EReal :=
  sSup {r | ∃ k : ℕ, ∃ code : RRCode (Fin (k + 1)) X Y,
    RRPrivateGood thetaY thetaZ code epsilon ∧
      r = (Real.logb 2 (k + 1 : ℝ) : EReal)}

/-- Cq state with classical first register; PDF p.3 and appendix p.7. -/
def rrCqState (p : A → ℝ) (theta : A → Matrix B B ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun a b => if a.1 = b.1 then (p a.1 : ℂ) * theta a.1 a.2 b.2 else 0

/-- Classical state with a trivial conditioning register; PDF p.7, (26). -/
def rrClassicalState (p : A → ℝ) : Matrix (A × Unit) (A × Unit) ℂ :=
  rrCqState p (fun _ => (1 : Matrix Unit Unit ℂ))

/-- Positive subnormalized smoothing candidates; PDF p.7, (29). -/
def RRSubnormalized (rho : Matrix A A ℂ) : Prop :=
  rho.PosSemidef ∧ rho.trace.re ≤ 1

/-- Purified distance to the normalized center used in this paper; PDF p.7,
(29). Root fidelity is the frozen primitive, so it is squared exactly once. -/
def rrPurifiedToCenter (tau rho : Matrix A A ℂ) : ℝ :=
  Real.sqrt (1 - rootFidelity tau rho ^ 2)

/-- Extended conditional min-entropy, PDF p.7, (26). The exponent set is
embedded before its supremum; the zero operator therefore has value +infinity. -/
def rrMinEntropy (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sSup {h : EReal | ∃ a : ℝ, h = (a : EReal) ∧
    ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
      ((Real.rpow 2 (-a) : ℂ) • Matrix.kronecker (1 : Matrix A A ℂ) sigma - rho).PosSemidef}

/-- Extended max-entropy, PDF p.7, (25). The fidelity supremum is finite on
finite-dimensional PSD states and positive for nonzero states; zero has value
-infinity, not the default Real.logb value. -/
def rrMaxEntropy (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  if rho = 0 then ⊥ else
    (Real.logb 2 (sSup {f : ℝ | ∃ sigma : Matrix B B ℂ,
      IsDensityMatrix sigma ∧
        f = rootFidelity rho (Matrix.kronecker (1 : Matrix A A ℂ) sigma) ^ 2}) : EReal)

/-- Smooth min-entropy over the full subnormalized purified-distance ball;
PDF p.7, (29)–(30). Normalization of the center is supplied by its construction. -/
def rrSmoothMin (rho : Matrix (A × B) (A × B) ℂ) (radius : ℝ) : EReal :=
  sSup {h | ∃ tau : Matrix (A × B) (A × B) ℂ, RRSubnormalized tau ∧
    rrPurifiedToCenter tau rho ≤ radius ∧ h = rrMinEntropy tau}

/-- Smooth max-entropy; PDF p.7, (29), (31). Radius ≥ 1 includes zero and
hence gives -infinity at a normalized center. -/
def rrSmoothMax (rho : Matrix (A × B) (A × B) ℂ) (radius : ℝ) : EReal :=
  sInf {h | ∃ tau : Matrix (A × B) (A × B) ℂ, RRSubnormalized tau ∧
    rrPurifiedToCenter tau rho ≤ radius ∧ h = rrMaxEntropy tau}

/-- Stochastic preprocessing T → X; PDF p.2, (6)–(7), and p.4. -/
def rrPreprocess (theta : X → Matrix B B ℂ) (enc : A → RRDistribution X) :
    A → Matrix B B ℂ :=
  rrEncoded theta enc

/-- Optimized smooth public entropy difference, with the additive cost outside
the optimization (it is uniform in the input law); PDF p.2, (4). -/
def rrPublicDirectInfo (theta : X → Matrix Y Y ℂ) (radius : ℝ) : EReal :=
  sSup {v | ∃ p : RRDistribution X,
    v = rrSmoothMin (rrClassicalState p.prob) radius -
      rrSmoothMax (rrCqState p.prob theta) radius}

/-- Public converse expression, unsmoothed Hmin and smoothed Hmax;
PDF p.2, (5). -/
def rrPublicConverseInfo (theta : X → Matrix Y Y ℂ) (radius : ℝ) : EReal :=
  sSup {v | ∃ p : RRDistribution X,
    v = rrMinEntropy (rrClassicalState p.prob) -
      rrSmoothMax (rrCqState p.prob theta) radius}

/-- Private entropy difference optimized over every finite nonempty auxiliary
T and stochastic map T → X; PDF p.2, (6)–(7). No attainment or bound on |T| is
assumed. Fin (k+1) enumerates finite auxiliaries up to relabeling. -/
def rrPrivateInfo (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (radius : ℝ) : EReal :=
  sSup {v | ∃ k : ℕ, ∃ p : RRDistribution (Fin (k + 1)),
    ∃ enc : Fin (k + 1) → RRDistribution X,
      v = rrSmoothMin (rrCqState p.prob (rrPreprocess thetaZ enc)) radius -
        rrSmoothMax (rrCqState p.prob (rrPreprocess thetaY enc)) radius}

/-- Conditional von Neumann entropy in bits, PDF p.7, following (28). -/
def rrConditionalEntropy (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy rho - vnEntropy (traceLeft rho)

/-- Optimized one-use public information on the fixed cq alphabet;
PDF p.5, (16), (18). Extended suprema avoid junk values on unbounded sets. -/
def rrPublicInformation (theta : X → Matrix Y Y ℂ) : EReal :=
  sSup {v | ∃ p : RRDistribution X,
    v = ((vnEntropy (Matrix.diagonal (fun x => (p.prob x : ℂ))) -
      rrConditionalEntropy (rrCqState p.prob theta) : ℝ) : EReal)}

/-- Private information over all finite auxiliaries and stochastic encoders,
PDF p.5, (17), (19). Each entropy is computed from the same law and encoder. -/
def rrPrivateInformation (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ) : EReal :=
  sSup {v | ∃ k : ℕ, ∃ p : RRDistribution (Fin (k + 1)),
    ∃ enc : Fin (k + 1) → RRDistribution X,
      v = ((rrConditionalEntropy (rrCqState p.prob (rrPreprocess thetaZ enc)) -
        rrConditionalEntropy (rrCqState p.prob (rrPreprocess thetaY enc)) : ℝ) : EReal)}

/-- Independent uses of the fixed cq channel, with arbitrary joint classical
input strings, PDF pp.5–6, (15)–(17). The empty product is one. -/
def rrChannelPower (theta : X → Matrix Y Y ℂ) (n : ℕ) :
    (Fin n → X) → Matrix (Fin n → Y) (Fin n → Y) ℂ :=
  fun x a b => ∏ i, theta (x i) (a i) (b i)

/-- Reciprocal blocklength scaling; only n+1 is used in all limits below.
PDF p.5, (15)–(17). -/
def rrPerUse (n : ℕ) (v : EReal) : EReal := ((n : ℝ)⁻¹ : EReal) * v

/-- Relational form of the iterated operational rate (15), PDF p.5.
Existence of both limits is part of a theorem, not a default-value definition.
The punctured right neighborhood may be restricted to epsilon < 1/2 without
changing the outer limit. -/
def RRIsOperationalRate (capacity : ℕ → ℝ → EReal) (rate : ℝ) : Prop :=
  ∃ innerLimit : ℝ → EReal,
    (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      Tendsto (fun n : ℕ => rrPerUse (n + 1) (capacity (n + 1) epsilon))
        atTop (nhds (innerLimit epsilon))) ∧
    Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds (rate : EReal))

/-- Public operational rate for independent uses; PDF p.5, (15). -/
def RRPublicRate (theta : X → Matrix Y Y ℂ) (rate : ℝ) : Prop :=
  RRIsOperationalRate (fun n epsilon => rrPublicCapacity (rrChannelPower theta n) epsilon) rate

/-- Private operational rate, with messagewise trace-distance secrecy;
PDF p.5, (15). Codes and input distributions may be correlated across uses. -/
def RRPrivateRate (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (rate : ℝ) : Prop :=
  RRIsOperationalRate (fun n epsilon =>
    rrPrivateCapacity (rrChannelPower thetaY n) (rrChannelPower thetaZ n) epsilon) rate

/-- Simultaneous diagonalizability in a common orthonormal basis, separately
for each output system; PDF p.5, before (18). -/
def RRClassicalOutputs (theta : X → Matrix Y Y ℂ) : Prop :=
  ∃ basisChange : Matrix Y Y ℂ,
    basisChangeᴴ * basisChange = 1 ∧ basisChange * basisChangeᴴ = 1 ∧
    ∀ x a b, a ≠ b → (basisChangeᴴ * theta x * basisChange) a b = 0

/-- Information reconciliation average recovery error for a supplied law;
PDF p.3, section II.B. For each c, the decompressor is a normalized POVM. -/
def rrReconciliationError (theta : U → Matrix Y Y ℂ) (compress : U → C)
    (decompress : C → U → Matrix Y Y ℂ) (p : U → ℝ) : ℝ :=
  ∑ u, p u * (1 - effectProb (decompress (compress u) u) (theta u))

/-- Average coding error for the affine fiber a + ker(compress), with its
uniform message law; PDF pp.3–4, proof of Lemma 2. -/
def rrAffineCodeError {K : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup C] [Module K C] (theta : U → Matrix Y Y ℂ)
    (compress : U →ₗ[K] C) (a : U)
    (decoder : {u : U // compress u = 0} → Matrix Y Y ℂ) : ℝ :=
  (Fintype.card {u : U // compress u = 0} : ℝ)⁻¹ *
    ∑ m : {u : U // compress u = 0},
      (1 - effectProb (decoder m) (theta (a + m.val)))

/-- Pushforward law of a deterministic extractor; PDF p.4, section II.C. -/
def rrExtractedLaw (p : X → ℝ) (extract : X → U) : U → ℝ :=
  fun u => ∑ x, if extract x = u then p x else 0

/-- Output law of a stochastic shaper; PDF p.4, section II.C. -/
def rrShapedLaw (p : U → ℝ) (shape : U → RRDistribution X) : X → ℝ :=
  fun x => ∑ u, p u * (shape u).prob x

/-- Joint extractor-output/eavesdropper state before reversing extraction;
PDF p.4, section II.C. Unattained extractor outputs have zero blocks. -/
def rrExtractedState (p : X → ℝ) (extract : X → U) (thetaZ : X → Matrix Z Z ℂ) :
    Matrix (U × Z) (U × Z) ℂ :=
  fun a b => if a.1 = b.1 then
    ∑ x, if extract x = a.1 then (p x : ℂ) * thetaZ x a.2 b.2 else 0
    else 0

/-- Ideal uniform classical output independent of the reference state;
PDF p.4 privacy-amplification premise. -/
def rrUniformReference (reference : Matrix Z Z ℂ) : Matrix (U × Z) (U × Z) ℂ :=
  rrCqState (rrUniform U) (fun _ => reference)

/-- Receiver's deterministic output in Figure 2, PDF p.6. -/
def rrExampleReceiver : Fin 3 → Matrix Bool Bool ℂ :=
  fun x => Matrix.diagonal (fun y => if y = decide (x = 2) then 1 else 0)

/-- Eve's output in Figure 2, PDF p.6: 0→0, 1→1, 2→fair bit. -/
def rrExampleEve : Fin 3 → Matrix Bool Bool ℂ :=
  fun x => Matrix.diagonal (fun z =>
    if x = 2 then (1 / 2 : ℂ) else if z = decide (x = 1) then 1 else 0)

/-- Figure 2 private encoder: 0 is uniformly randomized over 0,1; 1 uses 2.
PDF p.6. This is a probability kernel, specified as raw weights. -/
def rrExampleEncoder (message : Bool) (x : Fin 3) : ℝ :=
  if message then (if x = 2 then 1 else 0) else (if x = 2 then 0 else 1 / 2)

/-- Unpreprocessed private-information expression discussed below Figure 2,
PDF p.6; this is not a separate deterministic operational capacity. -/
def rrExampleUnprocessedInformation : EReal :=
  sSup {v | ∃ p : RRDistribution (Fin 3),
    v = ((rrConditionalEntropy (rrCqState p.prob rrExampleEve) -
      rrConditionalEntropy (rrCqState p.prob rrExampleReceiver) : ℝ) : EReal)}

/-! Sanity examples pin local definitions without proving any source result. -/

example : RRDistribution Unit :=
  { prob := fun _ => 1
    nonnegative := by intro x; norm_num
    total := by simp }

example : rrUniform Unit () = 1 := by simp [rrUniform]

example (rho : Matrix A A ℂ) : rrPurifiedToCenter 0 rho = 1 := by
  have hs : cfc Real.sqrt (0 : Matrix A A ℂ) = 0 := by
    rw [cfc_apply_zero, Real.sqrt_zero, map_zero]
  simp [rrPurifiedToCenter, rootFidelity, hs]

example : rrMaxEntropy (0 : Matrix (Unit × Unit) (Unit × Unit) ℂ) = ⊥ := by
  simp [rrMaxEntropy]

example (theta : X → Matrix Y Y ℂ) (x : Fin 0 → X) (a b : Fin 0 → Y) :
    rrChannelPower theta 0 x a b = 1 := by simp [rrChannelPower]

example : rrExampleEncoder false (0 : Fin 3) = 1 / 2 := by
  have hInput : (0 : Fin 3) ≠ 2 := by
    intro hEq
    have hVal := congrArg Fin.val hEq
    norm_num at hVal
  simp [rrExampleEncoder, hInput]

end QAlgorithms.Papers.Independent.Intakenext100.P30


