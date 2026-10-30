-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P15
-- name    : QAlgorithms_Papers_Independent_Advance50_P15
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T10:24:16.161567+00:00
-- url     : https://prove2.me/theorems/f3e2f476-46d6-4546-9956-0204b0a252af
-- title:
--   Definitions for Structured Codes Improve the Bennett-Brassard-84 Quantum Key Rate
-- statement:
--   The objects the formalized statements of *Structured Codes Improve the Bennett-Brassard-84 Quantum Key Rate* (arXiv:quant-ph/0607018) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `repetitionSyndrome`: PDF p.2, Lemma 2: the syndrome of the Z_1 Z_j checks; source wire 1 is wire 0.
--   - `repetitionCoordinates`: PDF p.2, Lemma 2: the bijective coherent decoder, retaining wire 0 and all check outcomes. It does not perform majority correction or discard syndromes.
--   - `repetitionEncode`: PDF p.2: the repetition-code embedding of a logical vector in the span of |0...0> and |1...1>.
--   - `repetitionDecode`: PDF pp.2--3: coherent decoding is a permutation of the computational basis.
--   - `phaseSign`: PDF p.2, Eq.(4): the phase (-1)^(v dot x), using the frozen modulo-two dot product.
--   - `physicalPauli`: PDF p.2, Lemma 2: the ordered Pauli X^u Z^v (Z acts first). The input coordinate at output y is y xor u.
--   - `logicalPauli`: PDF p.2, Lemma 2: the logical operator X^u Z^v, in the same order as the physical Pauli.
--   - `bernoulliWord`: PDF p.2, Eq.(3): an independent Bernoulli(p) word, including the endpoints. The empty word has mass one.
--   - `logicalSyndromeProb`: PDF p.2, Lemma 2: the actual pushforward of independent physical bit errors under the decoder, for one specific syndrome string.
--   - `bellWeight`: PDF p.2, definition of Gamma_p and Eq.(4): Bell/Pauli weights, indexed by (bit error, phase error). On 0 <= p <= 1/2, exactly 0 <= t <= p is allowed.
--   - `pauliWordProb`: PDF p.2, Eq.(4): the m-fold product distribution of the single-pair law. This is not an arbitrary correlated distribution with the same marginals.
--   - `EveRegister`: PDF pp.2--3, Eq.(5)--(8): Eve's register includes Alice's PUBLIC syndrome, then the entire channel-purifying registers E1 and E2. Alice's private noise register is excluded.
--   - `eveGivenBit`: PDF pp.2--3, Eq.(5)--(8), with the public V explicitly retained: Eve's normalized conditional density given Alice's noisy first bit a. For the public syndrome s, z = decoder^(-1)(a,s) is the noisy word, and x = z xor f was the original uniform word. Summing the independent private f incoherently traces out Alice's noise register. The uniform syndrome contributes 2^(-k). No conditional distribution at a zero-probability error word is used.
--   - `eveInformation`: PDF p.3, Eq.(8): I(A;E V), the Holevo information of the uniform retained bit in Eve's full system, including all public syndrome information.
--   - `phaseRay`: PDF p.2, Theorem 1: the two normalized rays phi_+ and phi_-.
--   - `phaseDensity`: PDF p.2, Theorem 1: rho_(p,q) = (1-q)|phi_+><phi_+| + q|phi_-><phi_-|.
--   - `repetitionPhaseMixture`: PDF p.2, Eq.(2): the equal mixture of rho^tensor m and its conjugate by Z^tensor m. Both signs are real, so the right factor is its own adjoint.
--   - `logicalConditionalEntropy`: PDF pp.2--3, Eq.(2): H(logical bit | syndrome) as H(joint)-H(syndrome). This equals the weighted sum over every individual syndrome, including its multiplicity; it never divides by the mass of an impossible syndrome.
--   - `repetitionExpression`: PDF p.2, Eq.(2): the displayed entropic expression per sifted signal. It can be negative and is not defined to be an operational capacity.
-- source:
--   Structured Codes Improve the Bennett-Brassard-84 Quantum Key Rate, arXiv:quant-ph/0607018v2, https://arxiv.org/abs/quant-ph/0607018v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

/-!
Smith--Renes--Smolin, arXiv:quant-ph/0607018v2, PDF pp.2--4.
The finite decoder, adversary-information maximum, and numerical positivity are
stated here. The operational Theorem 1 and the full single-letter comparison
are deferred in the unit's HARD.md, rather than replaced by entropic surrogates.
New paper-specific definitions are local; finite Shannon entropy is reused
directly from the pinned accepted Support50.P40 module. The parameter k denotes m - 1,
so that every repetition block has the positive length m = k + 1.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P15

open QAlgorithms
open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, Lemma 2: the syndrome of the Z_1 Z_j checks; source wire 1 is wire 0. -/
def repetitionSyndrome {k : ℕ} (x : Qubits (k + 1)) : Qubits k :=
  fun j => Bool.xor (x 0) (x j.succ)

/-- PDF p.2, Lemma 2: the bijective coherent decoder, retaining wire 0 and all
check outcomes. It does not perform majority correction or discard syndromes. -/
def repetitionCoordinates (k : ℕ) : Qubits (k + 1) ≃ Bool × Qubits k where
  toFun x := (x 0, repetitionSyndrome x)
  invFun z := Fin.cases z.1 (fun j => Bool.xor z.1 (z.2 j))
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change Bool.xor (x 0) (Bool.xor (x 0) (x j.succ)) = x j.succ
      rw [← Bool.xor_assoc, Bool.xor_self]
      simp
  right_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      change Bool.xor z.1 (Bool.xor z.1 (z.2 j)) = z.2 j
      rw [← Bool.xor_assoc, Bool.xor_self]
      simp

/-- PDF p.2: the repetition-code embedding of a logical vector in the span of
|0...0> and |1...1>. -/
def repetitionEncode (k : ℕ) (psi : EuclideanSpace ℂ Bool) :
    EuclideanSpace ℂ (Qubits (k + 1)) :=
  WithLp.toLp 2 fun x => if ∀ i, x i = x 0 then psi (x 0) else 0

/-- PDF pp.2--3: coherent decoding is a permutation of the computational basis. -/
def repetitionDecode {k : ℕ} (psi : EuclideanSpace ℂ (Qubits (k + 1))) :
    EuclideanSpace ℂ (Bool × Qubits k) :=
  WithLp.toLp 2 fun z => psi ((repetitionCoordinates k).symm z)

/-- PDF p.2, Eq.(4): the phase (-1)^(v dot x), using the frozen modulo-two dot product. -/
def phaseSign {m : ℕ} (v x : Qubits m) : ℂ :=
  if dotBits v x then -1 else 1

/-- PDF p.2, Lemma 2: the ordered Pauli X^u Z^v (Z acts first).
The input coordinate at output y is y xor u. -/
def physicalPauli {m : ℕ} (u v : Qubits m)
    (psi : EuclideanSpace ℂ (Qubits m)) : EuclideanSpace ℂ (Qubits m) :=
  WithLp.toLp 2 fun y => phaseSign v (y + u) * psi (y + u)

/-- PDF p.2, Lemma 2: the logical operator X^u Z^v, in the same order as the
physical Pauli. -/
def logicalPauli (u v : Bool) (psi : EuclideanSpace ℂ Bool) :
    EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun y =>
    (if v && Bool.xor y u then (-1 : ℂ) else 1) * psi (Bool.xor y u)

/-- PDF p.2, Eq.(3): an independent Bernoulli(p) word, including the endpoints.
The empty word has mass one. -/
def bernoulliWord {m : ℕ} (p : ℝ) (u : Qubits m) : ℝ :=
  ∏ i, if u i then p else 1 - p

/-- PDF p.2, Lemma 2: the actual pushforward of independent physical bit errors
under the decoder, for one specific syndrome string. -/
def logicalSyndromeProb (k : ℕ) (p : ℝ) (a : Bool) (s : Qubits k) : ℝ :=
  ∑ u : Qubits (k + 1), if u 0 = a ∧ repetitionSyndrome u = s then bernoulliWord p u else 0

/-- PDF p.2, definition of Gamma_p and Eq.(4): Bell/Pauli weights, indexed by
(bit error, phase error). On 0 <= p <= 1/2, exactly 0 <= t <= p is allowed. -/
def bellWeight (p t : ℝ) (u v : Bool) : ℝ :=
  if u then (if v then t else p - t)
  else (if v then p - t else 1 + t - 2 * p)

/-- PDF p.2, Eq.(4): the m-fold product distribution of the single-pair law.
This is not an arbitrary correlated distribution with the same marginals. -/
def pauliWordProb {m : ℕ} (p t : ℝ) (u v : Qubits m) : ℝ :=
  ∏ i, bellWeight p t (u i) (v i)

/-- PDF pp.2--3, Eq.(5)--(8): Eve's register includes Alice's PUBLIC syndrome,
then the entire channel-purifying registers E1 and E2. Alice's private noise
register is excluded. -/
abbrev EveRegister (k : ℕ) := Qubits k × (Qubits (k + 1) × Qubits (k + 1))

/-- PDF pp.2--3, Eq.(5)--(8), with the public V explicitly retained: Eve's
normalized conditional density given Alice's noisy first bit a. For the public
syndrome s, z = decoder^(-1)(a,s) is the noisy word, and x = z xor f was the
original uniform word. Summing the independent private f incoherently traces
out Alice's noise register. The uniform syndrome contributes 2^(-k).
No conditional distribution at a zero-probability error word is used. -/
def eveGivenBit (k : ℕ) (p q t : ℝ) (a : Bool) :
    Matrix (EveRegister k) (EveRegister k) ℂ :=
  fun e d => if e.1 = d.1 ∧ e.2.1 = d.2.1 then
    ((2 : ℂ) ^ k)⁻¹ * ∑ f : Qubits (k + 1),
      let x := ((repetitionCoordinates k).symm (a, e.1) + f)
      (bernoulliWord q f : ℂ) *
        (Real.sqrt (pauliWordProb p t e.2.1 e.2.2) : ℂ) *
        (Real.sqrt (pauliWordProb p t e.2.1 d.2.2) : ℂ) *
        phaseSign e.2.2 x * conj (phaseSign d.2.2 x)
  else 0

/-- PDF p.3, Eq.(8): I(A;E V), the Holevo information of the uniform retained
bit in Eve's full system, including all public syndrome information. -/
def eveInformation (k : ℕ) (p q t : ℝ) : ℝ :=
  let r0 := eveGivenBit k p q t false
  let r1 := eveGivenBit k p q t true
  vnEntropy (((1 / 2 : ℂ) • r0) + ((1 / 2 : ℂ) • r1)) -
    (vnEntropy r0 + vnEntropy r1) / 2

/-- PDF p.2, Theorem 1: the two normalized rays phi_+ and phi_-. -/
def phaseRay (p : ℝ) (minus : Bool) : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun b => if b then
    (if minus then (-1 : ℂ) else 1) * (Real.sqrt p : ℂ)
  else (Real.sqrt (1 - p) : ℂ)

/-- PDF p.2, Theorem 1: rho_(p,q) = (1-q)|phi_+><phi_+| + q|phi_-><phi_-|. -/
def phaseDensity (p q : ℝ) : Matrix Bool Bool ℂ :=
  ((1 - q : ℝ) : ℂ) • pureDensity (phaseRay p false) +
    (q : ℂ) • pureDensity (phaseRay p true)

/-- PDF p.2, Eq.(2): the equal mixture of rho^tensor m and its conjugate by
Z^tensor m. Both signs are real, so the right factor is its own adjoint. -/
def repetitionPhaseMixture (m : ℕ) (p q : ℝ) : Matrix (Qubits m) (Qubits m) ℂ :=
  fun x y => (1 / 2 : ℂ) * kronAll (fun _ : Fin m => phaseDensity p q) x y +
    (1 / 2 : ℂ) * (-1 : ℂ) ^ hammingWeight x *
      kronAll (fun _ : Fin m => phaseDensity p q) x y * (-1 : ℂ) ^ hammingWeight y

/-- PDF pp.2--3, Eq.(2): H(logical bit | syndrome) as H(joint)-H(syndrome).
This equals the weighted sum over every individual syndrome, including its
multiplicity; it never divides by the mass of an impossible syndrome. -/
def logicalConditionalEntropy (k : ℕ) (p : ℝ) : ℝ :=
  QAlgorithms.Papers.Independent.Support50.P40.finiteEntropyBits (fun z : Bool × Qubits k => logicalSyndromeProb k p z.1 z.2) -
    QAlgorithms.Papers.Independent.Support50.P40.finiteEntropyBits (fun s : Qubits k => ∑ a : Bool, logicalSyndromeProb k p a s)

/-- PDF p.2, Eq.(2): the displayed entropic expression per sifted signal.
It can be negative and is not defined to be an operational capacity. -/
def repetitionExpression (k : ℕ) (p q : ℝ) : ℝ :=
  (1 - logicalConditionalEntropy k (p * (1 - q) + q * (1 - p)) +
    ((k + 1 : ℕ) : ℝ) * vnEntropy (phaseDensity p q) -
    vnEntropy (repetitionPhaseMixture (k + 1) p q)) / ((k + 1 : ℕ) : ℝ)

/-! Sanity examples for the new interfaces. -/

example (k : ℕ) (a : Bool) (s : Qubits k) :
    (repetitionCoordinates k).symm (a, s) 0 = a := rfl

example (k : ℕ) : repetitionSyndrome (fun _ : Fin (k + 1) => false) =
    (fun _ : Fin k => false) := by
  funext j
  rfl

example (x : Qubits 0) : hammingWeight x = 0 := by
  simp [hammingWeight]

example (p : ℝ) (x : Qubits 0) : bernoulliWord p x = 1 := by
  simp [bernoulliWord]

example (v x : Qubits 0) : phaseSign v x = 1 := by
  simp [phaseSign, dotBits]

example (p : ℝ) : bellWeight p (p ^ 2) true true = p ^ 2 := rfl

example (k : ℕ) (p q t : ℝ) (a : Bool) (e d : EveRegister k)
    (h : e.1 ≠ d.1) : eveGivenBit k p q t a e d = 0 := by
  simp [eveGivenBit, h]

example (p : ℝ) : phaseDensity p 0 = pureDensity (phaseRay p false) := by
  simp [phaseDensity]

example (rho : Matrix Bool Bool ℂ) (x y : Qubits 0) :
    kronAll (fun _ : Fin 0 => rho) x y = 1 := by
  simp [kronAll]

example {I : Type*} [Fintype I] : QAlgorithms.Papers.Independent.Support50.P40.finiteEntropyBits (fun _ : I => 0) = 0 := by
  simp [QAlgorithms.Papers.Independent.Support50.P40.finiteEntropyBits]

end QAlgorithms.Papers.Independent.Advance50.P15


