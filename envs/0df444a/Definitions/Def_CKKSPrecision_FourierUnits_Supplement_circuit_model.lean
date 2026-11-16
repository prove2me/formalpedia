-- Prove2me | Definitions.Def_CKKSPrecision_FourierUnits_Supplement_circuit_model
-- name    : CKKSPrecision_FourierUnits_Supplement_circuit_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:23:58.295062+00:00
-- url     : https://prove2.me/theorems/778089d6-fd91-4473-8917-43e4d0c5a631
-- title:
--   Finite CKKS circuits, exact execution and rational error propagation
-- statement:
--   A circuit is a finite ordered list of nodes with references to earlier nodes and one designated output. Nodes are fresh encryption, addition, subtraction, addition or multiplication by a public vector, ciphertext multiplication, multiplication followed by rescaling, rescaling alone, modulus reduction, or an automorphism with its slot permutation and possible conjugation. A finite directed acyclic graph has such an ordering; repeated references preserve sharing. Public vectors and input values may be arbitrary complex vectors. Their magnitude bounds, scales and primitive error bounds are rational and independent of the allocation parameter. At every node, any chosen rational bound on the computed logical value is permitted, including bounds sharper than elementary triangle-inequality propagation.
--
--   For rational $c_j>0$ and $s_j\in\{-1,1\}$, let $W_j(t)=c_jt^{s_j}$. The node loop propagates moduli, scales and logical magnitude bounds, and constructs actual rational Laurent polynomials $E_{v,j}(t)$. Its rules are the rewritten rules in §6.1 and Appendix B. In particular, multiplication followed by rescaling uses
--   $$
--   E_{v,j}=A_{a,j}E_{b,j}+A_{b,j}E_{a,j}+E_{a,j}E_{b,j}
--    +W_j\frac{K_v+R_v}{\Delta_a\Delta_b},
--   \qquad D_v\Delta_v=\Delta_a\Delta_b.
--   $$
--   Plaintext multiplication adds $A_{a,j}\beta_{v,j}$ without a weight factor; automorphisms move $E_{a,k}$ without a weight ratio. Laurent polynomials use Mathlib's general rational Laurent polynomial type.
--
--   An execution records actual ciphertexts, relinearization outputs, phase errors and public correction polynomials. Its joint error event asserts only the exact operation equations and the primitive bounds (18) and Appendix B, simultaneously on these actual inputs. The logical values and restored messages are computed from this execution. Neither their desired propagated error bounds nor output recovery is assumed. Encryption is abstracted by its specified phase relation. Automorphism corrections satisfy $pq_\tau\equiv\tau(p)\pmod Q$; no probabilistic independence or encryption distribution is imposed.
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, STOC 2027 submission #148 (October 2026), pp. 11–15, 25–26 (PDF pp. 13–17, 27–28), §6.1, Algorithm 1 lines 1–3, §§7.1–7.2 and Appendix B.

import Definitions.Def_CKKSPrecision_FourierUnits_Supplement_ckks_model

set_option autoImplicit false
noncomputable section

namespace CKKSPrecision.FourierUnits.Supplement

abbrev Laurent := LaurentPolynomial ℚ

def lc (q : ℚ) : Laurent := LaurentPolynomial.C q

def leval (f : Laurent) (t : ℝ) : ℝ := f.coeff.sum (fun k c => (c : ℝ) * t ^ k)

structure Weights (r : ℕ+) where
  coefficient : Slot r → ℚ
  sign : Slot r → ℤ
  positive : ∀ j, 0 < coefficient j
  signed : ∀ j, sign j = -1 ∨ sign j = 1

def weightPoly {r : ℕ+} (w : Weights r) (j : Slot r) : Laurent :=
  lc (w.coefficient j) * LaurentPolynomial.T (w.sign j)

def weight {r : ℕ+} (w : Weights r) (t : ℝ) (j : Slot r) : ℝ := leval (weightPoly w j) t

/-- Slot permutation together with possible conjugation, induced by an actual ring automorphism. -/
structure SlotAutomorphism (r : ℕ+) where
  aut : Scalar r ≃ₐ[ℚ] Scalar r
  perm : Slot r ≃ Slot r
  conjugate : Slot r → Bool
  integral : ∀ f, InRing f → InRing (aut f)
  compatible : ∀ f j, sigma (aut f) j =
    if conjugate j then star (sigma f (perm j)) else sigma f (perm j)

def move {r : ℕ+} (tau : SlotAutomorphism r) (x : Vector r) : Vector r :=
  fun j => if tau.conjugate j then star (x (tau.perm j)) else x (tau.perm j)

inductive Operation (r : ℕ+) where
  | fresh
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | addPlain (a : ℕ)
  | multPlain (a : ℕ)
  | mult (a b : ℕ)
  | multRS (a b : ℕ)
  | rs (a : ℕ)
  | modReduce (a : ℕ)
  | auto (a : ℕ) (tau : SlotAutomorphism r)

def inputs {r : ℕ+} : Operation r → List ℕ
  | .fresh => []
  | .add a b | .sub a b | .mult a b | .multRS a b => [a, b]
  | .addPlain a | .multPlain a | .rs a | .modReduce a | .auto a _ => [a]

/-- Finite rational analysis data; input and public values themselves may be arbitrary complex. -/
structure Node (r : ℕ+) where
  op : Operation r
  input : Vector r
  plain : Vector r
  valueBound : Slot r → ℚ
  plainBound : Slot r → ℚ
  inputModulus : ℕ
  inputScale : ℚ
  plainScale : ℚ
  divisor : ℕ
  reducedModulus : ℕ
  encBound : ℚ
  decBound : ℚ
  keyBound : ℚ
  residueBound : ℚ
  addBound : ℚ
  beta : Slot r → ℚ

structure Circuit (r : ℕ+) where
  nodes : List (Node r)
  output : ℕ

structure Analysis (r : ℕ+) where
  modulus : ℕ
  scale : ℚ
  magnitude : Slot r → ℚ
  error : Slot r → Laurent

def zeroAnalysis (r : ℕ+) : Analysis r := ⟨1, 1, fun _ => 0, fun _ => 0⟩
def atAnalysis {r : ℕ+} (a : List (Analysis r)) (i : ℕ) : Analysis r := a.getD i (zeroAnalysis r)

/-- Lines 2–3 of Algorithm 1, with all error rules rewritten in restored errors.
    The magnitude field records the chosen certified rational bound at this node.
    ValidCircuit checks it against the exact logical values; sharper bounds are permitted. -/
def nextAnalysis {r : ℕ+} (w : Weights r) (prev : List (Analysis r)) (v : Node r) : Analysis r :=
  let a := fun i => atAnalysis prev i
  let wp := weightPoly w
  match v.op with
  | .fresh => ⟨v.inputModulus, v.inputScale, v.valueBound,
      fun j => wp j * lc ((v.encBound + v.decBound) / v.inputScale)⟩
  | .add i k | .sub i k => ⟨(a i).modulus, (a i).scale,
      v.valueBound,
      fun j => (a i).error j + (a k).error j⟩
  | .addPlain i => ⟨(a i).modulus, (a i).scale,
      v.valueBound,
      fun j => (a i).error j + wp j * lc (v.addBound / (a i).scale)⟩
  | .multPlain i => ⟨(a i).modulus, (a i).scale * v.plainScale,
      v.valueBound,
      fun j => lc (v.plainBound j + v.beta j) * (a i).error j + lc ((a i).magnitude j * v.beta j)⟩
  | .mult i k => ⟨(a i).modulus, (a i).scale * (a k).scale,
      v.valueBound,
      fun j => lc ((a i).magnitude j) * (a k).error j +
        lc ((a k).magnitude j) * (a i).error j + (a i).error j * (a k).error j +
        wp j * lc (v.keyBound / ((a i).scale * (a k).scale))⟩
  | .multRS i k => ⟨(a i).modulus / v.divisor, (a i).scale * (a k).scale / v.divisor,
      v.valueBound,
      fun j => lc ((a i).magnitude j) * (a k).error j +
        lc ((a k).magnitude j) * (a i).error j + (a i).error j * (a k).error j +
        wp j * lc ((v.keyBound + v.residueBound) / ((a i).scale * (a k).scale))⟩
  | .rs i => ⟨(a i).modulus / v.divisor, (a i).scale / v.divisor, v.valueBound,
      fun j => (a i).error j + wp j * lc (v.residueBound / (a i).scale)⟩
  | .modReduce i => ⟨v.reducedModulus, (a i).scale, v.valueBound, (a i).error⟩
  | .auto i tau => ⟨(a i).modulus, (a i).scale, v.valueBound,
      fun j => (a i).error (tau.perm j) + wp j * lc (v.keyBound / (a i).scale)⟩

def analyze {r : ℕ+} (w : Weights r) (c : Circuit r) : List (Analysis r) :=
  c.nodes.foldl (fun acc v => acc ++ [nextAnalysis w acc v]) []

/-- Checks only data admissibility, operation alignment, and acyclicity, never desired error bounds. -/
def ValidNode {r : ℕ+} (prev : List (Analysis r)) (v : Node r) : Prop :=
  (∀ i ∈ inputs v.op, i < prev.length) ∧
  (∀ j, 0 ≤ v.valueBound j ∧ 0 ≤ v.plainBound j ∧ 0 ≤ v.beta j ∧
    ‖v.plain j‖ ≤ (v.plainBound j : ℝ)) ∧
  0 ≤ v.encBound ∧ 0 ≤ v.decBound ∧ 0 ≤ v.keyBound ∧ 0 ≤ v.residueBound ∧ 0 ≤ v.addBound ∧
  let a := fun i => atAnalysis prev i
  match v.op with
  | .fresh => 1 < v.inputModulus ∧ Odd v.inputModulus ∧ 0 < v.inputScale
  | .add i k | .sub i k => (a i).modulus = (a k).modulus ∧ (a i).scale = (a k).scale
  | .multPlain _ => 0 < v.plainScale
  | .mult i k => (a i).modulus = (a k).modulus
  | .multRS i k => (a i).modulus = (a k).modulus ∧ 1 < v.divisor ∧ Odd v.divisor ∧
      v.divisor ∣ (a i).modulus ∧ 1 < (a i).modulus / v.divisor
  | .rs i => 1 < v.divisor ∧ Odd v.divisor ∧ v.divisor ∣ (a i).modulus ∧
      1 < (a i).modulus / v.divisor
  | .modReduce i => 1 < v.reducedModulus ∧ v.reducedModulus ∣ (a i).modulus
  | _ => True

/-- Intended values depend only on the logical circuit, not on allocation, ciphertexts or errors. -/
def nextValue {r : ℕ+} (prev : List (Vector r)) (v : Node r) : Vector r :=
  let a := fun i => prev.getD i (fun _ => 0)
  match v.op with
  | .fresh => v.input
  | .add i k => fun j => a i j + a k j
  | .sub i k => fun j => a i j - a k j
  | .addPlain i => fun j => a i j + v.plain j
  | .multPlain i => fun j => a i j * v.plain j
  | .mult i k | .multRS i k => fun j => a i j * a k j
  | .rs i | .modReduce i => a i
  | .auto i tau => move tau (a i)

def logicalValues {r : ℕ+} (c : Circuit r) : List (Vector r) :=
  c.nodes.foldl (fun acc v => acc ++ [nextValue acc v]) []

def ValidCircuit {r : ℕ+} (w : Weights r) (c : Circuit r) : Prop :=
  c.output < c.nodes.length ∧ ∀ i (h : i < c.nodes.length),
    ValidNode ((analyze w c).take i) (c.nodes[i]) ∧
      ∀ j, ‖((logicalValues c).getD i (fun _ => 0)) j‖ ≤ ((c.nodes[i]).valueBound j : ℝ)

/-- Choices actually made by encryption and evaluation keys; no distributions are imposed. -/
structure Noise (r : ℕ+) where
  ct : Cipher r
  relin : Cipher r
  decryption : Scalar r
  kappa : Scalar r
  correction : Scalar r

structure LogicalState (r : ℕ+) where
  value : Vector r
  message : Scalar r

def zeroLogical (r : ℕ+) : LogicalState r := ⟨fun _ => 0, 0⟩
def atLogical {r : ℕ+} (a : List (LogicalState r)) (i : ℕ) : LogicalState r := a.getD i (zeroLogical r)

def freshPlain {r : ℕ+} (p : Scalar r) (v : Node r) : Scalar r :=
  encode v.inputScale (fun j => v.input j / sigma p j)

def additivePlain {r : ℕ+} (p : Scalar r) (delta : ℚ) (v : Node r) : Scalar r :=
  encode delta (fun j => v.plain j / sigma p j)

def multiplicativePlain {r : ℕ+} (v : Node r) : Scalar r := encode v.plainScale v.plain

/-- The restored polynomial is constructed by the exact operation identities, never freely assumed. -/
def nextLogical {r : ℕ+} (p s : Scalar r) (prev : List (LogicalState r))
    (aprev : List (Analysis r)) (v : Node r) (n : Noise r) (cts : ℕ → Noise r) : LogicalState r :=
  let a := fun i => atLogical prev i
  match v.op with
  | .fresh => ⟨v.input, p * (freshPlain p v + n.decryption)⟩
  | .add i k => ⟨fun j => (a i).value j + (a k).value j, (a i).message + (a k).message⟩
  | .sub i k => ⟨fun j => (a i).value j - (a k).value j, (a i).message - (a k).message⟩
  | .addPlain i => ⟨fun j => (a i).value j + v.plain j,
      (a i).message + p * additivePlain p (atAnalysis aprev i).scale v⟩
  | .multPlain i => ⟨fun j => (a i).value j * v.plain j, multiplicativePlain v * (a i).message⟩
  | .mult i k => ⟨fun j => (a i).value j * (a k).value j, (a i).message * (a k).message + p * n.kappa⟩
  | .multRS i k => ⟨fun j => (a i).value j * (a k).value j,
      rescaledMessage v.divisor p s ((a i).message * (a k).message + p * n.kappa) n.relin⟩
  | .rs i => ⟨(a i).value, rescaledMessage v.divisor p s (a i).message (cts i).ct⟩
  | .modReduce i => a i
  | .auto i tau => ⟨move tau (a i).value, tau.aut (a i).message + p * n.kappa⟩

def logicalRun {r : ℕ+} (w : Weights r) (c : Circuit r) (p s : Scalar r)
    (noise : ℕ → Noise r) : List (LogicalState r) :=
  c.nodes.foldl (fun acc v => acc ++ [nextLogical p s acc ((analyze w c).take acc.length)
    v (noise acc.length) noise]) []

/-- Actual operation equations plus precisely the primitive bounds, on their joint event. -/
def ExecutesNode {r : ℕ+} (p s : Scalar r) (a : List (Analysis r))
    (v : Node r) (n : Noise r) (noise : ℕ → Noise r) : Prop :=
  IntegralCipher n.ct ∧
  let an := fun i => atAnalysis a i
  let ct := fun i => (noise i).ct
  match v.op with
  | .fresh => InRing n.decryption ∧
      Congruent v.inputModulus (phase s n.ct) (freshPlain p v + n.decryption) ∧
      ∀ j, ‖sigma (freshPlain p v) j - (v.inputScale : ℂ) * (v.input j / sigma p j)‖ ≤ (v.encBound : ℝ) ∧
        ‖sigma n.decryption j‖ ≤ (v.decBound : ℝ)
  | .add i k => n.ct = addCipher (an i).modulus (ct i) (ct k)
  | .sub i k => n.ct = subCipher (an i).modulus (ct i) (ct k)
  | .addPlain i => n.ct = addPlainCipher (an i).modulus (ct i) (additivePlain p (an i).scale v) ∧
      ∀ j, ‖sigma (additivePlain p (an i).scale v) j -
        ((an i).scale : ℂ) * (v.plain j / sigma p j)‖ ≤ (v.addBound : ℝ)
  | .multPlain i => n.ct = multPlainCipher (an i).modulus (ct i) (multiplicativePlain v) ∧
      ∀ j, ‖sigma (multiplicativePlain v) j / (v.plainScale : ℂ) - v.plain j‖ ≤ (v.beta j : ℝ)
  | .mult i k => Relin (an i).modulus p s (ct i) (ct k) n.ct n.kappa ∧
      ∀ j, ‖sigma n.kappa j‖ ≤ (v.keyBound : ℝ)
  | .multRS i k => Relin (an i).modulus p s (ct i) (ct k) n.relin n.kappa ∧
      n.ct = rescale v.divisor ((an i).modulus / v.divisor) n.relin ∧
      ∀ j, ‖sigma n.kappa j‖ ≤ (v.keyBound : ℝ) ∧
        ‖sigma (phase s (residues v.divisor n.relin)) j‖ ≤ (v.residueBound : ℝ)
  | .rs i => n.ct = rescale v.divisor ((an i).modulus / v.divisor) (ct i) ∧
      ∀ j, ‖sigma (phase s (residues v.divisor (ct i))) j‖ ≤ (v.residueBound : ℝ)
  | .modReduce i => n.ct = centeredCipher v.reducedModulus (ct i)
  | .auto i tau => InRing n.correction ∧ InRing n.kappa ∧
      Congruent (an i).modulus (p * n.correction) (tau.aut p) ∧
      Congruent (an i).modulus (phase s n.ct)
        (n.correction * (tau.aut (ct i).c0 + tau.aut (ct i).c1 * tau.aut s) + n.kappa) ∧
      ∀ j, ‖sigma n.kappa j‖ ≤ (v.keyBound : ℝ)

def JointExecution {r : ℕ+} (w : Weights r) (c : Circuit r) (p s : Scalar r)
    (noise : ℕ → Noise r) : Prop :=
  InRing s ∧ ∀ i (h : i < c.nodes.length),
    ExecutesNode p s ((analyze w c).take i) c.nodes[i] (noise i) noise

end CKKSPrecision.FourierUnits.Supplement


