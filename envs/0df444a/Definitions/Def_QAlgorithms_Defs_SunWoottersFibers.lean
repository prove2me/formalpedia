-- Prove2me | Definitions.Def_QAlgorithms_Defs_SunWoottersFibers
-- name    : QAlgorithms_Defs_SunWoottersFibers
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:35:51.531439+00:00
-- url     : https://prove2.me/theorems/69ae6d4b-5927-4d2a-8504-082f774a31fd
-- title:
--   SunWoottersFibers
-- statement:
--   SunWoottersFibers
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SunWoottersFibers.lean

import Definitions.Def_QAlgorithms_Defs_SunWoottersData
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.SunWootters

/-- Entire supported syndrome fiber; 2607.16541 p.9 (23). -/
def shellFiber {p m n : ℕ} [NeZero p] (H : Matrix (Fin n) (Fin m) (ZMod p))
    (D : ShellDomain m) (s : Fin n → ZMod p) : Finset (Fin m → ZMod p) :=
  Finset.univ.filter fun y => H.mulVec y = s ∧ hammingNorm y ∈ shell D

/-- Complex product amplitude over nonzero coordinates; 2607.16541 p.9 (21). -/
def errorAmplitude {p m : ℕ} (g : Fin m → ZMod p → ℂ) (D : ShellDomain m)
    (y : Fin m → ZMod p) : ℂ :=
  (shellWeights D (hammingNorm y) : ℂ)*
    ∏ i ∈ Finset.univ.filter (fun i => y i ≠ 0), g i (y i)

/-- Squared norm before coherent summation; 2607.16541 p.9 (22). -/
def errorNormSq {p m : ℕ} [NeZero p] (g : Fin m → ZMod p → ℂ) (D : ShellDomain m) : ℝ :=
  ∑ y : Fin m → ZMod p, Complex.normSq (errorAmplitude g D y)

/-- Normalized labelled error-syndrome vector on positive norm domain;
2607.16541 p.9 (22). -/
def labeledErrorState {p m n : ℕ} [NeZero p]
    (H : Matrix (Fin n) (Fin m) (ZMod p)) (g : Fin m → ZMod p → ℂ)
    (D : ShellDomain m) (_positive : 0 < errorNormSq g D) :
    EuclideanSpace ℂ ((Fin m → ZMod p) × (Fin n → ZMod p)) :=
  WithLp.toLp 2 fun ys => if H.mulVec ys.1 = ys.2
    then errorAmplitude g D ys.1/(Real.sqrt (errorNormSq g D) : ℂ) else 0

/-- Coherent, phase-sensitive sum, not a sum of probabilities;
2607.16541 p.9 (23). -/
def syndromeAmplitude {p m n : ℕ} [NeZero p]
    (H : Matrix (Fin n) (Fin m) (ZMod p)) (g : Fin m → ZMod p → ℂ)
    (D : ShellDomain m) (s : Fin n → ZMod p) : ℂ :=
  ∑ y ∈ shellFiber H D s, errorAmplitude g D y

/-- Squared norm after coherent summation; 2607.16541 p.9 (24). -/
def syndromeNormSq {p m n : ℕ} [NeZero p]
    (H : Matrix (Fin n) (Fin m) (ZMod p)) (g : Fin m → ZMod p → ℂ)
    (D : ShellDomain m) : ℝ :=
  ∑ s : Fin n → ZMod p, Complex.normSq (syndromeAmplitude H g D s)

/-- Normalized constructed syndrome vector on positive norm domain;
2607.16541 p.9 (24). -/
def syndromeState {p m n : ℕ} [NeZero p]
    (H : Matrix (Fin n) (Fin m) (ZMod p)) (g : Fin m → ZMod p → ℂ)
    (D : ShellDomain m) (_positive : 0 < syndromeNormSq H g D) :
    EuclideanSpace ℂ (Fin n → ZMod p) :=
  WithLp.toLp 2 fun s => syndromeAmplitude H g D s/(Real.sqrt (syndromeNormSq H g D) : ℂ)

/-- Johnson-domain global power-of-two padding (L,q);
2607.16541 pp.11–12 (35)–(36). Positive denominator is required explicitly. -/
def listPadding (m n ell : ℕ) (_domain : 0 < n ∧ n < m ∧ ell ≤ m ∧
    Real.sqrt (((m : ℝ)-n-1)*m) < (m : ℝ)-ell) : ℕ × ℕ :=
  let a := (m : ℝ)-ell
  let k := (m : ℝ)-n
  let bound := max 1 ⌈(a-(k-1))/(a^2/m-(k-1))⌉₊
  let q := Nat.clog 2 bound
  (2^q,q)

/-- Full-basis reversible canonical indexer; 2607.16541 pp.12–13 (37).
First XOR the match index/flag, then subtract the selected error iff flag is set.
Unmatched input uses zero index/flag; a match at index zero is distinguished. -/
def listIndexer {p m n : ℕ} [NeZero p] (q : ℕ)
    (lists : (Fin n → ZMod p) → List (Fin m → ZMod p))
    (_nodup : ∀ s, (lists s).Nodup) (_fits : ∀ s, (lists s).length ≤ 2^q) :
    Matrix (((Fin m → ZMod p) × (Fin n → ZMod p)) × (Qubits q × Bool))
      (((Fin m → ZMod p) × (Fin n → ZMod p)) × (Qubits q × Bool)) ℂ :=
  let find := fun y s => (List.range (lists s).length).find? fun j => (lists s).getD j 0 = y
  let compute := fun z =>
    let result := find z.1.1 z.1.2
    (z.1,(z.2.1+natToBits q (result.getD 0),xor z.2.2 result.isSome))
  let subtract := fun z =>
    ((z.1.1-(if z.2.2 then (lists z.1.2).getD (bitsToNat z.2.1) 0 else 0),z.1.2),z.2)
  Matrix.of fun y z => if y = subtract (compute z) then 1 else 0

example {p m : ℕ} (g : Fin m → ZMod p → ℂ) (D : ShellDomain m)
    (y : Fin m → ZMod p) (h : hammingNorm y ∉ shell D) :
    errorAmplitude g D y = 0 := by simp [errorAmplitude,shellWeights,h]

end QAlgorithms.SunWootters


