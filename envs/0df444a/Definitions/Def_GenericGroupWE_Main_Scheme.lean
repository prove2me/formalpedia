-- Prove2me | Definitions.Def_GenericGroupWE_Main_Scheme
-- name    : GenericGroupWE_Main_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:48.74268+00:00
-- url     : https://prove2.me/theorems/aff6fcef-028d-4ced-b403-3d7fc5df7fa7
-- title:
--   Explicit rank-gap encryption, bounded sampling, and oracle decryption
-- statement:
--   Let $M_1,\ldots,M_k$ be $m\times m$ matrices over $\mathbb F_p$. A certificate consists of coefficients $a$ and factors $u,v$; validity means $\sum_j a_jM_j=uv^T\ne0$ with every coordinate of $v$ zero or one. Independently sample $s\in\mathbb F_p^m$, $r\in\{1,\ldots,m\}^m$ and $t\in\mathbb F_p^k$, as well as a fresh encoding.
--
--   $$X_i=[s_i],\qquad Y_j=\begin{cases}[s^TM_jr]&\beta=0,\\[t_j]&\beta=1.\end{cases}$$
--
--   Let $n$ be the effective input size. Bounded rejection sampling uses the minimum sufficient bit length and $n+2+\lceil\log_2(2m+k)\rceil$ attempts per coordinate. Failure yields the same abort ciphertext for either bit. The module specifies both the exact and bounded laws.
--
--   The valid-witness decryption core uses only additions/subtractions: it computes $H=\sum_i u_iX_i$ and $Z=\sum_j a_jY_j$, then returns zero precisely when $Z\in\{H,2H,\ldots,m^2H\}$. Abort returns zero and malformed data returns failure. The full algorithms in Theorems 3.1 and 1.1 supply the witness check and conversion. Fixed linear tests and both conditional/unconditional advantage are explicit probability experiments.
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §3.1, eq. (1) and decryption, PDF pp. 8–9 (printed pp. 7–8); Lemma 3.2, PDF p. 9 (printed p. 8); §3.3, PDF pp. 9–10 (printed pp. 8–9).

import Definitions.Def_GenericGroupWE_Main_Oracle

namespace GenericGroupWE.Main

open scoped BigOperators

abbrev PrimeOrder := {p : ℕ // p.Prime}

instance primeOrderFact (p : PrimeOrder) : Fact p.val.Prime := ⟨p.property⟩

structure MatrixBundle (m : ℕ) (p : PrimeOrder) where
  k : ℕ
  matrices : Fin k → Matrix (Fin m) (Fin m) (ZMod p.val)

structure RankOneCertificate {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p) where
  coefficients : Fin B.k → ZMod p.val
  left : Fin m → ZMod p.val
  right : Fin m → ZMod p.val

noncomputable def MatrixBundle.combination {m : ℕ} {p : PrimeOrder}
    (B : MatrixBundle m p) (a : Fin B.k → ZMod p.val) :=
  ∑ j, a j • B.matrices j

def RankOneCertificate.Valid {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (w : RankOneCertificate B) : Prop :=
  B.combination w.coefficients = Matrix.vecMulVec w.left w.right ∧
    Matrix.vecMulVec w.left w.right ≠ 0 ∧ ∀ i, w.right i = 0 ∨ w.right i = 1

noncomputable def bundleBits {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p) : Bits :=
  pack ([m.bits, p.val.bits, B.k.bits] ++
    (List.ofFn fun j : Fin B.k => pack ((List.ofFn fun i : Fin m =>
      pack (List.ofFn fun l : Fin m => (B.matrices j i l).val.bits)))))

noncomputable def certificateBits {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (w : RankOneCertificate B) : Bits :=
  pack [pack (List.ofFn fun j => (w.coefficients j).val.bits),
    pack (List.ofFn fun i => (w.left i).val.bits),
    pack (List.ofFn fun i => (w.right i).val.bits)]

def encodeField {p : PrimeOrder} (σ : Encoding p.val) (z : ZMod p.val) : Bits :=
  label σ ⟨z.val, ZMod.val_lt z⟩

noncomputable def coordinateCiphertext {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (σ : Encoding p.val) (s : Fin m → ZMod p.val) (r : Fin m → ℕ)
    (t : Fin B.k → ZMod p.val) (message : Bool) : Ciphertext :=
  let Γ : GroupContext := ⟨p.val, p.property, σ⟩
  let X := List.ofFn fun i : Fin m => encodeField σ (s i)
  let Y := List.ofFn fun j : Fin B.k => encodeField σ
    (if message then t j else ∑ i : Fin m, ∑ l : Fin m,
      s i * B.matrices j i l * (r l : ZMod p.val))
  ⟨some Γ, some (pack [Γ.generator, pack X, pack Y])⟩

noncomputable def exactCoordinates {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (hm : 0 < m) : PMF ((Fin m → ZMod p.val) × (Fin m → Fin m) × (Fin B.k → ZMod p.val)) := by
  letI : NeZero m := ⟨hm.ne'⟩
  exact PMF.uniformOfFintype _

noncomputable def idealEncryption {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (hm : 0 < m) (message : Bool) : PMF Ciphertext :=
  (PMF.uniformOfFintype (Encoding p.val)).bind fun σ =>
    (exactCoordinates B hm).map fun (s,r,t) =>
      coordinateCiphertext B σ s (fun i => (r i).val+1) t message

/-- Minimum sufficient bit length; zero-sized ranges reject on every trial. -/
noncomputable def boundedUniform (D : ℕ) : ℕ → PMF (Option ℕ)
  | 0 => pure none
  | attempts+1 => (PMF.uniformOfFintype (Fin (2 ^ Nat.clog 2 D))).bind fun x =>
      if x.val < D then pure (some x.val) else boundedUniform D attempts

noncomputable def boundedCoordinates (attempts : ℕ) : List ℕ → PMF (Option (List ℕ))
  | [] => pure (some [])
  | D :: Ds => (boundedUniform D attempts).bind fun x =>
      (boundedCoordinates attempts Ds).map fun xs => do
        let x ← x
        let xs ← xs
        pure (x :: xs)

def coordinateBounds (m k p : ℕ) : List ℕ :=
  List.replicate m p ++ List.replicate m m ++ List.replicate k p

def coordinateAttempts (n m k : ℕ) : ℕ := n + 2 + Nat.clog 2 (2*m+k)

noncomputable def samplingLaw {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p) (n : ℕ) :=
  boundedCoordinates (coordinateAttempts n m B.k) (coordinateBounds m B.k p.val)

noncomputable def samplingFailure {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p) (n : ℕ) : ℝ :=
  probability (samplingLaw B n) (· = none)

noncomputable def boundedEncryption {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (n : ℕ) (message : Bool) : PMF Ciphertext :=
  (samplingLaw B n).bind fun result => match result with
    | none => pure abortCiphertext
    | some xs => (PMF.uniformOfFintype (Encoding p.val)).map fun σ =>
        coordinateCiphertext B σ
          (fun i => (xs.getD i.val 0 : ZMod p.val))
          (fun i => xs.getD (m+i.val) 0 + 1)
          (fun j => (xs.getD (2*m+j.val) 0 : ZMod p.val)) message

noncomputable def schemeInput {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p) (n : ℕ) (message : Bool) : Bits :=
  pack [List.replicate n true, bundleBits B, [message]]

/-- Oracle-only scalar multiplication, logarithmic in the scalar's binary length. -/
def scalarHandle (Γ : GroupContext) (zero handle : Bits) (scalar : ℕ) : Option Bits :=
  scalar.bits.foldr (fun bit acc => do
    let acc ← acc
    let doubled ← Γ.query false acc acc
    if bit then Γ.query false doubled handle else pure doubled) (some zero)

def linearHandle (Γ : GroupContext) (coefficients : List ℕ) (handles : List Bits) : Option Bits := do
  let zero ← Γ.query true Γ.generator Γ.generator
  (coefficients.zip handles).foldl (fun acc term => do
    let acc ← acc
    let term ← scalarHandle Γ zero term.2 term.1
    Γ.query false acc term) (some zero)

def multipleHandles (Γ : GroupContext) (H : Bits) : ℕ → Option (List Bits)
  | 0 => some []
  | n+1 => do
      let xs ← multipleHandles Γ H n
      let x ← match xs.getLast? with
        | none => some H
        | some x => Γ.query false x H
      pure (xs ++ [x])

/-- Parse exactly three packets from the §3.1 payload. -/
def schemeHandles (out : Bits) : Option (Bits × Bits × Bits) := do
  let (g, rest) ← unpacket out
  let (xs, rest) ← unpacket rest
  let (ys, tail) ← unpacket rest
  if tail.isEmpty then pure (g,xs,ys) else none

def unpackHandles : ℕ → Bits → Option (List Bits)
  | 0, bs => if bs.isEmpty then some [] else none
  | n+1, bs => do
      let (x, tail) ← unpacket bs
      let xs ← unpackHandles n tail
      pure (x :: xs)

noncomputable def schemeDecryption {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (w : RankOneCertificate B) (C : Ciphertext) : Option Bool :=
  match C.output with
  | none => some false
  | some out => do
      let Γ ← C.context
      if Γ.p ≠ p.val then none else do
        let (g, xs, ys) ← schemeHandles out
        if g ≠ Γ.generator then none else do
          let X ← unpackHandles m xs
          let Y ← unpackHandles B.k ys
          let H ← linearHandle Γ (List.ofFn fun i => (w.left i).val) X
          let Z ← linearHandle Γ (List.ofFn fun j => (w.coefficients j).val) Y
          let multiples ← multipleHandles Γ H (m*m)
          pure (!(multiples.contains Z))

noncomputable def schemeAdvantage {m : ℕ} {p : PrimeOrder} {q : ℕ}
    (B : MatrixBundle m p) (n : ℕ) (A : Adversary q) (conditional : Bool) (hm : 0 < m) : ℝ :=
  let law := fun b => if conditional then idealEncryption B hm b else boundedEncryption B n b
  |probability (adversaryOutput A (law false)) (· = true) -
    probability (adversaryOutput A (law true)) (· = true)|

noncomputable def fixedTestProbability {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (hm : 0 < m) (α : ZMod p.val) (β : Fin m → ZMod p.val)
    (γ : Fin B.k → ZMod p.val) (message : Bool) : ℝ :=
  probability (exactCoordinates B hm) fun (s,r,t) =>
    α + (∑ i, β i * s i) + (∑ j, γ j *
      (if message then t j else ∑ i : Fin m, ∑ l : Fin m,
        s i * B.matrices j i l * ((r l).val+1 : ℕ))) = 0

end GenericGroupWE.Main


