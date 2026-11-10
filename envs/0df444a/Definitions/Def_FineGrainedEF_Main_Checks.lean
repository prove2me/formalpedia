-- Prove2me | Definitions.Def_FineGrainedEF_Main_Checks
-- name    : FineGrainedEF_Main_Checks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:12:28.622689+00:00
-- url     : https://prove2.me/theorems/fe781b7b-6f02-4968-bb32-d34ddbedc6a6
-- title:
--   Check circuits of C.1 and array operators: numerical EQ, LE_u, LT_u, LT_s, LE_s, Abs, ‖·‖∞ ≤ e, M, W, Shift, CShift₁, Pad
-- statement:
--   **Equality** (C.1, p. 61): two unsigned integer words are zero-extended to a common width; otherwise both are put in a common signed representation (an unsigned word gets an extra zero sign bit) and sign-extended; then EQ. Array equality is the AND tree of the coordinate checks.
--
--   **Order** (p. 61). For unsigned words zero-extended to width $w$, the borrow chain of $Y-X$ is $b_0:=0$, $d_j:=y_j\oplus x_j\oplus b_j$, $b_{j+1}:=(\neg y_j\wedge(x_j\vee b_j))\vee(x_j\wedge b_j)$, and $\mathrm{LE}_u(X,Y):=\neg b_w$, $\mathrm{LT}_u(X,Y):=\neg b_w\wedge\neg\mathrm{EQ}(X,Y)$. For signed words sign-extended to a common width with sign bits $s_X,s_Y$: $\mathrm{LT}_s:=(s_X\wedge\neg s_Y)\vee((s_X\leftrightarrow s_Y)\wedge\mathrm{LT}_u)$ and $\mathrm{LE}_s:=\mathrm{LT}_s\vee\mathrm{EQ}$. A comparison of two unsigned words uses $\mathrm{LE}_u$, any other uses $\mathrm{LE}_s$ on the common signed representation.
--
--   **Norm** (p. 62). For an array $v$ of scale-zero integer words and a nonnegative bound word $E$, $\|v\|_\infty\le E$ is $\bigwedge_{j}\mathrm{LE}_u(\mathrm{Abs}(v_j),E)$. $M:=N^8$ is an integer literal (p. 123) and $\|h\|_\infty\le M$ uses it.
--
--   **Further checks.** $x=0$ compares with the literal $0$; $0\le x$ is $\mathrm{LE}_s(0,x)$; the range check $0\le x\le A$ is $(0\le x)\wedge(x\le A)$.
--
--   **Array operators.** Entrywise $a+b$ (AddInt), $a-b$ (SubInt), $-a$ (Neg), $2a$ (left shift); $(\mathrm{Shift}\,u)_j:=u_{j-1}$, $(\mathrm{Shift}\,u)_0:=0$ (p. 18); $(\mathrm{CShift}_1v)_j:=v_{j-1\bmod N}$ (p. 28); $\mathrm{Pad}_k$ appends high zero bits (p. 133); a bit array is read as two-bit scale-zero coefficients (p. 47). $NAB$ for unsigned bound words $A,B$ is $\mathrm{MulInt}(2^L A,B)$ with $A,B$ in signed representation. $W:=(L+1)^4$ (the paper: $W=O(L^4)$ bounds every width and scale, p. 53).
--
--   **Formalization Note.** `toSigned`, `eqNum`, `borrowChain`, `leU`, `ltU`, `ltS`, `leS`, `leNum`, `absNum`, `normLe`, `isZero`, `nonneg`, `rangeChk`, `arrEq`, `arrAdd`, `arrSub`, `arrNeg`, `arrDouble`, `arrShift`, `arrCShift1`, `bitsD0`, `pad`, `mLit`, `Wbound`, `nab`, `normLeM`, `IsWordArray` (a length-$N$ array of words of $\Gamma$ of widths in $[1,w_{\max}]$).
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), pp. 60-62, §C.1 (EQ, LE_u, LT_u, LT_s, LE_s, Abs, ‖·‖∞); Shift p. 18; CShift_1 p. 28; M p. 123; W p. 53; Pad p. 133

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith
import Definitions.Def_FineGrainedEF_Main_FFTMul

namespace FineGrainedEF.Main

/-- Common signed representation of an integer word (C.1, p. 61): a signed word is unchanged; an
unsigned word gets one extra zero sign bit. -/
def toSigned (x : List ℕ) (signed : Bool) : Build (List ℕ) :=
  if signed then pure x else zeroExt (x.length + 1) x

/-- Numerical equality check on integer words (C.1, p. 61, item 1); `sx`, `sy` say whether each
word is signed. Two unsigned words are zero-extended to a common width; otherwise both are put in
a common signed representation and sign-extended to a common width; then `EQ`. -/
def eqNum (x : List ℕ) (sx : Bool) (y : List ℕ) (sy : Bool) : Build ℕ :=
  if !sx && !sy then eqBits x y
  else do
    let x' ← toSigned x sx
    let y' ← toSigned y sy
    let w := max x'.length y'.length
    let x'' ← signExt w x'
    let y'' ← signExt w y'
    eqBits x'' y''

/-- The borrow chain of `Y - X` (C.1, p. 61): `d_j := (y_j ⊕ x_j) ⊕ b_j`,
`b_{j+1} := (¬y_j ∧ (x_j ∨ b_j)) ∨ (x_j ∧ b_j)`; returns the difference bits and the final borrow. -/
def borrowChain : List ℕ → List ℕ → ℕ → Build (List ℕ × ℕ)
  | x :: xs, y :: ys, b => do
      let t ← xorG y x
      let d ← xorG t b
      let ny ← notG y
      let xb ← orG x b
      let l ← andG ny xb
      let r ← andG x b
      let b' ← orG l r
      let rest ← borrowChain xs ys b'
      pure (d :: rest.1, rest.2)
  | _, _, b => pure ([], b)

/-- `LE_u(X, Y) := ¬b_w` (C.1, p. 61): zero-extend to a common width `w`, run the borrow chain with
`b_0 := 0`; checks `X ≤ Y` for unsigned words. -/
def leU (X Y : List ℕ) : Build ℕ := do
  let w := max X.length Y.length
  let X' ← zeroExt w X
  let Y' ← zeroExt w Y
  let z ← zeroG
  let r ← borrowChain X' Y' z
  notG r.2

/-- `LT_u(X, Y) := ¬b_w ∧ ¬EQ(X, Y)` (C.1, p. 61). -/
def ltU (X Y : List ℕ) : Build ℕ := do
  let le ← leU X Y
  let e ← eqBits X Y
  let ne ← notG e
  andG le ne

/-- `LT_s(X, Y) := (s_X ∧ ¬s_Y) ∨ ((s_X ↔ s_Y) ∧ LT_u(X, Y))` after sign-extension to a common
width (C.1, p. 61). -/
def ltS (X Y : List ℕ) : Build ℕ := do
  let w := max X.length Y.length
  let X' ← signExt w X
  let Y' ← signExt w Y
  let nsY ← notG (signBit Y')
  let t₁ ← andG (signBit X') nsY
  let t₂ ← iffG (signBit X') (signBit Y')
  let lu ← ltU X' Y'
  let t₃ ← andG t₂ lu
  orG t₁ t₃

/-- `LE_s(X, Y) := LT_s(X, Y) ∨ EQ(X, Y)` (C.1, p. 61), on the sign-extended words. -/
def leS (X Y : List ℕ) : Build ℕ := do
  let w := max X.length Y.length
  let X' ← signExt w X
  let Y' ← signExt w Y
  let lt ← ltS X' Y'
  let e ← eqBits X' Y'
  orG lt e

/-- The order check `x ≤ y` on integer words (C.1, p. 61): `LE_u` when both are unsigned;
otherwise `LE_s` on the common signed representation. -/
def leNum (x : List ℕ) (sx : Bool) (y : List ℕ) (sy : Bool) : Build ℕ :=
  if !sx && !sy then leU x y
  else do
    let x' ← toSigned x sx
    let y' ← toSigned y sy
    leS x' y'

/-- Absolute value of an integer word (C.1, p. 62): `Abs` for a signed word; an unsigned word is
already nonnegative. -/
def absNum (x : List ℕ) (signed : Bool) : Build (List ℕ) :=
  if signed then absInt x else pure x

/-- The check `‖v‖_∞ ≤ e` for a vector of scale-zero integer words and a nonnegative bound word `E`
(C.1, p. 62, item 1): `⋀_{j<N} LE(Abs(X_j), E)` with `LE = LE_u`, a balanced AND tree. -/
def normLe (v : List (List ℕ)) (signed : Bool) (E : List ℕ) : Build ℕ := do
  let cs ← v.mapM fun x => do
    let a ← absNum x signed
    leU a E
  andTree cs

/-- The check `x = 0` for an integer word (literal `0`, two signed bits). -/
def isZero (x : List ℕ) (signed : Bool) : Build ℕ := do
  let z ← intLit 0
  eqNum x signed z true

/-- The check `0 ≤ x` for a signed integer word. -/
def nonneg (x : List ℕ) : Build ℕ := do
  let z ← intLit 0
  leNum z true x true

/-- The range check `0 ≤ x ≤ A` for a signed word `x` and a bound word `A`:
`(0 ≤ x) ∧ (x ≤ A)`. -/
def rangeChk (x : List ℕ) (A : List ℕ) (signedA : Bool) : Build ℕ := do
  let z ← intLit 0
  let l ← leNum z true x true
  let u ← leNum x true A signedA
  andG l u

/-- Equality of two arrays of signed scale-zero words: the AND tree of the coordinate checks
(C.1, p. 61). -/
def arrEq (a b : List (List ℕ)) : Build ℕ := do
  let es ← (List.zip a b).mapM fun p => eqNum p.1 true p.2 true
  andTree es

/-- Entrywise `a + b` on scale-zero coefficient words (`AddInt`). -/
def arrAdd (a b : List (List ℕ)) : Build (List (List ℕ)) :=
  (List.zip a b).mapM fun p => addInt p.1 p.2

/-- Entrywise `a - b` (`SubInt`). -/
def arrSub (a b : List (List ℕ)) : Build (List (List ℕ)) :=
  (List.zip a b).mapM fun p => subInt p.1 p.2

/-- Entrywise `-a` (`Neg`). -/
def arrNeg (a : List (List ℕ)) : Build (List (List ℕ)) := a.mapM negInt

/-- Entrywise `2a` by left-shift wiring (p. 127). -/
def arrDouble (a : List (List ℕ)) : Build (List (List ℕ)) := a.mapM (shl 1)

/-- `Shift u` (p. 18): `(Shift u)_j := u_{j-1}` for `j ≥ 1`, `(Shift u)_0 := 0` (the literal 0);
same length as `u`. -/
def arrShift (u : List (List ℕ)) : Build (List (List ℕ)) := do
  let z ← intLit 0
  pure (z :: u.dropLast)

/-- `CShift_1 v` (p. 28): `(CShift_1 v)_j := v_{j-1}`, indices modulo the length; wiring only. -/
def arrCShift1 (v : List (List ℕ)) : List (List ℕ) :=
  match v.getLast? with
  | some l => l :: v.dropLast
  | none => []

/-- A bit array viewed as scale-zero coefficients: each bit zero-extended to a two-bit signed
numerator (p. 47, "a real bit coefficient uses two signed bits"; one fresh constant zero). -/
def bitsD0 (b : List ℕ) : Build (List (List ℕ)) := do
  let z ← zeroG
  pure (b.map fun x => [x, z])

/-- `Pad_k(v)` (p. 133): append high zero bits up to length `k`. -/
def pad (k : ℕ) (v : List ℕ) : Build (List ℕ) := zeroExt k v

/-- The literal `M = N^8` (p. 123). -/
def mLit (P : FFTParams) : Build (List ℕ) := intLit ((P.N : ℤ) ^ 8)

/-- `W` (p. 53): read as `(L + 1)^4`, a common `O(L^4)` bound on numerator widths and scales. -/
def Wbound (n : ℕ) : ℕ := ((paperParams n).L + 1) ^ 4

/-- `N A B` for nonnegative (unsigned) bound words `A, B` (Lemma G.2): `A, B` in signed
representation, `N A` by left shift by `L`, then `MulInt(N A, B)`. -/
def nab (P : FFTParams) (A B : List ℕ) : Build (List ℕ) := do
  let A' ← toSigned A false
  let B' ← toSigned B false
  let NA ← shl P.L A'
  mulInt NA B'

/-- The check `‖h‖_∞ ≤ M`, `M = N^8`, for an array of signed scale-zero words (p. 123, 126). -/
def normLeM (P : FFTParams) (h : List (List ℕ)) : Build ℕ := do
  let M ← mLit P
  normLe h true M

/-- `a` is an array of `N` signed scale-zero words of `Γ`, each of width between `1` and `wmax`. -/
def IsWordArray (Γ : Ctx) (a : List (List ℕ)) (N wmax : ℕ) : Prop :=
  a.length = N ∧ ∀ x ∈ a, 1 ≤ x.length ∧ x.length ≤ wmax ∧ Γ.HasWires x

end FineGrainedEF.Main


