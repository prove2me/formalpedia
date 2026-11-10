-- Prove2me | Definitions.Def_FineGrainedEF_Main_BoolCircuits
-- name    : FineGrainedEF_Main_BoolCircuits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:08:55.907674+00:00
-- url     : https://prove2.me/theorems/0141cf9d-13cd-4905-b428-cd076ebfa9db
-- title:
--   Boolean gadgets: ∧, ∨, ↔, ⊕, constants, balanced AND/OR trees, EQ, Mux, Sel and hardwired encodings
-- statement:
--   Over the gate basis $\{\top,\neg,\to\}$ of the EF definition, the connectives are fixed sub-circuits: $a\wedge b:=\neg(a\to\neg b)$ (3 gates), $a\vee b:=\neg a\to b$ (2 gates), $a\leftrightarrow b:=(a\to b)\wedge(b\to a)$ (5 gates), $a\oplus b:=\neg(a\leftrightarrow b)$ (6 gates); the constant one is a $\top$ gate and the constant zero is $\neg\top$.
--
--   **Trees** (p. 9). $\bigwedge_{j<m}P_j$ and $\bigvee_{j<m}P_j$ are balanced binary AND / OR trees over the leaves $P_0,\dots,P_{m-1}$: one leaf is returned as is, otherwise the first $\lceil m/2\rceil$ leaves form the left subtree and the rest the right subtree (for $m$ a power of two this is the paper's balanced tree; the paper also uses $\bigwedge_{j<w}$ for arbitrary widths $w$).
--
--   **Equality check** (p. 56). For bit strings, $\mathrm{EQ}(x,y):=\bigwedge_{j<w}(x_j\leftrightarrow y_j)$; strings of different lengths are first zero-padded to the common length (p. 50).
--
--   **Multiplexer and selector** (p. 10). $\mathrm{Mux}(c,x,y)_j:=(c\wedge x_j)\vee(\neg c\wedge y_j)$ selects $x$ when $c=1$. For an array $A=(A_0,\dots,A_{m-1})$, $m=2^s$, and an $s$-bit address $i$ (least significant bit first), $\mathrm{Sel}(A,i)$ is the balanced tree of word multiplexers in which the most significant address bit selects the lower half when it is $0$ and the upper half when it is $1$; for $m=1$ it is $A_0$.
--
--   **Hardwired words.** A constant word wires each bit to a fresh $\top$ or $\neg\top$ gate; the hardwired $s$-bit encoding of $j$ is the constant word of $j$.
--
--   **Formalization Note.** `notG`, `impG`, `oneG`, `zeroG`, `andG`, `orG`, `iffG`, `xorG`, `andTree`, `orTree`, `zeroExt`, `signExt`, `eqBits`, `mux`, `sel`, `constWord`, `encAddr`. Words are `List ℕ` of wire names, least significant bit first.
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 9 (Boolean trees), p. 10 (Mux, Sel), p. 56 (EQ), p. 50 (zero-padding before comparison)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF

namespace FineGrainedEF.Main

/-- `¬a`: one gate. -/
def notG (a : ℕ) : Build ℕ := Build.gate .neg [a]

/-- `a → b`: one gate. -/
def impG (a b : ℕ) : Build ℕ := Build.gate .imp [a, b]

/-- The constant one: one `⊤` gate. -/
def oneG : Build ℕ := Build.gate .top []

/-- The constant zero: `¬⊤`, two gates. -/
def zeroG : Build ℕ := do
  let t ← oneG
  notG t

/-- `a ∧ b := ¬(a → ¬b)`: three gates. -/
def andG (a b : ℕ) : Build ℕ := do
  let nb ← notG b
  let i ← impG a nb
  notG i

/-- `a ∨ b := ¬a → b`: two gates. -/
def orG (a b : ℕ) : Build ℕ := do
  let na ← notG a
  impG na b

/-- `a ↔ b := (a → b) ∧ (b → a)`: five gates. -/
def iffG (a b : ℕ) : Build ℕ := do
  let i₁ ← impG a b
  let i₂ ← impG b a
  andG i₁ i₂

/-- `a ⊕ b := ¬(a ↔ b)`: six gates. -/
def xorG (a b : ℕ) : Build ℕ := do
  let e ← iffG a b
  notG e

/-- Balanced binary tree over the leaves `l`, combining with `op`; `fuel ≥ l.length`. A single
leaf is returned as is (no gate); otherwise the first `⌈|l|/2⌉` leaves form the left subtree and
the rest the right subtree. The empty tree is the constant `empty`. -/
def treeAux (op : ℕ → ℕ → Build ℕ) (empty : Build ℕ) : ℕ → List ℕ → Build ℕ
  | 0, _ => empty
  | fuel + 1, l =>
      match l with
      | [] => empty
      | [a] => pure a
      | l => do
          let k := (l.length + 1) / 2
          let x ← treeAux op empty fuel (l.take k)
          let y ← treeAux op empty fuel (l.drop k)
          op x y

/-- `⋀_{j<m} P_j` (p. 9): the balanced binary AND tree over the leaves `P_0, …, P_{m-1}`. -/
def andTree (l : List ℕ) : Build ℕ := treeAux andG oneG l.length l

/-- `⋁_{j<m} P_j` (p. 9): the balanced binary OR tree over the leaves. -/
def orTree (l : List ℕ) : Build ℕ := treeAux orG zeroG l.length l

/-- Zero-extension of an unsigned word to width `w` (p. 43): the new high bits are wired to one
fresh constant-zero gate; no change if the word is already at least `w` bits long. -/
def zeroExt (w : ℕ) (x : List ℕ) : Build (List ℕ) :=
  if x.length < w then do
    let z ← zeroG
    pure (x ++ List.replicate (w - x.length) z)
  else pure x

/-- Sign-extension of a signed word to width `w` (p. 44): copies of the sign bit (wiring only);
the empty word extends to constant zeros. -/
def signExt (w : ℕ) (x : List ℕ) : Build (List ℕ) :=
  match x.getLast? with
  | some s => pure (x ++ List.replicate (w - x.length) s)
  | none =>
      if w = 0 then pure []
      else do
        let z ← zeroG
        pure (List.replicate w z)

/-- The binary-string equality check (p. 56): `EQ(x, y) := ⋀_{j<w} (x_j ↔ y_j)`, a balanced AND
tree of `↔` gates. Strings of different lengths are first zero-padded to the common length
(p. 50: "corresponding output strings are zero-padded to a common length before comparison"). -/
def eqBits (x y : List ℕ) : Build ℕ := do
  let w := max x.length y.length
  let x' ← zeroExt w x
  let y' ← zeroExt w y
  let es ← (List.zip x' y').mapM fun p => iffG p.1 p.2
  andTree es

/-- The word multiplexer `Mux(c, x, y)` (p. 10): output bit `j` is `(c ∧ x_j) ∨ (¬c ∧ y_j)`
(one shared `¬c` gate); it selects `x` when `c = 1`. -/
def mux (c : ℕ) (x y : List ℕ) : Build (List ℕ) := do
  let nc ← notG c
  (List.zip x y).mapM fun p => do
    let u ← andG c p.1
    let v ← andG nc p.2
    orG u v

/-- `Sel_{m,w}(A, i)` for `m = 2^s` (p. 10): a balanced binary tree of word multiplexers; the
most significant address bit `i_{s-1}` selects the lower half `A_0, …, A_{m/2-1}` when it is zero
and the upper half when it is one, the remaining bits select recursively within that half; for
`m = 1` the output is `A_0` itself. Addresses are LSB first. -/
def selAux : ℕ → List (List ℕ) → List ℕ → Build (List ℕ)
  | 0, A, _ => pure (A.headD [])
  | s + 1, A, i => do
      let lo ← selAux s (A.take (2 ^ s)) i
      let hi ← selAux s (A.drop (2 ^ s)) i
      mux (i.getD s 0) hi lo

/-- `Sel(A, i)` with an `s`-bit address `i`, `s = |i|`. -/
def sel (A : List (List ℕ)) (i : List ℕ) : Build (List ℕ) := selAux i.length A i

/-- A hardwired constant word: bit `j` of the natural number `v`, `j < w`, LSB first, each wired
to one of two fresh constant gates (one `⊤`, one `¬⊤`). -/
def constWord (v w : ℕ) : Build (List ℕ) := do
  let o ← oneG
  let z ← zeroG
  pure ((List.range w).map fun j => if v.testBit j then o else z)

/-- The hardwired `s`-bit encoding of `j` (Lemmas B.5, B.8). -/
def encAddr (s j : ℕ) : Build (List ℕ) := constWord j s

end FineGrainedEF.Main


