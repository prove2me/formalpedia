-- Prove2me | Definitions.Def_EditGV897_Main_Affine
-- name    : EditGV897_Main_Affine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:24:26.525763+00:00
-- url     : https://prove2.me/theorems/197610ff-7556-4139-a100-c44513f04577
-- title:
--   Affine binary data and executable Gaussian counts
-- statement:
--   Let $\mathbb F_2$ be the two-element field. A length-$n$ word is an ordered coordinate vector, a row is another such vector, and an affine map has explicit matrix and offset data $f(x)=Ax+e$. A family is a finite list of maps, so equal maps at different indices remain separate occurrences. A row list $G$ defines the syndrome $(\langle g,x\rangle)_{g\in G}$.
--
--   An affine equation is a pair $(c,a)$ meaning $\langle c,x\rangle=a$. Gaussian elimination processes columns in order, chooses the first available pivot, and adds it to other rows with a nonzero pivot entry. Its counting output is
--
--   $$\operatorname{affineCount}(E)=\begin{cases}0,&\text{an inconsistent zero row remains},\\2^{n-r},&\text{otherwise, with }r\text{ nonzero echelon rows}.\end{cases}$$
--
--   These data and algorithms are the reusable linear-algebra input layer. Equality with the cardinality of the solution set and polynomial-time realization are theorem conclusions in Lemma 1.
--
--   **Formalization Note** Words use $\mathrm{Fin}\,n\to\mathrm{ZMod}\,2$ through the published word definition. Matrix and family serialization is dense and includes all entries. Full row rank means linear independence of the actual ordered rows.
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §§3.1–3.2, printed pp. 6–8 / PDF pp. 7–9

import Definitions.Def_EditGV897_Main_Machine
import Definitions.Def_DeletionHash_MixedEdit_Channel

namespace EditGV897.Main

abbrev Bit := ZMod 2
abbrev Word (n : ℕ) := DeletionHash.MixedEdit.Word Bit n
abbrev Equation (n : ℕ) := Word n × Bit
abbrev Rows (n : ℕ) := List (Word n)

def dot {n : ℕ} (x y : Word n) : Bit := ∑ i, x i * y i
def wordList {n : ℕ} (x : Word n) : List Bit := DeletionHash.MixedEdit.letters x
def bitCode (x : List Bit) : List Bool := x.map (fun a => decide (a ≠ 0))
def wordCode {n : ℕ} (x : Word n) : List Bool := bitCode (wordList x)
def listWord (n : ℕ) (p : List Bit) : Word n := fun i => p[i.val]?.getD 0

def unitWord (n k : ℕ) : Word n := fun i => if i.val = k then 1 else 0

structure Affine (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) Bit
  offset : Word n

abbrev Family (n : ℕ) := List (Affine n)

def Affine.apply {n : ℕ} (f : Affine n) (x : Word n) : Word n :=
  fun i => dot (f.matrix i) x + f.offset i

def difference {n : ℕ} (f : Affine n) : Affine n :=
  ⟨fun i j => (if i = j then 1 else 0) + f.matrix i j, f.offset⟩

def differenceAt {n : ℕ} (f : Affine n) (x : Word n) : Word n := x + f.apply x

def syndrome {n : ℕ} (G : Rows n) (x : Word n) : List Bit := G.map (fun h => dot h x)

def rowCode {n : ℕ} (G : Rows n) : List Bool := unary G.length ++ G.flatMap wordCode

def familyCode {n : ℕ} (F : Family n) : List Bool :=
  unary F.length ++ F.flatMap (fun f =>
    (List.ofFn (fun i : Fin n => wordCode (f.matrix i))).flatten ++ wordCode f.offset)

/-- Dense affine equations, Gaussian elimination left-to-right, retaining zero rows. -/
def xorEquation {n : ℕ} (a b : Equation n) : Equation n := (a.1 + b.1, a.2 + b.2)

def gaussian {n : ℕ} : ℕ → ℕ → List (Equation n) → List (Equation n)
  | 0, _, E => E
  | fuel + 1, k, E =>
    if hk : k < n then
      match E.find? (fun e => decide (e.1 ⟨k, hk⟩ ≠ 0)) with
      | none => gaussian fuel (k + 1) E
      | some pivot =>
        pivot :: gaussian fuel (k + 1)
          ((E.erase pivot).map (fun e =>
            if e.1 ⟨k, hk⟩ = 0 then e else xorEquation e pivot))
    else E

def pivotCount {n : ℕ} (E : List (Equation n)) : ℕ :=
  (E.filter (fun e => decide (e.1 ≠ 0))).length

def affineCount {n : ℕ} (E : List (Equation n)) : ℕ :=
  let R := gaussian n 0 E
  if R.any (fun e => decide (e.1 = 0 ∧ e.2 ≠ 0)) then 0
  else 2 ^ (n - pivotCount R)

def equationHolds {n : ℕ} (e : Equation n) (x : Word n) : Prop := dot e.1 x = e.2

def equationCode {n : ℕ} (E : List (Equation n)) : List Bool :=
  unary E.length ++ E.flatMap (fun e => wordCode e.1 ++ [decide (e.2 ≠ 0)])

def rowRank {n : ℕ} (G : Rows n) : ℕ :=
  pivotCount (gaussian n 0 (G.map (fun h => (h, 0))))

def FullRowRank {n : ℕ} (G : Rows n) : Prop :=
  LinearIndependent Bit (fun i : Fin G.length => G.get i)

end EditGV897.Main


