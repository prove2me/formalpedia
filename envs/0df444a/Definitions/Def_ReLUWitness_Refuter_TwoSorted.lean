-- Prove2me | Definitions.Def_ReLUWitness_Refuter_TwoSorted
-- name    : ReLUWitness_Refuter_TwoSorted
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:48:11.098207+00:00
-- url     : https://prove2.me/theorems/1ab5c83b-d8fa-438b-a187-7751e5abd757
-- title:
--   Two-sorted syntax and semantics with chosen FTC⁰ function symbols: terms, formulas, Σ^B_0, structures, programs of chosen definitions
-- statement:
--   **Sorts and symbols.** The language $\mathcal L^2_A$ of two-sorted bounded arithmetic has a **number** sort (intended range $\mathbb N$) with $0,1,+,\cdot,\le$ and a **string** sort (intended range: finite subsets of $\mathbb N$, read as binary strings) with the bit relation $X(i)$ ("$i\in X$") and the length $|X|$ (one more than the largest element, $0$ for the empty set). The language is extended by function symbols of two kinds:
--
--   * **primitive symbols** for the threshold-computable functions the paper imports (Fact 2.3, Fact 8.1): the counting function $\mathrm{numones}(y,X)$, row extraction $X[a]$, the empty string, binary addition, truncated subtraction, cut (bits below $b$), shift by $k$, iterated addition $\mathrm{isum}(b,X)=\sum_{a<b}X[a]$, binary multiplication, interval products $\mathrm{imul}(i,j,X)=\prod_{i\le a<j}X[a]$, quotient and remainder of division, and the magnitude and sign recodings of signed integers (each with a fixed signature: numbers of number and string arguments and result sort);
--   * **defined symbols** $F_k$, the $k$-th entry of a **program**: a finite list of chosen definitions.
--
--   **Terms and formulas.** Number terms are variables, $0$, $1$, $s+t$, $s\cdot t$, $|T|$ and applications of number-valued symbols; string terms are variables and applications of string-valued symbols. Formulas are built from $s=t$, $s\le t$, $T(s)$, $T=U$ with $\neg,\wedge,\vee$, bounded number quantifiers $\forall x\le t$, $\exists x\le t$ and unbounded quantifiers of both sorts. A formula is $\Sigma^B_0$ when it has only bounded number quantifiers and no string quantifiers. A **structure** consists of a number domain with $0,1,+,\cdot,\le$, a string domain with length and bit relation, and an interpretation of every symbol; satisfaction under an assignment is the usual Tarski definition, with equality of either sort read as identity.
--
--   **Chosen definitions.** A definition with $a$ number and $b$ string arguments is either a **bit-definition** $F(\vec x,\vec X)(i)\leftrightarrow i<t(\vec x,\vec X)\wedge\varphi(i,\vec x,\vec X)$ (a string function) or a **bounded minimization** $f(\vec x,\vec X)=$ the least $y<t$ with $\varphi(y,\vec x,\vec X)$, and $t$ if there is none (a number function), where $\varphi$ is $\Sigma^B_0$, its free variables are among the bound variable and the arguments, $t$ is a term in the arguments, and only primitives and earlier definitions occur, each with its signature. A program is **well formed** when every definition is. These are the chosen total $\mathrm{FTC}^0$ functions: each comes with its specified defining graph, and $\mathrm{FTC}^0$ is the closure of the counting function under $\mathrm{AC}^0$ reductions (composition, $\Sigma^B_0$ bit-definition and bounded minimization).
--
--   **Formalization Note.** Variables are indexed by natural numbers; in a definition the bound variable is number variable $0$, the number arguments are number variables $1,\dots,a$ and the string arguments string variables $0,\dots,b-1$. The binary order $X<_2Y$ of nonnegative binary integers (bit $i$ is the coefficient of $2^i$) and the pairing $\langle u,v\rangle=(u+v)(u+v+1)+2v$ of §2.1 are also defined here.
-- source:
--   Myrisiotis, A Witnessing Duality for ReLU Network Depth, arXiv:2610.38281v1, pp. 12-14, §2 and §2.1-2.2; p. 46, Fact 8.1

import Mathlib

open scoped Classical

namespace ReLUWitness.Refuter

/-! Two-sorted syntax of the language of VTC⁰ with its adjoined function symbols
(Myrisiotis, arXiv:2610.38281v1, §2 pp. 12-14 and §8 p. 46), its structures and
satisfaction, the Σ^B_0 class, and finite lists of chosen FTC⁰ definitions. -/

/-- The two sorts: numbers and strings (finite sets of numbers). -/
inductive Srt where
  | num
  | str
  deriving DecidableEq

/-- The imported threshold-computable functions of Fact 2.3 and Fact 8.1, adjoined as
primitive symbols of the extension: the counting function, row extraction, the empty
string, binary addition, truncated subtraction, cut and shift, iterated addition,
binary multiplication, iterated (interval) multiplication, division with remainder,
and the sign-bit recoding of canonical signed integers. -/
inductive Prim where
  | numones
  | row
  | empt
  | add
  | sub
  | cut
  | shl
  | isum
  | mul
  | imul
  | div
  | md
  | mag
  | sgnd
  deriving DecidableEq

/-- Signature of a primitive: (number arguments, string arguments, result sort). -/
def Prim.sig : Prim → ℕ × ℕ × Srt
  | .numones => (1, 1, .num)
  | .row => (1, 1, .str)
  | .empt => (0, 0, .str)
  | .add => (0, 2, .str)
  | .sub => (0, 2, .str)
  | .cut => (1, 1, .str)
  | .shl => (1, 1, .str)
  | .isum => (1, 1, .str)
  | .mul => (0, 2, .str)
  | .imul => (2, 1, .str)
  | .div => (0, 2, .str)
  | .md => (0, 2, .str)
  | .mag => (0, 1, .str)
  | .sgnd => (1, 1, .str)

/-- A function symbol: a primitive, or the `k`-th definition of a program. -/
inductive Sym where
  | prim : Prim → Sym
  | defd : ℕ → Sym
  deriving DecidableEq

mutual
/-- Number terms over 0, 1, +, ·, |·| and the function symbols. -/
inductive NT where
  | var : ℕ → NT
  | zero : NT
  | one : NT
  | add : NT → NT → NT
  | mul : NT → NT → NT
  | len : ST → NT
  | app : Sym → NArgs → SArgs → NT
/-- String terms: variables and string-valued function symbols. -/
inductive ST where
  | var : ℕ → ST
  | app : Sym → NArgs → SArgs → ST
/-- Lists of number arguments. -/
inductive NArgs where
  | nil : NArgs
  | cons : NT → NArgs → NArgs
/-- Lists of string arguments. -/
inductive SArgs where
  | nil : SArgs
  | cons : ST → SArgs → SArgs
end

/-- Two-sorted formulas. `ballN v t φ` is the bounded quantifier `∀ v ≤ t, φ` and `bexN v t φ`
is `∃ v ≤ t, φ` (the bound is evaluated outside the scope of `v`); `allN`, `exN`, `allS`,
`exS` are unbounded number and string quantifiers. -/
inductive Fml where
  | eqN : NT → NT → Fml
  | leN : NT → NT → Fml
  | mem : NT → ST → Fml
  | eqS : ST → ST → Fml
  | neg : Fml → Fml
  | and : Fml → Fml → Fml
  | or : Fml → Fml → Fml
  | ballN : ℕ → NT → Fml → Fml
  | bexN : ℕ → NT → Fml → Fml
  | allN : ℕ → Fml → Fml
  | exN : ℕ → Fml → Fml
  | allS : ℕ → Fml → Fml
  | exS : ℕ → Fml → Fml

/-- Σ^B_0: only bounded number quantifiers, no string quantifiers. -/
def Fml.isSigmaB0 : Fml → Bool
  | .eqN _ _ => true
  | .leN _ _ => true
  | .mem _ _ => true
  | .eqS _ _ => true
  | .neg φ => φ.isSigmaB0
  | .and φ ψ => φ.isSigmaB0 && ψ.isSigmaB0
  | .or φ ψ => φ.isSigmaB0 && ψ.isSigmaB0
  | .ballN _ _ φ => φ.isSigmaB0
  | .bexN _ _ φ => φ.isSigmaB0
  | .allN _ _ => false
  | .exN _ _ => false
  | .allS _ _ => false
  | .exS _ _ => false

def NArgs.length : NArgs → ℕ
  | .nil => 0
  | .cons _ as => as.length + 1

def SArgs.length : SArgs → ℕ
  | .nil => 0
  | .cons _ as => as.length + 1

mutual
/-- Well-formedness of a number term: every symbol is allowed by `sig` and applied with its
signature, every free number variable satisfies `okN` and every string variable `okS`. -/
def NT.ok (sig : Sym → Option (ℕ × ℕ × Srt)) (okN okS : ℕ → Bool) : NT → Bool
  | .var v => okN v
  | .zero => true
  | .one => true
  | .add a b => a.ok sig okN okS && b.ok sig okN okS
  | .mul a b => a.ok sig okN okS && b.ok sig okN okS
  | .len X => X.ok sig okN okS
  | .app f as Xs =>
      (match sig f with
        | some (a, b, .num) => as.length == a && Xs.length == b
        | _ => false) && as.ok sig okN okS && Xs.ok sig okN okS
def ST.ok (sig : Sym → Option (ℕ × ℕ × Srt)) (okN okS : ℕ → Bool) : ST → Bool
  | .var v => okS v
  | .app f as Xs =>
      (match sig f with
        | some (a, b, .str) => as.length == a && Xs.length == b
        | _ => false) && as.ok sig okN okS && Xs.ok sig okN okS
def NArgs.ok (sig : Sym → Option (ℕ × ℕ × Srt)) (okN okS : ℕ → Bool) : NArgs → Bool
  | .nil => true
  | .cons a as => a.ok sig okN okS && as.ok sig okN okS
def SArgs.ok (sig : Sym → Option (ℕ × ℕ × Srt)) (okN okS : ℕ → Bool) : SArgs → Bool
  | .nil => true
  | .cons a as => a.ok sig okN okS && as.ok sig okN okS
end

/-- Well-formedness of a formula; binders extend the allowed free variables. -/
def Fml.ok (sig : Sym → Option (ℕ × ℕ × Srt)) : (ℕ → Bool) → (ℕ → Bool) → Fml → Bool
  | okN, okS, .eqN a b => a.ok sig okN okS && b.ok sig okN okS
  | okN, okS, .leN a b => a.ok sig okN okS && b.ok sig okN okS
  | okN, okS, .mem a X => a.ok sig okN okS && X.ok sig okN okS
  | okN, okS, .eqS X Y => X.ok sig okN okS && Y.ok sig okN okS
  | okN, okS, .neg φ => φ.ok sig okN okS
  | okN, okS, .and φ ψ => φ.ok sig okN okS && ψ.ok sig okN okS
  | okN, okS, .or φ ψ => φ.ok sig okN okS && ψ.ok sig okN okS
  | okN, okS, .ballN v t φ => t.ok sig okN okS && φ.ok sig (fun w => w == v || okN w) okS
  | okN, okS, .bexN v t φ => t.ok sig okN okS && φ.ok sig (fun w => w == v || okN w) okS
  | okN, okS, .allN v φ => φ.ok sig (fun w => w == v || okN w) okS
  | okN, okS, .exN v φ => φ.ok sig (fun w => w == v || okN w) okS
  | okN, okS, .allS v φ => φ.ok sig okN (fun w => w == v || okS w)
  | okN, okS, .exS v φ => φ.ok sig okN (fun w => w == v || okS w)

/-- A two-sorted structure for the language with all symbols: a number domain with
0, 1, +, ·, ≤, a string domain with length and bit relation, and an interpretation of
every function symbol on argument lists. Equality of either sort is true equality. -/
structure Structure where
  N : Type
  S : Type
  zero : N
  one : N
  add : N → N → N
  mul : N → N → N
  le : N → N → Prop
  len : S → N
  mem : N → S → Prop
  nfun : Sym → List N → List S → N
  sfun : Sym → List N → List S → S

/-- Variable assignments for both sorts. -/
structure Assignment (M : Structure) where
  n : ℕ → M.N
  s : ℕ → M.S

def Assignment.setN {M : Structure} (ρ : Assignment M) (v : ℕ) (a : M.N) : Assignment M :=
  ⟨Function.update ρ.n v a, ρ.s⟩

def Assignment.setS {M : Structure} (ρ : Assignment M) (v : ℕ) (X : M.S) : Assignment M :=
  ⟨ρ.n, Function.update ρ.s v X⟩

mutual
def NT.eval (M : Structure) (ρ : Assignment M) : NT → M.N
  | .var v => ρ.n v
  | .zero => M.zero
  | .one => M.one
  | .add a b => M.add (a.eval M ρ) (b.eval M ρ)
  | .mul a b => M.mul (a.eval M ρ) (b.eval M ρ)
  | .len X => M.len (X.eval M ρ)
  | .app f as Xs => M.nfun f (as.eval M ρ) (Xs.eval M ρ)
def ST.eval (M : Structure) (ρ : Assignment M) : ST → M.S
  | .var v => ρ.s v
  | .app f as Xs => M.sfun f (as.eval M ρ) (Xs.eval M ρ)
def NArgs.eval (M : Structure) (ρ : Assignment M) : NArgs → List M.N
  | .nil => []
  | .cons a as => a.eval M ρ :: as.eval M ρ
def SArgs.eval (M : Structure) (ρ : Assignment M) : SArgs → List M.S
  | .nil => []
  | .cons a as => a.eval M ρ :: as.eval M ρ
end

/-- Satisfaction of a formula in a structure under an assignment (Tarski semantics). -/
def Fml.Sat (M : Structure) : Fml → Assignment M → Prop
  | .eqN a b, ρ => a.eval M ρ = b.eval M ρ
  | .leN a b, ρ => M.le (a.eval M ρ) (b.eval M ρ)
  | .mem a X, ρ => M.mem (a.eval M ρ) (X.eval M ρ)
  | .eqS X Y, ρ => X.eval M ρ = Y.eval M ρ
  | .neg φ, ρ => ¬ φ.Sat M ρ
  | .and φ ψ, ρ => φ.Sat M ρ ∧ ψ.Sat M ρ
  | .or φ ψ, ρ => φ.Sat M ρ ∨ ψ.Sat M ρ
  | .ballN v t φ, ρ => ∀ a, M.le a (t.eval M ρ) → φ.Sat M (ρ.setN v a)
  | .bexN v t φ, ρ => ∃ a, M.le a (t.eval M ρ) ∧ φ.Sat M (ρ.setN v a)
  | .allN v φ, ρ => ∀ a, φ.Sat M (ρ.setN v a)
  | .exN v φ, ρ => ∃ a, φ.Sat M (ρ.setN v a)
  | .allS v φ, ρ => ∀ X, φ.Sat M (ρ.setS v X)
  | .exS v φ, ρ => ∃ X, φ.Sat M (ρ.setS v X)

/-- A chosen definition of a new function symbol with `nn` number and `ns` string arguments.
In both forms the arguments are number variables `1, …, nn` and string variables
`0, …, ns-1`, and number variable `0` is the bound variable.
* `bit nn ns t φ`: a string function `F` with `F(x⃗, X⃗)(i) ↔ i < t ∧ φ(i, x⃗, X⃗)`
  (Σ^B_0 bit-definition, CN10 AC⁰ reductions);
* `min nn ns t φ`: a number function, the least `y < t` with `φ(y, x⃗, X⃗)`, and `t` if there
  is none (Σ^B_0 bounded minimization). -/
inductive FDef where
  | bit (nn ns : ℕ) (bound : NT) (φ : Fml)
  | min (nn ns : ℕ) (bound : NT) (φ : Fml)

def FDef.sig : FDef → ℕ × ℕ × Srt
  | .bit nn ns _ _ => (nn, ns, .str)
  | .min nn ns _ _ => (nn, ns, .num)

/-- A finite list of chosen definitions; definition `k` may use the primitives and the
definitions `j < k`. -/
abbrev Program := List FDef

/-- Symbols available to definition `k` of `P` (to all of `P` when `k = P.length`). -/
def Program.symSig (P : Program) (k : ℕ) : Sym → Option (ℕ × ℕ × Srt)
  | .prim p => some p.sig
  | .defd j => if j < k then (P[j]?).map FDef.sig else none

/-- Well-formedness of one definition at position `k`: a Σ^B_0 defining formula whose
free variables are among the arguments and the bound variable, a bound term in the
arguments only, and only earlier symbols, each applied with its signature. -/
def FDef.WF (P : Program) (k : ℕ) : FDef → Prop
  | .bit nn ns t φ =>
      φ.isSigmaB0 = true ∧
      t.ok (P.symSig k) (fun v => 1 ≤ v && v ≤ nn) (fun v => v < ns) = true ∧
      φ.ok (P.symSig k) (fun v => v ≤ nn) (fun v => v < ns) = true
  | .min nn ns t φ =>
      φ.isSigmaB0 = true ∧
      t.ok (P.symSig k) (fun v => 1 ≤ v && v ≤ nn) (fun v => v < ns) = true ∧
      φ.ok (P.symSig k) (fun v => v ≤ nn) (fun v => v < ns) = true

def Program.WF (P : Program) : Prop :=
  ∀ k (h : k < P.length), (P[k]'h).WF P k

namespace Structure

variable (M : Structure)

/-- Strict order `a < b`, i.e. `a ≤ b ∧ a ≠ b`. -/
def lt (a b : M.N) : Prop := M.le a b ∧ a ≠ b

/-- The numeral with value `c`: `0, 1, 1+1, (1+1)+1, …`. -/
def numeral : ℕ → M.N
  | 0 => M.zero
  | c + 1 => M.add (numeral c) M.one

/-- Fixed powers `a^e`, `e` an external exponent. -/
def npow (a : M.N) : ℕ → M.N
  | 0 => M.one
  | e + 1 => M.mul (npow a e) a

/-- The pairing function `⟨u,v⟩ = (u+v)(u+v+1)+2v` of §2.1. -/
def pair (u v : M.N) : M.N :=
  M.add (M.mul (M.add u v) (M.add (M.add u v) M.one)) (M.add v v)

/-- `X` is the string whose bits are exactly the numbers satisfying `P`. -/
def IsSet (X : M.S) (P : M.N → Prop) : Prop := ∀ z, M.mem z X ↔ P z

/-! Interpretations of the primitives, named. -/
def numones (y : M.N) (X : M.S) : M.N := M.nfun (.prim .numones) [y] [X]
def row (a : M.N) (X : M.S) : M.S := M.sfun (.prim .row) [a] [X]
def empt : M.S := M.sfun (.prim .empt) [] []
def badd (X Y : M.S) : M.S := M.sfun (.prim .add) [] [X, Y]
def bsub (X Y : M.S) : M.S := M.sfun (.prim .sub) [] [X, Y]
def cut (b : M.N) (X : M.S) : M.S := M.sfun (.prim .cut) [b] [X]
def shl (k : M.N) (X : M.S) : M.S := M.sfun (.prim .shl) [k] [X]
def isum (b : M.N) (X : M.S) : M.S := M.sfun (.prim .isum) [b] [X]
def bmul (X Y : M.S) : M.S := M.sfun (.prim .mul) [] [X, Y]
def imul (i j : M.N) (X : M.S) : M.S := M.sfun (.prim .imul) [i, j] [X]
def bdiv (A B : M.S) : M.S := M.sfun (.prim .div) [] [A, B]
def bmod (A B : M.S) : M.S := M.sfun (.prim .md) [] [A, B]
def mag (u : M.S) : M.S := M.sfun (.prim .mag) [] [u]
def sgnd (s : M.N) (X : M.S) : M.S := M.sfun (.prim .sgnd) [s] [X]

/-- Binary order of nonnegative binary integers (bit `i` = coefficient of `2^i`):
`X <₂ Y` iff at the highest bit where they differ, `Y` has the bit. -/
def BLt (X Y : M.S) : Prop :=
  ∃ i, M.mem i Y ∧ ¬ M.mem i X ∧ ∀ j, M.lt i j → (M.mem j X ↔ M.mem j Y)

def BLe (X Y : M.S) : Prop := M.BLt X Y ∨ X = Y

end Structure

end ReLUWitness.Refuter


