-- Prove2me | Definitions.Def_DistLTLSynth_Char_LTL
-- name    : DistLTLSynth_Char_LTL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:15:45.016293+00:00
-- url     : https://prove2.me/theorems/0e28fe3f-d5b1-4a77-91f1-98c53e2d3da2
-- title:
--   LTL over executions (Appendix A), safety formulas, realizability, guarded formula ϕ̂, and the encoded instances of LL-Synthesis(A)
-- statement:
--   **LTL** (Appendix A): $\varphi ::= (\mathrm{in}_p = x)\mid(\mathrm{out}_p=y)\mid(\mathrm{graph}=g)\mid X\varphi\mid F\varphi\mid G\varphi\mid \varphi U\varphi\mid\varphi W\varphi\mid\neg\varphi\mid\varphi\vee\varphi\mid\varphi\wedge\varphi\mid\varphi\to\varphi\mid\varphi\leftrightarrow\varphi$. On $e\in(\Sigma\times\Omega)^\omega$ atoms read the first letter, $X\varphi$ holds iff $e[2\ldots]\models\varphi$, and with positions $r\ge1$:
--   $$e\models F\varphi \iff \exists r\ge1,\ e[r\ldots]\models\varphi,\qquad e\models \varphi U\psi\iff \exists r\ge1\,\big(e[r\ldots]\models\psi\wedge\forall\,1\le r'<r,\ e[r'\ldots]\models\varphi\big),$$
--   $G$ dually, and $\psi W\varphi := G\psi\vee\psi U\varphi$. $L(\varphi) = \{e \mid e\models\varphi\}$; $\varphi$ is **realizable under $A$** if some algorithm realizes $L(\varphi)$ under $A$.
--
--   A set $P$ of infinite words is a **safety property** if for every $t\notin P$ there is $i\ge0$ with $t[\ldots i]\cdot u\notin P$ for all $u$; $\varphi$ is a **safety formula** if $L(\varphi)$ is one. For a finite graph history $h$, $\mathrm{Prefix}_h := \bigwedge_{r=1}^{|h|}X^{r-1}(\mathrm{graph}=h[r])$ and $\widehat\varphi := \mathrm{Prefix}_h\to X^{|h|}\varphi$ (p. 11).
--
--   An **instance** of LL-Synthesis$(A)$ is $(k_1,k_2,m_1,m_2,\text{tokens})$: alphabets $X_p=\{0,\dots,k_p\}$, $Y_p=\{0,\dots,m_p\}$ and an LTL formula written in prefix notation with atoms naming letters by natural numbers. It is a yes-instance under $A$ if the token list is exactly one formula $\varphi$ and $\varphi$ is realizable under $A$ by an algorithm over these alphabets, an atom with an out-of-range index being false. A partial recursive code $c$ **computes** an algorithm $f$ if $c(\langle 0,\ulcorner v\urcorner\rangle)=\ulcorner f_1(v)\urcorner$ and $c(\langle 1,\ulcorner v\urcorner\rangle)=\ulcorner f_2(v)\urcorner$ for every view $v$.
--
--   **Formalization Note.** Round $r$ is index $r-1$. The empty conjunction is `tt` $:= (\mathrm{graph}=(1\leftrightarrow2))\vee\neg(\mathrm{graph}=(1\leftrightarrow2))$. Instances are `Primcodable` through a definitional equivalence with $\mathbb N^4\times\mathrm{List}(\mathbb N^3)$; parsing uses fuel equal to the token count, which suffices for every formula.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), pp. 38–39 (PDF 39–40), Appendix A; p. 6 (PDF 7), §2.3; p. 11 (PDF 12), safety formulas and ϕ̂; p. 39 (PDF 40), Appendix B (instances)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model

namespace DistLTLSynth.Char

/-- LTL formulas over inputs `X₁, X₂`, outputs `Y₁, Y₂` and `Γ` (Appendix A, p. 38):
`(in_p = x) | (out_p = y) | (graph = g) | X ϕ | F ϕ | G ϕ | ϕ U ϕ | ϕ W ϕ | ¬ϕ | ϕ ∨ ϕ | ϕ ∧ ϕ |
ϕ → ϕ | ϕ ↔ ϕ`. -/
inductive Formula (X1 X2 Y1 Y2 : Type) : Type where
  | inp1 (x : X1) : Formula X1 X2 Y1 Y2
  | inp2 (x : X2) : Formula X1 X2 Y1 Y2
  | out1 (y : Y1) : Formula X1 X2 Y1 Y2
  | out2 (y : Y2) : Formula X1 X2 Y1 Y2
  | graph (g : CommGraph) : Formula X1 X2 Y1 Y2
  | next (φ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | eventually (φ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | always (φ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | untl (φ ψ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | weakUntil (ψ φ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | neg (φ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | or (φ ψ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | and (φ ψ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | imp (φ ψ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2
  | iff (φ ψ : Formula X1 X2 Y1 Y2) : Formula X1 X2 Y1 Y2

/-- The suffix `e[r+1 ...]` of an infinite word (dropping the first `r` letters). -/
def shift {α : Type} (e : ℕ → α) (r : ℕ) : ℕ → α := fun n => e (n + r)

/-- Satisfaction `e ⊨ ϕ` (Appendix A, p. 39). Positions are 1-based in the paper; here the
letter of round `r` is `e (r - 1)`, so `∃ r ≥ 1, e[r...] ⊨ ϕ` is `∃ r, shift e r ⊨ ϕ`.
`F`, `G`, `U` include the current position; `ψ W ϕ :≡ G ψ ∨ ψ U ϕ`. -/
def Formula.Sat {X1 X2 Y1 Y2 : Type} :
    Formula X1 X2 Y1 Y2 → (ℕ → Signal X1 X2 × (Y1 × Y2)) → Prop
  | .inp1 x, e => (e 0).1.1 = x
  | .inp2 x, e => (e 0).1.2.1 = x
  | .out1 y, e => (e 0).2.1 = y
  | .out2 y, e => (e 0).2.2 = y
  | .graph g, e => (e 0).1.2.2 = g
  | .next φ, e => φ.Sat (shift e 1)
  | .eventually φ, e => ∃ r, φ.Sat (shift e r)
  | .always φ, e => ∀ r, φ.Sat (shift e r)
  | .untl φ ψ, e => ∃ r, ψ.Sat (shift e r) ∧ ∀ r' < r, φ.Sat (shift e r')
  | .weakUntil ψ φ, e =>
      (∀ r, ψ.Sat (shift e r)) ∨ (∃ r, φ.Sat (shift e r) ∧ ∀ r' < r, ψ.Sat (shift e r'))
  | .neg φ, e => ¬ φ.Sat e
  | .or φ ψ, e => φ.Sat e ∨ ψ.Sat e
  | .and φ ψ, e => φ.Sat e ∧ ψ.Sat e
  | .imp φ ψ, e => φ.Sat e → ψ.Sat e
  | .iff φ ψ, e => (φ.Sat e ↔ ψ.Sat e)

/-- `L(ϕ) := {e ∈ (Σ × Ω)^ω | e ⊨ ϕ}`. -/
def Formula.Lang {X1 X2 Y1 Y2 : Type} (φ : Formula X1 X2 Y1 Y2) :
    Set (ℕ → Signal X1 X2 × (Y1 × Y2)) :=
  {e | φ.Sat e}

/-- A safety property `P` (§3.2, p. 11): for every `t ∉ P` there is `i ≥ 0` such that
`t[...i] · u ∉ P` for every infinite word `u`. -/
def IsSafety {α : Type} (P : Set (ℕ → α)) : Prop :=
  ∀ t, t ∉ P → ∃ i : ℕ, ∀ u : ℕ → α, append (pre t i) u ∉ P

/-- `ϕ` is a safety formula if `L(ϕ)` is a safety property. -/
def Formula.IsSafety {X1 X2 Y1 Y2 : Type} (φ : Formula X1 X2 Y1 Y2) : Prop :=
  DistLTLSynth.Char.IsSafety φ.Lang

/-- `f` realizes `ϕ` under `A`. -/
def FRealizes {X1 X2 Y1 Y2 : Type} (f : Algorithm X1 X2 Y1 Y2) (A : Set (ℕ → CommGraph))
    (φ : Formula X1 X2 Y1 Y2) : Prop :=
  RealizesLang f A φ.Lang

/-- `ϕ` is (LL-)realizable under `A`: some distributed algorithm realizes it. -/
def Realizable {X1 X2 Y1 Y2 : Type} (A : Set (ℕ → CommGraph))
    (φ : Formula X1 X2 Y1 Y2) : Prop :=
  ∃ f : Algorithm X1 X2 Y1 Y2, FRealizes f A φ

/-- `true`, written `(graph = (1 ↔ 2)) ∨ ¬(graph = (1 ↔ 2))`. -/
def Formula.tt {X1 X2 Y1 Y2 : Type} : Formula X1 X2 Y1 Y2 :=
  .or (.graph CommGraph.both) (.neg (.graph CommGraph.both))

/-- `false`. -/
def Formula.ff {X1 X2 Y1 Y2 : Type} : Formula X1 X2 Y1 Y2 := .neg Formula.tt

/-- `Xⁿ ϕ`. -/
def Formula.nextIter {X1 X2 Y1 Y2 : Type} : ℕ → Formula X1 X2 Y1 Y2 → Formula X1 X2 Y1 Y2
  | 0, φ => φ
  | n + 1, φ => .next (Formula.nextIter n φ)

/-- Finite conjunction (the empty conjunction is `true`). -/
def Formula.bigAnd {X1 X2 Y1 Y2 : Type} : List (Formula X1 X2 Y1 Y2) → Formula X1 X2 Y1 Y2
  | [] => Formula.tt
  | φ :: l => .and φ (Formula.bigAnd l)

/-- Finite disjunction (the empty disjunction is `false`). -/
def Formula.bigOr {X1 X2 Y1 Y2 : Type} : List (Formula X1 X2 Y1 Y2) → Formula X1 X2 Y1 Y2
  | [] => Formula.ff
  | φ :: l => .or φ (Formula.bigOr l)

/-- `Prefix_h := ⋀_{r=1}^{|h|} X^{r-1} (graph = h[r])` (§3.2, p. 11). -/
def prefixFormula {X1 X2 Y1 Y2 : Type} (h : List CommGraph) : Formula X1 X2 Y1 Y2 :=
  Formula.bigAnd ((List.finRange h.length).map fun i => Formula.nextIter i.val (.graph h[i]))

/-- The guarded formula `ϕ̂ := Prefix_h → X^{|h|} ϕ` (§3.2, p. 11). -/
def hatFormula {X1 X2 Y1 Y2 : Type} (h : List CommGraph) (φ : Formula X1 X2 Y1 Y2) :
    Formula X1 X2 Y1 Y2 :=
  .imp (prefixFormula h) (Formula.nextIter h.length φ)

/-! ### Instances of `LL-Synthesis(A)` and their encoding -/

/-- A token of a formula written in prefix (Polish) notation: `(tag, a, b)` with
`tag = 0`: `(in_a = b)`; `1`: `(out_a = b)` (`a ∈ {1, 2}`); `2`: `(graph = g)` with
`a = 0, 1, 2` for `(1 → 2), (1 ↔ 2), (1 ← 2)`; `3`–`7`: `X, F, G, U, W`;
`8`–`12`: `¬, ∨, ∧, →, ↔`. -/
abbrev Token : Type := ℕ × ℕ × ℕ

/-- Parse one formula from the front of a token list (fuel-bounded; returns the rest). -/
def parseAux : ℕ → List Token → Option (Formula ℕ ℕ ℕ ℕ × List Token)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, t :: ts =>
    let un : (Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) → Option (Formula ℕ ℕ ℕ ℕ × List Token) :=
      fun c => match parseAux n ts with
        | some (φ, r) => some (c φ, r)
        | none => none
    let bin : (Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) →
        Option (Formula ℕ ℕ ℕ ℕ × List Token) :=
      fun c => match parseAux n ts with
        | some (φ, r) => match parseAux n r with
          | some (ψ, r') => some (c φ ψ, r')
          | none => none
        | none => none
    match t with
    | (0, 1, x) => some (.inp1 x, ts)
    | (0, 2, x) => some (.inp2 x, ts)
    | (1, 1, y) => some (.out1 y, ts)
    | (1, 2, y) => some (.out2 y, ts)
    | (2, 0, _) => some (.graph CommGraph.oneToTwo, ts)
    | (2, 1, _) => some (.graph CommGraph.both, ts)
    | (2, 2, _) => some (.graph CommGraph.twoToOne, ts)
    | (3, _, _) => un .next
    | (4, _, _) => un .eventually
    | (5, _, _) => un .always
    | (6, _, _) => bin .untl
    | (7, _, _) => bin .weakUntil
    | (8, _, _) => un .neg
    | (9, _, _) => bin .or
    | (10, _, _) => bin .and
    | (11, _, _) => bin .imp
    | (12, _, _) => bin .iff
    | _ => none

/-- The formula written by a token list, if the whole list is exactly one formula. -/
def parse (ts : List Token) : Option (Formula ℕ ℕ ℕ ℕ) :=
  match parseAux ts.length ts with
  | some (φ, []) => some φ
  | _ => none

/-- An instance of `LL-Synthesis(A)`: the finite nonempty alphabets
`X₁ = Fin (k1 + 1)`, `X₂ = Fin (k2 + 1)`, `Y₁ = Fin (m1 + 1)`, `Y₂ = Fin (m2 + 1)` and an LTL
formula (as a token list) whose atoms name letters by their index in `ℕ`. -/
structure Instance : Type where
  k1 : ℕ
  k2 : ℕ
  m1 : ℕ
  m2 : ℕ
  tokens : List Token

/-- The (computable, primitive recursive) identification of instances with tuples. -/
def Instance.equiv : Instance ≃ ℕ × ℕ × ℕ × ℕ × List Token where
  toFun I := (I.k1, I.k2, I.m1, I.m2, I.tokens)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Instance := Primcodable.ofEquiv _ Instance.equiv

/-- Input/output alphabets of an instance. -/
abbrev Instance.X1 (I : Instance) : Type := Fin (I.k1 + 1)
abbrev Instance.X2 (I : Instance) : Type := Fin (I.k2 + 1)
abbrev Instance.Y1 (I : Instance) : Type := Fin (I.m1 + 1)
abbrev Instance.Y2 (I : Instance) : Type := Fin (I.m2 + 1)

/-- Read the letters of an execution over `Fin` alphabets as natural numbers, so that an
atom `(in_p = x)`/`(out_p = y)` whose index is out of range is false at every position. -/
def valExec {a b c d : ℕ} (e : ℕ → Signal (Fin a) (Fin b) × (Fin c × Fin d)) :
    ℕ → Signal ℕ ℕ × (ℕ × ℕ) :=
  fun n => (((e n).1.1.val, (e n).1.2.1.val, (e n).1.2.2), ((e n).2.1.val, (e n).2.2.val))

/-- The language of the instance's formula over its own alphabets. -/
def Instance.Lang (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ) :
    Set (ℕ → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :=
  {e | φ.Sat (valExec e)}

/-- `I` is a yes-instance of `LL-Synthesis(A)`: its token list is a formula `ϕ`, and some
distributed algorithm over `I`'s alphabets realizes `ϕ` under `A`. -/
def Instance.Realizable (A : Set (ℕ → CommGraph)) (I : Instance) : Prop :=
  ∃ φ, parse I.tokens = some φ ∧
    ∃ f : Algorithm I.X1 I.X2 I.Y1 I.Y2, RealizesLang f A (I.Lang φ)

/-- The instance's formula is a safety formula over its alphabets. -/
def Instance.IsSafety (I : Instance) : Prop :=
  ∃ φ, parse I.tokens = some φ ∧ DistLTLSynth.Char.IsSafety (I.Lang φ)

/-- A partial recursive code `c` computes the local output functions of `f`:
`c` on `⟨0, ⌜v⌝⟩` returns `⌜f₁(v)⌝` and on `⟨1, ⌜v⌝⟩` returns `⌜f₂(v)⌝`, for every view `v`. -/
def CodeComputes {X1 X2 Y1 Y2 : Type} [Encodable X1] [Encodable X2] [Encodable Y1]
    [Encodable Y2] (c : Nat.Partrec.Code) (f : Algorithm X1 X2 Y1 Y2) : Prop :=
  ∀ v : View X1 X2,
    c.eval (Nat.pair 0 (Encodable.encode v)) = Part.some (Encodable.encode (f.f1 v)) ∧
    c.eval (Nat.pair 1 (Encodable.encode v)) = Part.some (Encodable.encode (f.f2 v))

/-- The code `c` computes a distributed algorithm realizing `I`'s formula under `A`. -/
def Instance.RealizedByCode (A : Set (ℕ → CommGraph)) (I : Instance)
    (c : Nat.Partrec.Code) : Prop :=
  ∃ φ, parse I.tokens = some φ ∧
    ∃ f : Algorithm I.X1 I.X2 I.Y1 I.Y2, CodeComputes c f ∧ RealizesLang f A (I.Lang φ)

end DistLTLSynth.Char


