-- Prove2me | Definitions.Def_CookPvsNP_defs
-- name    : CookPvsNP_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T13:37:22.89316+00:00
-- url     : https://prove2.me/theorems/7c6b3da6-5145-4b2d-9550-f07c61d2c766
-- title:
--   Cook's Turing machines; the classes P, NP, coNP; reductions; NP-completeness; CNF-SAT
-- statement:
--   This file sets up the objects of the P versus NP problem exactly as in Cook's official Clay description.
--
--   1. **Turing machines** (Appendix). A machine $M$ with non-blank tape symbols $\Gamma$ (a type) has tape alphabet $\Gamma\cup\{b\}$, a finite state set $Q$ with decidable equality, an initial state $q_0$, halting states $q_{\mathrm{accept}}\neq q_{\mathrm{reject}}$, and a transition function $\delta : Q\times(\Gamma\cup\{b\})\to Q\times(\Gamma\cup\{b\})\times\{-1,+1\}$. A configuration $x\,q\,y$ is stored as the state, the left part $x$ (reversed), the scanned symbol and the rest of $y$. One step follows Cook's four cases (moving right off the end of $y$ scans a fresh blank; moving left off the start of $x$ creates a fresh blank). Halting configurations do not change. The computation on $w$ starts from $q_0 w$ (or $q_0 b$ if $w$ is empty). $M$ **halts within $n$ steps** if the configuration after $n$ steps is halting, and **accepts** $w$ if some iterate is in state $q_{\mathrm{accept}}$.
--
--   2. **The class P** (§1). For an alphabet $\Sigma$ (a finite type), $L\in\mathrm P_\Sigma$ iff there are a finite $\Gamma$, an injection $\iota:\Sigma\hookrightarrow\Gamma$, a machine $M$ and $k\in\mathbb N$ such that $M$ halts within $|w|^k+k$ steps on every $w\in\Sigma^*$, and $L=\{w : M\text{ accepts }\iota(w)\}$.
--
--   3. **Checking relations and NP** (§1). For $R\subseteq\Sigma^*\times\Sigma_1^*$,
--   $$L_R=\{\,w\#y : R(w,y)\,\}$$
--   over the alphabet $\{\#\}\cup\Sigma\cup\Sigma_1$ (disjointly tagged). $L\in\mathrm{NP}_\Sigma$ iff there are a finite nonempty $\Sigma_1$, a relation $R$ with $L_R\in\mathrm P$, and $k$ such that for all $w$,
--   $$w\in L\iff\exists y\in\Sigma_1^*,\ |y|\le|w|^k\ \wedge\ R(w,y).$$
--
--   4. **coNP** (§2): $L\in\mathrm{coNP}_\Sigma$ iff $\Sigma^*\setminus L\in\mathrm{NP}_\Sigma$.
--
--   5. **Polynomial-time computable functions and reductions** (Definition 3). $f:\Sigma_1^*\to\Sigma_2^*$ is polynomial-time computable if some machine whose finite tape alphabet contains copies of $\Sigma_1$ and $\Sigma_2$ halts within $|x|^k+k$ steps on every input $x$, leaving $f(x)$ as the tape content from the head rightwards (trailing blanks removed). $L_1\le_p L_2$ iff there is such an $f$ with $x\in L_1\iff f(x)\in L_2$.
--
--   6. **NP-completeness** (Definition 4). $L$ is NP-complete iff $L\in\mathrm{NP}$ and $L'\le_p L$ for every language $L'\in\mathrm{NP}_{\Sigma'}$ over every finite nonempty alphabet $\Sigma'$.
--
--   7. **CNF-Satisfiability** (§2). A CNF formula is a list of clauses, each a list of literals $x_i$ or $\neg x_i$ ($i\in\mathbb N$). It is satisfiable if some assignment $\tau:\mathbb N\to\{0,1\}$ makes some literal in every clause true. Formulas are written over the four-letter alphabet $\{+,-,1,;\}$: a literal is its sign followed by $i$ copies of $1$, and every clause is followed by $;$. $\mathrm{SAT}$ is the set of codes of satisfiable formulas.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Strings are `List`s and languages are `Set (List Sym)`. The blank is `none : Option Γ`. Cook's $\Sigma\cup\Sigma_1\cup\{\#\}$ is modelled as `Option (Sym ⊕ Sym₁)`, and Satisfiability is restricted to CNF formulas.
-- source:
--   S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §1 (pp. 1–2: P, checking relations, NP), §2 (p. 4: Definitions 3 and 4; p. 5: Satisfiability, coNP), Appendix (pp. 9–10: Turing machines)

import Mathlib

/-!
# The P versus NP problem, following S. Cook's Clay Mathematics Institute statement

Definitions for the mission draft. Everything follows S. Cook, *The P versus NP problem*
(official Clay problem description): the one-tape Turing machine of the Appendix, the class `P`
(§1), checking relations and the class `NP` (§1), `coNP` (§2), polynomial-time many-one
reducibility (Definition 3), NP-completeness (Definition 4), and the language Satisfiability (§2),
here in its conjunctive-normal-form version.

Conventions:
* A string over an alphabet `Sym` is a `List Sym`; a language is a `Set (List Sym)`.
* The blank symbol is represented by `none : Option Γ`; the full tape alphabet of a machine whose
  non-blank symbols are `Γ` is `Option Γ`, so the blank is automatically distinct from every input
  symbol.
-/

namespace CookPvsNP

/-- A language over the alphabet `Sym`: a set of finite strings over `Sym`. -/
abbrev Lang (Sym : Type) : Type := Set (List Sym)

/-- Head movements of a Turing machine: one square to the left (`-1`) or right (`+1`). -/
inductive Move where
  | left
  | right
  deriving DecidableEq

/-- A (deterministic, one-tape) Turing machine in the sense of Cook's Appendix, with non-blank tape
symbols `Γ` (the full tape alphabet is `Option Γ`, where `none` is the blank symbol `b`).
It has a finite state set `Q` with three special states `q₀`, `qaccept`, `qreject`
(the latter two distinct) and a transition function `δ`. The value of `δ` on the two halting
states is never used. -/
structure TM (Γ : Type) where
  /-- The finite set of states. -/
  Q : Type
  [finQ : Fintype Q]
  [decQ : DecidableEq Q]
  /-- The initial state. -/
  q₀ : Q
  /-- The accepting state. -/
  qaccept : Q
  /-- The rejecting state. -/
  qreject : Q
  accept_ne_reject : qaccept ≠ qreject
  /-- The transition function: `δ q s = (q', s', h)` means: in state `q` scanning `s`, print `s'`,
  move the head in direction `h`, and enter state `q'`. -/
  δ : Q → Option Γ → Q × Option Γ × Move

attribute [instance] TM.finQ TM.decQ

/-- A configuration `x q y` of a machine (Cook's Appendix): the state `q`, the tape contents `x`
to the left of the head (stored in reverse order, nearest square first), the scanned symbol
(the first symbol of `y`), and the rest of `y` to the right of the head. -/
structure Cfg (Γ Q : Type) where
  state : Q
  left : List (Option Γ)
  head : Option Γ
  right : List (Option Γ)

namespace TM

variable {Γ : Type} (M : TM Γ)

/-- A configuration is halting if its state is `qaccept` or `qreject`. -/
def IsHalting (c : Cfg Γ M.Q) : Prop := c.state = M.qaccept ∨ c.state = M.qreject

instance (c : Cfg Γ M.Q) : Decidable (M.IsHalting c) := by
  unfold IsHalting; infer_instance

/-- One computation step `C → C'` (the four cases of Cook's Appendix); halting configurations are
left unchanged. -/
def step (c : Cfg Γ M.Q) : Cfg Γ M.Q :=
  if M.IsHalting c then c else
    match M.δ c.state c.head with
    | (q', s', Move.right) =>
        { state := q', left := s' :: c.left, head := c.right.headD none, right := c.right.tail }
    | (q', s', Move.left) =>
        match c.left with
        | [] => { state := q', left := [], head := none, right := s' :: c.right }
        | a :: x' => { state := q', left := x', head := a, right := s' :: c.right }

/-- The configuration reached after `n` steps (halting configurations are fixed points). -/
def run (n : ℕ) (c : Cfg Γ M.Q) : Cfg Γ M.Q := (M.step)^[n] c

/-- The initial configuration `q₀ w` on input `w` (or `q₀ b` if `w` is empty). -/
def init (w : List Γ) : Cfg Γ M.Q :=
  { state := M.q₀, left := [], head := (w.map some).headD none, right := (w.map some).tail }

/-- `M` halts on input `w` within `n` steps, i.e. `t_M(w) ≤ n`. -/
def HaltsWithin (n : ℕ) (w : List Γ) : Prop := M.IsHalting (M.run n (M.init w))

/-- `M` accepts `w`: the computation on `w` is finite and ends in the state `qaccept`. -/
def Accepts (w : List Γ) : Prop := ∃ n, (M.run n (M.init w)).state = M.qaccept

/-- The output of a configuration: the tape contents from the scanned square rightwards, with the
trailing blanks removed. -/
def output (c : Cfg Γ M.Q) : List (Option Γ) :=
  ((c.head :: c.right).reverse.dropWhile Option.isNone).reverse

end TM

/-- The class `P` of languages over `Sym` (Cook, §1): `L ∈ P Sym` iff `L = L(M)` for a Turing
machine `M` with input alphabet `Sym` (embedded into the machine's finite tape alphabet by `ι`)
that runs in polynomial time, i.e. there is `k` with `t_M(w) ≤ |w|^k + k` for every input `w`. -/
def P (Sym : Type) [Fintype Sym] : Set (Lang Sym) :=
  { L | ∃ (Γ : Type) (_ : Fintype Γ) (ι : Sym ↪ Γ) (M : TM Γ) (k : ℕ),
      (∀ w : List Sym, M.HaltsWithin (w.length ^ k + k) (w.map ι)) ∧
      ∀ w : List Sym, w ∈ L ↔ M.Accepts (w.map ι) }

/-- The language `L_R = {w#y | R(w, y)}` of a checking relation `R ⊆ Sym* × Sym₁*` (Cook, §1).
It is a language over the alphabet `Option (Sym ⊕ Sym₁)`, where `none` plays the role of the
separator `#` and `inl`/`inr` tag the symbols of `Sym` and `Sym₁`. -/
def checkLang {Sym Sym₁ : Type} (R : List Sym → List Sym₁ → Prop) :
    Lang (Option (Sym ⊕ Sym₁)) :=
  { s | ∃ w y, R w y ∧ s = w.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr) }

/-- The class `NP` of languages over `Sym` (Cook, §1): `L ∈ NP Sym` iff there are a finite
nonempty alphabet `Sym₁`, a checking relation `R ⊆ Sym* × Sym₁*` which is polynomial-time
(`L_R ∈ P`), and `k ∈ ℕ` such that for all `w`, `w ∈ L ↔ ∃ y, |y| ≤ |w|^k ∧ R(w, y)`. -/
def NP (Sym : Type) [Fintype Sym] : Set (Lang Sym) :=
  { L | ∃ (Sym₁ : Type) (_ : Fintype Sym₁) (_ : Nonempty Sym₁)
      (R : List Sym → List Sym₁ → Prop) (k : ℕ),
      checkLang R ∈ P (Option (Sym ⊕ Sym₁)) ∧
      ∀ w : List Sym, w ∈ L ↔ ∃ y : List Sym₁, y.length ≤ w.length ^ k ∧ R w y }

/-- The class `coNP` of complements of `NP` languages (Cook, §2). -/
def coNP (Sym : Type) [Fintype Sym] : Set (Lang Sym) :=
  { L | Lᶜ ∈ NP Sym }

/-- `f : Sym₁* → Sym₂*` is polynomial-time computable: some Turing machine whose finite tape
alphabet contains both `Sym₁` (via `ι₁`) and `Sym₂` (via `ι₂`) halts on every input `x` within
`|x|^k + k` steps, and its output (tape contents from the head rightwards, trailing blanks
removed) is `f x`. -/
def PolyTimeComputable {Sym₁ Sym₂ : Type} (f : List Sym₁ → List Sym₂) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ) (ι₁ : Sym₁ ↪ Γ) (ι₂ : Sym₂ ↪ Γ) (M : TM Γ) (k : ℕ),
    ∀ x : List Sym₁,
      M.HaltsWithin (x.length ^ k + k) (x.map ι₁) ∧
      M.output (M.run (x.length ^ k + k) (M.init (x.map ι₁))) = (f x).map (some ∘ ι₂)

/-- Polynomial-time many-one reducibility `L₁ ≤ₚ L₂` (Cook, Definition 3). -/
def PolyReducible {Sym₁ Sym₂ : Type} (L₁ : Lang Sym₁) (L₂ : Lang Sym₂) : Prop :=
  ∃ f : List Sym₁ → List Sym₂, PolyTimeComputable f ∧ ∀ x, x ∈ L₁ ↔ f x ∈ L₂

/-- NP-completeness (Cook, Definition 4): `L ∈ NP` and `L' ≤ₚ L` for every language `L'` in `NP`
over any finite nonempty alphabet. -/
def NPComplete {Sym : Type} [Fintype Sym] (L : Lang Sym) : Prop :=
  L ∈ NP Sym ∧
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : Lang Sym'),
      L' ∈ NP Sym' → PolyReducible L' L

/-! ### Satisfiability (conjunctive normal form) -/

/-- A literal: a propositional variable `x_i` (`i : ℕ`) with a polarity (`true` for `x_i`,
`false` for its negation). -/
abbrev Literal : Type := Bool × ℕ

/-- A propositional formula in conjunctive normal form: a list of clauses, each a list of literals
(the disjunction of its literals); the formula is the conjunction of its clauses. -/
abbrev CNF : Type := List (List Literal)

/-- A CNF formula is satisfiable if some truth assignment makes every clause contain a true
literal. -/
def CNF.Satisfiable (F : CNF) : Prop :=
  ∃ τ : ℕ → Bool, ∀ C ∈ F, ∃ ℓ ∈ C, τ ℓ.2 = ℓ.1

/-- The four-letter alphabet used to write CNF formulas. -/
inductive SatSym where
  | pos
  | neg
  | one
  | endClause
  deriving DecidableEq

instance : Fintype SatSym where
  elems := {SatSym.pos, SatSym.neg, SatSym.one, SatSym.endClause}
  complete := by intro x; cases x <;> simp

/-- Encoding of a literal: its sign (`pos`/`neg`) followed by the variable index in unary. -/
def encodeLiteral (ℓ : Literal) : List SatSym :=
  (if ℓ.1 then SatSym.pos else SatSym.neg) :: List.replicate ℓ.2 SatSym.one

/-- Encoding of a CNF formula: each clause is the concatenation of its literals' codes followed by
`endClause`. -/
def encodeCNF (F : CNF) : List SatSym :=
  F.flatMap fun C => C.flatMap encodeLiteral ++ [SatSym.endClause]

/-- The language CNF-Satisfiability: codes of satisfiable CNF formulas. -/
def SAT : Lang SatSym :=
  { s | ∃ F : CNF, F.Satisfiable ∧ s = encodeCNF F }

end CookPvsNP


