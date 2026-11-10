-- Prove2me | Definitions.Def_ObfEF_Incremental_Formula
-- name    : ObfEF_Incremental_Formula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:55:24.87721+00:00
-- url     : https://prove2.me/theorems/f2f908ec-e909-468b-8368-bec07e537e15
-- title:
--   Propositional formulas over {→, ⊥}: abbreviations, symbol count, semantics (pp. 26-27)
-- statement:
--   Formulas are built from propositional variables $x_v$ ($v\in\mathbb N$), the constant $\bot$ and the connective $\to$. The other connectives are the abbreviations fixed on p. 27:
--   $$\neg\varphi:=\varphi\to\bot,\quad \varphi\wedge\varphi':=\neg(\varphi\to\neg\varphi'),\quad \varphi\vee\varphi':=\neg\varphi\to\varphi',\quad \varphi\leftrightarrow\varphi':=(\varphi\to\varphi')\wedge(\varphi'\to\varphi),$$
--   with $0:=\bot$ and $1:=\bot\to\bot$. Definition 2.7 adds $\mathrm{eq}(P,Q):=(\neg P\vee Q)\wedge(\neg Q\vee P)$. The **size** $|\varphi|$ is the number of symbols of $\varphi$. An assignment $\alpha$ maps variables to bits, $\alpha(\varphi)\in\{0,1\}$ is the value of $\varphi$, and $\varphi$ is a **tautology** if $\alpha(\varphi)=1$ for every $\alpha$.
--
--   These are the lines of Extended Frege proofs, of equivalence formulas and of derivations of width three.
--
--   **Formalization Note.** `Fml` has constructors `var`, `bot`, `imp`; `size` counts every occurrence of a variable, of `⊥` and of `→` once (parentheses are not counted; counting them changes sizes by at most a factor 3). A finite conjunction $\varphi_1\wedge\dots\wedge\varphi_m$ is right-nested (`bigConj`), and the empty conjunction is $1$. `vars` is the set of variables, `eval` the value under an assignment.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 26, 'Boolean Formulas'; p. 27 (connectives of the fixed system); p. 28 (eq)

import Mathlib

/-!
# Propositional formulas over {→, ⊥}, their abbreviations, size and semantics

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), p. 26 ("Boolean
Formulas") and p. 27 (the connectives of the fixed Extended Frege system of [Li25]).

Formulas are built from variables `var v` (`v : ℕ`), `⊥` and `→`. The other connectives are the
abbreviations printed on p. 27: `¬φ := φ → ⊥`, `φ ∧ φ' := ¬(φ → ¬φ')`, `φ ∨ φ' := ¬φ → φ'`,
`φ ↔ φ' := (φ → φ') ∧ (φ' → φ)`, `0 := ⊥`, `1 := ⊥ → ⊥`. The size `|φ|` is the number of symbols:
each occurrence of a variable, of `⊥` and of `→` counts one (no parentheses are counted).
-/

namespace ObfEF.Incremental

/-- Formulas over the connectives `{→, ⊥}` with propositional variables indexed by `ℕ`. -/
inductive Fml where
  | var (v : ℕ)
  | bot
  | imp (φ ψ : Fml)
  deriving DecidableEq

namespace Fml

/-- `¬φ := φ → ⊥`. -/
def neg (φ : Fml) : Fml := imp φ bot

/-- `φ ∧ ψ := ¬(φ → ¬ψ)`. -/
def conj (φ ψ : Fml) : Fml := neg (imp φ (neg ψ))

/-- `φ ∨ ψ := ¬φ → ψ`. -/
def disj (φ ψ : Fml) : Fml := imp (neg φ) ψ

/-- `φ ↔ ψ := (φ → ψ) ∧ (ψ → φ)`. -/
def iff (φ ψ : Fml) : Fml := conj (imp φ ψ) (imp ψ φ)

/-- The constant `1 := ⊥ → ⊥` (the constant `0` is `⊥`). -/
def top : Fml := imp bot bot

/-- The formula of a bit: `0 = ⊥`, `1 = ⊥ → ⊥`. -/
def ofBool (b : Bool) : Fml := if b then top else bot

/-- `eq(P, Q) := (¬P ∨ Q) ∧ (¬Q ∨ P)` (Definition 2.7). -/
def eqF (P Q : Fml) : Fml := conj (disj (neg P) Q) (disj (neg Q) P)

/-- The conjunction `φ₁ ∧ (φ₂ ∧ (⋯ ∧ φ_m))` of a nonempty list, right-nested; the empty
conjunction is `1`. -/
def bigConj : List Fml → Fml
  | [] => top
  | [φ] => φ
  | φ :: ψ :: l => conj φ (bigConj (ψ :: l))

/-- `|φ|`: the number of symbols (variables, `⊥`, `→`). -/
def size : Fml → ℕ
  | var _ => 1
  | bot => 1
  | imp φ ψ => φ.size + ψ.size + 1

/-- The set of variables occurring in `φ`. -/
def vars : Fml → Finset ℕ
  | var v => {v}
  | bot => ∅
  | imp φ ψ => φ.vars ∪ ψ.vars

/-- `α(φ)`: the value of `φ` under the assignment `α`. -/
def eval (α : ℕ → Bool) : Fml → Bool
  | var v => α v
  | bot => false
  | imp φ ψ => !(φ.eval α) || ψ.eval α

/-- `⊨ φ`: `φ` is a tautology. -/
def Taut (φ : Fml) : Prop := ∀ α : ℕ → Bool, φ.eval α = true

end Fml

end ObfEF.Incremental


