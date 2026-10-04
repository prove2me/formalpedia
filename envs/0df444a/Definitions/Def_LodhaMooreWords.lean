-- Prove2me | Definitions.Def_LodhaMooreWords
-- name    : LodhaMooreWords
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-02T17:57:21.196981+00:00
-- url     : https://prove2.me/theorems/d9f22761-b512-437c-a9e6-50edb3ca61bc
-- title:
--   Lodha–Moore §5: words, derivations, standard forms, B-words and advancing
-- statement:
--   Notions of Lodha and Moore's §2 (p. 4) and §5 (pp. 9–12).
--
--   **Words (p. 4).** p. 4: “If $G$ is a group and $A$ is a subset of $G$, an $A$-word is a finite sequence of elements of the set $A \times (\mathbb{Z} \setminus \{0\})$. We typically denote a pair $(a, n)$ as $a^n$, but we emphasize here that it is formally distinct from the group element $a^n$. The *word length* of an $A$-word is the sum of the absolute values of the exponents which occur in it.” A `Word` is a finite sequence of pairs $(g, n)$ of a generator and an integer, written $g^n$, with every exponent nonzero (`IsWord`); `wordLength` is that sum and `eval` the product in `SeqGroup`, left to right. `IsXWord`, `IsYWord`, `IsS0Word`: every letter is some $x_s$, some $y_s$, or in $S_0$. `xFinInv s t` is $t.x_s^{-1}$ on finite sequences. The paper has no separate defining sentence for $X$-, $Y$- and $S_0$-words (its $A$-words for those alphabets), for the value of a word, or for $t.x_s^{-1}$ on finite sequences.
--
--   **Derivations (p. 9).** p. 9: “In what follows, we will say that an $S$-word $\Omega_1$ is *derived from* an $S$-word $\Omega_0$ if it is the result of applying substitutions of the following forms: $y_t^ix_s^{\pm1} \Rightarrow x_s^{\pm1}y^i_{t.x_s^{\pm1}} \qquad y_s \Rightarrow x_sy_{s0}y_{s10}^{-1}y_{s11} \qquad y_uy_v \Leftrightarrow y_vy_u \qquad x^{i+j} \Leftrightarrow x^ix^j \qquad y^{i+j} \Leftrightarrow y^iy^j$ delete an occurrence of $y^iy^{-i}$ where $s, t, u, v \in 2^{<\mathbb{N}}$ are such that $t.x_s$ is defined and $u$ and $v$ are incompatible, and $i, j$ are nonzero integers of the same sign. We will write this symbolically as $\Omega_0 \Rightarrow \Omega_1$.” `Step` is one substitution inside a word: $y_t^ix_s^{\pm1} \Rightarrow x_s^{\pm1}y^i_{t.x_s^{\pm1}}$ when $t.x_s^{\pm1}$ is defined; $y_s \Rightarrow x_sy_{s0}y_{s10}^{-1}y_{s11}$; $y_s^{-1} \Rightarrow x_s^{-1}y_{s00}^{-1}y_{s01}y_{s1}^{-1}$; $y_u^iy_v^j \Leftrightarrow y_v^jy_u^i$ for incompatible $u$, $v$; $g^{i+j} \Leftrightarrow g^ig^j$ for nonzero $i$, $j$ of the same sign; and deleting $y_s^iy_s^{-i}$. `Derives Ω Ω'` ($\Omega \Rightarrow \Omega'$) means finitely many substitutions lead from $\Omega$ to $\Omega'$.
--
--   **Standard forms (Definitions 5.1, 5.5).** p. 9 (Definition 5.1): “An $S$-word $\Omega$ is in *standard form* if it is the concatenation of a $X$-word followed by a $Y$-word and whenever $\Omega(i) = y_s^m$, $\Omega(j) = y_t^n$, and $s \subseteq t$, then $j \le i$. We will write *standard form* to mean an $S$-word in standard form. The *depth* of a standard form $\Omega$ is the least $l$ such that there is binary sequence $s$ of length $l$ such that $y_s$ occurs in $\Omega$ (if $\Omega$ is an $X$-word, then we say that $\Omega$ has infinite depth).” `IsStandardForm Ω` says that $\Omega$ is in standard form in this sense. `depth Ω` is the least length of an $s$ with $y_s$ occurring in $\Omega$, and $\infty$ for an $X$-word.
--
--   p. 10: “If $\Omega$ is standard form and $y_s$ occurs in $\Omega$, we say that $s$ is *exposed in* $\Omega$ if there is a finite binary sequence $u$ extending $s$ such that if $t$ is a binary sequence compatible with $u$ and $y_t$ occurs in $\Omega$, then $t$ is an initial part of $s$.” `Exposed Ω s` is the existence of such a $u$.
--
--   p. 11 (Definition 5.5): “A standard form $\Omega$ is *sufficiently expanded* if whenever $y_s$ occurs in $\Omega$ and $s$ is not exposed in $\Omega$, then: • $y_{s0}$ occurs in $\Omega$ if $y_s$ occurs positively in $\Omega$; • $y_{s1}$ occurs in $\Omega$ if $y_s$ occurs negatively in $\Omega$.” `SufficientlyExpanded Ω` is the condition from “whenever” on.
--
--   **$B$-words (Definitions 5.7, 5.8).** p. 12: “Let $B$ denote the set $\{0, 1, y, y^{-1}\}$ and let $B^{<\mathbb{N}}$ denote the collection of all finite strings of elements of $B$. If $\Lambda$ is in $B^{<\mathbb{N}}$ and $\Lambda(i)$ is either $y$ or $y^{-1}$, we will say that $\Lambda(i)$ is an *occurrence of $y^{\pm}$*.” `BWord` is a string over $B$.
--
--   p. 12 (Definition 5.7): “Suppose that $\Lambda$ is in $B^{<\mathbb{N}}$. An application of one of the substitutions $y00 \Rightarrow 0y \qquad y01 \Rightarrow 10y^{-1} \qquad y1 \Rightarrow 11y \qquad y^{-1}0 \Rightarrow 00y^{-1} \qquad y^{-1}10 \Rightarrow 01y \qquad y^{-1}11 \Rightarrow 1y^{-1}$ at an occurrence of $y^{\pm}$ is said to *advance* that symbol. If several advances of occurrences of $y^{\pm}$ are applied to $\Lambda$, resulting in $\Lambda'$, then we say that $\Lambda$ *can be advanced to* $\Lambda'$, denoted $\Lambda \Rightarrow \Lambda'$.” `AdvanceAt` advances one occurrence of $y^{\pm1}$ by one of these substitutions, keeping track of its position; `Advances` is any finite sequence of advances.
--
--   p. 12 (Definition 5.8): “Suppose that $\Lambda$ is in $B^{<\mathbb{N}}$. An occurrence of $y^{\pm}$ is a *potential cancellation* in $\Lambda$ if repeatedly advancing it results in an occurrence of the substring $yy^{-1}$ or $y^{-1}y$ in the modified word.” `PotentialCancellation Λ i`: repeatedly advancing the occurrence at position $i$ reaches a word in which it is immediately followed by its inverse; `NoPotentialCancellation Λ` (Lemma 5.9's “contains no potential cancellations”): no occurrence of $y^{\pm1}$ is one. Lodha and Moore count the substring anywhere in the modified word; after an advance the moved letter has a digit on its left and nothing else changes, and a pair already present is caught at its left letter, so a word has a potential cancellation in their sense exactly when it has one here.
--
--   **Formalization Note (p. 9).** The list of substitutions on p. 9 has no rule for $y_s^{-1}$, but the proof of Lemma 5.2 says “the case of $y_s^{-1}$ is handled similarly using the substitution $y_s^{-1} \Rightarrow x_s^{-1}y_{s00}^{-1}y_{s01}y_{s1}^{-1}$” (p. 10), its induction step for $y_s$ already applies the induction hypothesis to $y_{s10}^{-1}$, and the paragraph before Lemma 5.6 writes the substitution out (p. 11). Without it, nothing other than $y_s^{-1}$ itself can be derived from the word $y_s^{-1}$, and every word derived from $y_s$ other than $y_s$ keeps the letter $y_{s10}^{-1}$; so Lemmas 5.2 and 5.4 fail, for $y_s^{-1}$ and, once $l \ge |s| + 3$, for $y_s$. The rule is included, and it is then the only substitution that applies to the one-letter word $y_s^{-1}$ ([`LodhaMoorePrinted.eq_of_step_singleton_y_neg_one`](https://prove2.me/theorems/30028156-0a85-46eb-8c27-910730f17aee)). The list also writes “$y_uy_v \Leftrightarrow y_vy_u$” without exponents, while the proof of Lemma 5.6 moves $y_{s10}^{-1}$ past other letters this way; the rule here allows any exponents. Read for positive exponents only, Lemma 5.6 is false ([`LodhaMoorePosCommute.not_forall_exists_derives_sufficientlyExpanded`](https://prove2.me/theorems/b2454ba6-4adc-4e33-9abf-a48b1a234e53), with that relation in the bundle [`LodhaMoorePosCommute`](https://prove2.me/theorems/4c79d492-000b-43d7-85a2-6e38b1d570d9)). The print gives one side condition for both signs of the first substitution, “where $s, t, u, v \in 2^{<\mathbb{N}}$ are such that $t.x_s$ is defined” (p. 9), while the rule here moves $x_s^{-1}$ past $y_t^i$ when $t.x_s^{-1}$ is defined; the two give different moves only at $t = s0$, where $t.x_s^{-1} = s00$ is defined and $t.x_s$ is not. This follows the paper's own usage: the proof of Lemma 5.3 says “$t.x_s^{\pm1}$ is defined” (p. 10), and the negative case of the proof of Lemma 5.6 needs this move. The Lean writes the indexing $\Omega(i)$ as `(Ω)[i]`: Mathlib's notation `Ω[S⁄R]` (Kähler differentials) takes the token `Ω[`; the parentheses change nothing in the definition.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), pp. 4–12, §2 (words) and §5 (Definitions 5.1, 5.5, 5.7, 5.8)

import Definitions.Def_LodhaMoore

/-!
# Lodha–Moore §5: words, standard forms and advancing

Y. Lodha and J. T. Moore, arXiv:1308.4250v3, §2 p. 4 (words) and §5 pp. 9–13 (derivations,
standard forms, sufficiently expanded standard forms, `B`-words, advancing, potential
cancellations).
-/

namespace LodhaMoore

/-! ### Words (p. 4) -/

/-- A word in the generators (p. 4): a finite sequence of pairs `(g, n)`, written `gⁿ`; the
exponents of a word are nonzero (`IsWord`). -/
abbrev Word := List (Gen × ℤ)

/-- Every exponent of `w` is nonzero (p. 4: `A × (ℤ \ {0})`). -/
def IsWord (w : Word) : Prop := ∀ p ∈ w, p.2 ≠ 0

/-- The word length (p. 4): the sum of the absolute values of the exponents. -/
def Word.wordLength (w : Word) : ℕ := (w.map fun p => p.2.natAbs).sum

/-- The value of a word in `SeqGroup`, multiplied left to right. -/
noncomputable def Word.eval (w : Word) : SeqGroup := (w.map fun p => p.1.val ^ p.2).prod

/-- An `X`-word: every letter is some `x_s`. -/
def IsXWord (w : Word) : Prop := IsWord w ∧ ∀ p ∈ w, ∃ s, p.1 = .x s

/-- A `Y`-word: every letter is some `y_s`. -/
def IsYWord (w : Word) : Prop := IsWord w ∧ ∀ p ∈ w, ∃ s, p.1 = .y s

/-- An `S0`-word: every letter is in `S0`. -/
def IsS0Word (w : Word) : Prop := IsWord w ∧ ∀ p ∈ w, p.1.InS0

/-- `t.x_s⁻¹` for a finite sequence `t`: `s⌢0u ↦ s⌢00u`, `s⌢10u ↦ s⌢01u`, `s⌢11u ↦ s⌢1u`; `t`
when `t` is incompatible with `s`; undefined otherwise. -/
def xFinInv (s t : Seq) : Option Seq :=
  if s <+: t then
    match t.drop s.length with
    | false :: r => some (s ++ false :: false :: r)
    | true :: false :: r => some (s ++ false :: true :: r)
    | true :: true :: r => some (s ++ true :: r)
    | _ => none
  else if t <+: s then none else some t

/-! ### Derivations (p. 9) -/

/-- One substitution (p. 9), applied inside a word:
`y_t^i x_s^{±1} ⇒ x_s^{±1} y^i_{t.x_s^{±1}}`; `y_s ⇒ x_s y_{s0} y_{s10}⁻¹ y_{s11}`;
`y_s⁻¹ ⇒ x_s⁻¹ y_{s00}⁻¹ y_{s01} y_{s1}⁻¹` (used in the proofs of Lemmas 5.2 and 5.6);
`y_u^i y_v^j ⇔ y_v^j y_u^i` for incompatible `u`, `v`; `g^{i+j} ⇔ g^i g^j` for `i`, `j` nonzero of
the same sign; deleting `y_s^i y_s^{-i}`. -/
inductive Step : Word → Word → Prop
  | moveX (pre post : Word) (s t t' : Seq) (i : ℤ) (h : xFin s t = some t') :
      Step (pre ++ [(.y t, i), (.x s, 1)] ++ post) (pre ++ [(.x s, 1), (.y t', i)] ++ post)
  | moveXInv (pre post : Word) (s t t' : Seq) (i : ℤ) (h : xFinInv s t = some t') :
      Step (pre ++ [(.y t, i), (.x s, -1)] ++ post) (pre ++ [(.x s, -1), (.y t', i)] ++ post)
  | expand (pre post : Word) (s : Seq) :
      Step (pre ++ [(.y s, 1)] ++ post)
        (pre ++ [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
          (.y (s ++ [true, true]), 1)] ++ post)
  | expandInv (pre post : Word) (s : Seq) :
      Step (pre ++ [(.y s, -1)] ++ post)
        (pre ++ [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
          (.y (s ++ [true]), -1)] ++ post)
  | commute (pre post : Word) (u v : Seq) (i j : ℤ) (h : Incompatible u v) :
      Step (pre ++ [(.y u, i), (.y v, j)] ++ post) (pre ++ [(.y v, j), (.y u, i)] ++ post)
  | split (pre post : Word) (g : Gen) (i j : ℤ) (hi : i ≠ 0) (hj : j ≠ 0) (hij : 0 < i * j) :
      Step (pre ++ [(g, i + j)] ++ post) (pre ++ [(g, i), (g, j)] ++ post)
  | merge (pre post : Word) (g : Gen) (i j : ℤ) (hi : i ≠ 0) (hj : j ≠ 0) (hij : 0 < i * j) :
      Step (pre ++ [(g, i), (g, j)] ++ post) (pre ++ [(g, i + j)] ++ post)
  | cancel (pre post : Word) (s : Seq) (i : ℤ) (hi : i ≠ 0) :
      Step (pre ++ [(.y s, i), (.y s, -i)] ++ post) (pre ++ post)

/-- `Ω₁` is **derived** from `Ω₀` (`Ω₀ ⇒ Ω₁`, p. 9): it results from finitely many substitutions. -/
def Derives (Ω₀ Ω₁ : Word) : Prop := Relation.ReflTransGen Step Ω₀ Ω₁

/-! ### Standard forms (Definitions 5.1 and 5.5) -/

/-- `y_s` occurs in `Ω` (with some exponent). -/
def YOccurs (Ω : Word) (s : Seq) : Prop := ∃ n, (Gen.y s, n) ∈ Ω

/-- Definition 5.1: `Ω` is in **standard form**: an `X`-word followed by a `Y`-word, and whenever
`Ω(i) = y_s^m`, `Ω(j) = y_t^n` and `s ⊆ t`, then `j ≤ i`. -/
def IsStandardForm (Ω : Word) : Prop :=
  IsWord Ω ∧ (∃ Ξ Υ, Ω = Ξ ++ Υ ∧ IsXWord Ξ ∧ IsYWord Υ) ∧
    ∀ (i j : ℕ) (hi : i < Ω.length) (hj : j < Ω.length) (s t : Seq) (m n : ℤ),
      (Ω)[i] = (.y s, m) → (Ω)[j] = (.y t, n) → s <+: t → j ≤ i

/-- Definition 5.1: the **depth** of `Ω`: the least length of an `s` with `y_s` occurring in `Ω`,
and `⊤` (infinite) when `Ω` is an `X`-word. -/
noncomputable def depth (Ω : Word) : ℕ∞ := ⨅ (s : Seq) (_ : YOccurs Ω s), (s.length : ℕ∞)

/-- `s` is **exposed** in `Ω` (p. 10): some `u` extending `s` has the property that whenever `t` is
compatible with `u` and `y_t` occurs in `Ω`, `t` is an initial part of `s`. -/
def Exposed (Ω : Word) (s : Seq) : Prop :=
  ∃ u, s <+: u ∧ ∀ t, ¬ Incompatible t u → YOccurs Ω t → t <+: s

/-- `y_s` occurs positively (some exponent `> 0`) or negatively (some exponent `< 0`) in `Ω`. -/
def YOccursPos (Ω : Word) (s : Seq) : Prop := ∃ n, 0 < n ∧ (Gen.y s, n) ∈ Ω
def YOccursNeg (Ω : Word) (s : Seq) : Prop := ∃ n, n < 0 ∧ (Gen.y s, n) ∈ Ω

/-- Definition 5.5: a standard form `Ω` is **sufficiently expanded**: whenever `y_s` occurs in `Ω`
and `s` is not exposed, `y_{s0}` occurs if `y_s` occurs positively and `y_{s1}` occurs if `y_s`
occurs negatively. -/
def SufficientlyExpanded (Ω : Word) : Prop :=
  ∀ s, YOccurs Ω s → ¬ Exposed Ω s →
    (YOccursPos Ω s → YOccurs Ω (s ++ [false])) ∧ (YOccursNeg Ω s → YOccurs Ω (s ++ [true]))

/-! ### `B`-words and advancing (Definitions 5.7 and 5.8) -/

/-- The alphabet `B = {0, 1, y, y⁻¹}` (p. 12). -/
inductive BLetter
  | zero | one | y | yinv
  deriving DecidableEq

/-- A `B`-word: a finite string over `B`. -/
abbrev BWord := List BLetter

/-- Advancing the occurrence of `y^{±1}` at position `i` (Definition 5.7):
`y00 ⇒ 0y`, `y01 ⇒ 10y⁻¹`, `y1 ⇒ 11y`, `y⁻¹0 ⇒ 00y⁻¹`, `y⁻¹10 ⇒ 01y`, `y⁻¹11 ⇒ 1y⁻¹`; the second
component tracks the new position of the advanced occurrence. -/
inductive AdvanceAt : BWord × ℕ → BWord × ℕ → Prop
  | y00 (pre post : BWord) :
      AdvanceAt (pre ++ [.y, .zero, .zero] ++ post, pre.length) (pre ++ [.zero, .y] ++ post, pre.length + 1)
  | y01 (pre post : BWord) :
      AdvanceAt (pre ++ [.y, .zero, .one] ++ post, pre.length)
        (pre ++ [.one, .zero, .yinv] ++ post, pre.length + 2)
  | y1 (pre post : BWord) :
      AdvanceAt (pre ++ [.y, .one] ++ post, pre.length) (pre ++ [.one, .one, .y] ++ post, pre.length + 2)
  | yinv0 (pre post : BWord) :
      AdvanceAt (pre ++ [.yinv, .zero] ++ post, pre.length)
        (pre ++ [.zero, .zero, .yinv] ++ post, pre.length + 2)
  | yinv10 (pre post : BWord) :
      AdvanceAt (pre ++ [.yinv, .one, .zero] ++ post, pre.length)
        (pre ++ [.zero, .one, .y] ++ post, pre.length + 2)
  | yinv11 (pre post : BWord) :
      AdvanceAt (pre ++ [.yinv, .one, .one] ++ post, pre.length)
        (pre ++ [.one, .yinv] ++ post, pre.length + 1)

/-- `Λ` **can be advanced** to `Λ'` (Definition 5.7): by finitely many advances of occurrences of
`y^{±1}`. -/
def Advances (Λ Λ' : BWord) : Prop :=
  Relation.ReflTransGen (fun A B : BWord => ∃ i j, AdvanceAt (A, i) (B, j)) Λ Λ'

/-- Definition 5.8: the occurrence of `y^{±1}` at position `i` of `Λ` is a **potential
cancellation**: repeatedly advancing it reaches a word in which it is immediately followed by its
inverse (`yy⁻¹` or `y⁻¹y`). -/
def PotentialCancellation (Λ : BWord) (i : ℕ) : Prop :=
  ∃ Λ' j, Relation.ReflTransGen AdvanceAt (Λ, i) (Λ', j) ∧
    ((Λ'[j]? = some .y ∧ Λ'[j + 1]? = some .yinv) ∨ (Λ'[j]? = some .yinv ∧ Λ'[j + 1]? = some .y))

/-- `Λ` contains no potential cancellation. -/
def NoPotentialCancellation (Λ : BWord) : Prop :=
  ∀ i, (Λ[i]? = some .y ∨ Λ[i]? = some .yinv) → ¬ PotentialCancellation Λ i

end LodhaMoore


