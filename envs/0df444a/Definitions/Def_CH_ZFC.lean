-- Prove2me | Definitions.Def_CH_ZFC
-- name    : CH_ZFC
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T22:23:42.198739+00:00
-- url     : https://prove2.me/theorems/4dbb2cc3-35dc-4451-a66a-21cd78b7da5c
-- title:
--   ZF, ZFC, and CH / GCH / AC as first-order sentences
-- statement:
--   First-order **Zermelo–Fraenkel set theory** $\mathrm{ZF}$ and $\mathrm{ZFC}$ in the language $\{\in\}$, together with the sentences CH, GCH and AC.
--
--   1. $\mathrm{ZF}$ (`ZF`) consists of the universal closures of: extensionality, foundation, pairing, union, power set, infinity (an inductive set exists), every instance of the **separation schema** $\forall a\,\exists b\,\forall x\,(x\in b\leftrightarrow x\in a\wedge\varphi)$ ($b$ not free in $\varphi$), and every instance of the **replacement schema** $\forall a\,\big(\forall x\in a\,\exists! y\,\varphi(x,y)\to\exists b\,\forall x\in a\,\exists y\in b\,\varphi(x,y)\big)$ ($b$ not free in $\varphi$); other free variables of $\varphi$ act as parameters.
--   2. $\mathrm{AC}$ (`acSentence`): every set of nonempty, pairwise disjoint sets has a choice set meeting each member in exactly one element. $\mathrm{ZFC}=\mathrm{ZF}\cup\{\mathrm{AC}\}$ (`ZFC`).
--   3. $\mathrm{CH}$ (`chSentence`): with $\omega$ the least inductive set, every $S\subseteq\mathcal P(\omega)$ satisfies $|S|\le|\omega|$ or $|\mathcal P(\omega)|\le|S|$.
--   4. $\mathrm{GCH}$ (`gchSentence`): for every infinite set $S$ and every set $T$ with $|S|\le|T|\le|\mathcal P(S)|$, $|T|=|S|$ or $|T|=|\mathcal P(S)|$.
--
--   Here $|x|\le|y|$ means there is an injection $x\to y$ and $|x|=|y|$ a bijection, coded by sets of Kuratowski pairs. These are the objects of the independence results of Gödel and Cohen.
--
--   **Formalization Note** Semantic consequence $T\models\sigma$ (`T ⊨ᵇ σ`, truth in every model of $T$) and satisfiability (`T.IsSatisfiable`) are Mathlib's; by Gödel's completeness theorem they coincide with provability and consistency.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; intro ('In ZFC, CH is equivalent to …'), 'Cardinality of infinite sets' (CH restated as: every infinite S ⊆ ℝ injects into ℤ or ℝ injects into S, with |ℝ| = 2^ℵ₀), 'Generalized continuum hypothesis' (first paragraph).

import Definitions.Def_CH_SetTheoryLanguage

/-!
# ZF, ZFC and the continuum hypothesis as first-order sentences

`ZF` is the first-order theory with the axioms of extensionality, foundation, pairing,
union, power set, infinity, and the separation and replacement schemas (with parameters);
`ZFC` adds the axiom of choice.  `chSentence`, `gchSentence` and `acSentence` are the
continuum hypothesis, the generalized continuum hypothesis and the axiom of choice,
written as sentences in the language of set theory.
-/

namespace ContinuumHypothesis

open FirstOrder FirstOrder.Language

noncomputable section

namespace SFormula

/-- Extensionality: `∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
def extensionality : SFormula :=
  all 0 (all 1 (all 2 (mem 2 0 ⇔ mem 2 1) ⟹ eq 0 1))

/-- Foundation: every nonempty set `x` has an element `y` with `y ∩ x = ∅`. -/
def foundation : SFormula :=
  all 0 (ex 1 (mem 1 0) ⟹ ex 1 (mem 1 0 ⊓ ∼(ex 2 (mem 2 1 ⊓ mem 2 0))))

/-- Pairing: for all `x, y` the set `{x, y}` exists. -/
def pairing : SFormula := all 0 (all 1 (ex 2 (isDoubleton 2 0 1)))

/-- Union: for every `x` the set `⋃ x` exists. -/
def union : SFormula :=
  all 0 (ex 1 (all 2 (mem 2 1 ⇔ ex 3 (mem 3 0 ⊓ mem 2 3))))

/-- Power set: for every `x` the set `𝒫(x)` exists. -/
def powerset : SFormula := all 0 (ex 1 (isPowerset 1 0))

/-- Infinity: an inductive set exists. -/
def infinity : SFormula := ex 0 (isInductive 0)

/-- Choice: every set `x` of nonempty, pairwise disjoint sets has a choice set `c`, meeting
each member of `x` in exactly one element. -/
def choice : SFormula :=
  all 0 ((all 1 (mem 1 0 ⟹ ex 2 (mem 2 1)) ⊓
      all 1 (all 2 ((mem 1 0 ⊓ mem 2 0 ⊓ ∼(eq 1 2)) ⟹ ∼(ex 3 (mem 3 1 ⊓ mem 3 2))))) ⟹
    ex 4 (all 1 (mem 1 0 ⟹
      ex 2 (mem 2 1 ⊓ mem 2 4 ⊓ all 3 ((mem 3 1 ⊓ mem 3 4) ⟹ eq 3 2)))))

/-- `σ` is an instance of the separation schema
`∀ a ∃ b ∀ x (x ∈ b ↔ x ∈ a ∧ φ)`, where `b` is not free in `φ`
(the other free variables of `φ` are parameters). -/
def IsSeparation (σ : SFormula) : Prop :=
  ∃ (φ : SFormula) (x a b : ℕ), x ≠ a ∧ x ≠ b ∧ a ≠ b ∧ b ∉ φ.freeVarFinset ∧
    σ = all a (ex b (all x (mem x b ⇔ (mem x a ⊓ φ))))

/-- `σ` is an instance of the replacement schema
`∀ a ((∀ x ∈ a ∃! y φ(x, y)) → ∃ b ∀ x ∈ a ∃ y ∈ b φ(x, y))`, where `b` is not free in
`φ`; uniqueness `∃! y` is written `∃ y (φ(x, y) ∧ ∀ y' (φ(x, y') → y' = y))` with a fresh
variable `y'` (the other free variables of `φ` are parameters). -/
def IsReplacement (σ : SFormula) : Prop :=
  ∃ (φ : SFormula) (x y y' a b : ℕ), [x, y, y', a, b].Nodup ∧
    b ∉ φ.freeVarFinset ∧ y' ∉ φ.freeVarFinset ∧
    σ = all a
      (all x (mem x a ⟹
          ex y (φ ⊓ all y' (φ.subst (fun v => if v = y then Term.var y' else Term.var v) ⟹
            eq y' y))) ⟹
        ex b (all x (mem x a ⟹ ex y (mem y b ⊓ φ))))

/-- The axioms of ZF, as formulas (their universal closures are the axioms). -/
def ZFAxioms : Set SFormula :=
  {extensionality, foundation, pairing, union, powerset, infinity} ∪
    {σ | IsSeparation σ} ∪ {σ | IsReplacement σ}

/-- CH: for `w = ω` and `p = 𝒫(ω)`, every subset `x ⊆ p` either injects into `ω` or
`p` injects into `x`. -/
def ch : SFormula :=
  all 0 (isOmega 0 ⟹ all 1 (isPowerset 1 0 ⟹
    all 2 (subset 2 1 ⟹ (injects 2 0 ⊔ injects 1 2))))

/-- GCH: for every infinite set `s` and every set `t` with `|s| ≤ |t| ≤ |𝒫(s)|`,
`t` is equinumerous with `s` or with `𝒫(s)`. -/
def gch : SFormula :=
  all 0 (∼(isFiniteSet 0) ⟹ all 1 (isPowerset 1 0 ⟹
    all 2 ((injects 0 2 ⊓ injects 2 1) ⟹ (equinum 2 0 ⊔ equinum 2 1))))

end SFormula

open SFormula

/-- Zermelo–Fraenkel set theory, as a first-order theory in the language of set theory. -/
def ZF : setLang.Theory := close '' ZFAxioms

/-- The axiom of choice, as a sentence. -/
def acSentence : setLang.Sentence := close choice

/-- Zermelo–Fraenkel set theory with the axiom of choice. -/
def ZFC : setLang.Theory := ZF ∪ {acSentence}

/-- The continuum hypothesis, as a sentence of set theory. -/
def chSentence : setLang.Sentence := close ch

/-- The generalized continuum hypothesis, as a sentence of set theory. -/
def gchSentence : setLang.Sentence := close gch

end

end ContinuumHypothesis


