-- Prove2me | Definitions.Def_SNPTreedepth_Supplement_ESOSentence
-- name    : SNPTreedepth_Supplement_ESOSentence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:53:59.796702+00:00
-- url     : https://prove2.me/theorems/193f950b-b733-4597-900d-8f1ddcbf3320
-- title:
--   ESO sentences over graphs
-- statement:
--   An **existential second-order (ESO) sentence** over graphs has the form
--   $$
--   \varphi=\exists R_1\cdots\exists R_r\,\psi ,
--   $$
--   where $R_1,\dots,R_r$ are relation variables of arities $\mathrm{ar}_1,\dots,\mathrm{ar}_r$ and $\psi$ is an arbitrary first-order sentence (with any quantifiers) over the edge relation $E$, the relations $R_1,\dots,R_r$ and equality. A graph $G=(V,E)$ satisfies $\varphi$, written $G\models\varphi$, if there are relations $R'_j\subseteq V^{\mathrm{ar}_j}$ such that the expansion $(V,E,R'_1,\dots,R'_r)$ satisfies $\psi$.
--
--   SNP is the fragment in which $\psi$ is universal; Theorem 55 shows that the treedepth metatheorem does not extend to ESO.
--
--   **Formalization Note** $\psi$ is a Mathlib first-order sentence in the language with relation symbols $E$ (arity $2$) and $R_1,\dots,R_r$, and no function symbols.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), §6.2, p.52 (PDF p.53)

import Mathlib

set_option autoImplicit false

namespace SNPTreedepth.Supplement

/-- The relation symbols of an ESO sentence over graphs: the edge relation `E` (arity `2`) and the
relation variables `R₁, …, R_r` of arities `ar j`. -/
inductive ESORel (r : ℕ) (ar : Fin r → ℕ) : ℕ → Type
  /-- the input edge relation `E` -/
  | edge : ESORel r ar 2
  /-- the relation variable `R_j` -/
  | var (j : Fin r) : ESORel r ar (ar j)

/-- The first-order language of an ESO sentence over graphs: no function symbols, the relation
symbols `E, R₁, …, R_r` (equality is built into Mathlib's first-order logic). -/
def esoLang (r : ℕ) (ar : Fin r → ℕ) : FirstOrder.Language :=
  ⟨fun _ => Empty, ESORel r ar⟩

/-- The expansion `(V, E, R'₁, …, R'_r)` of a graph `G` by relations `R'_j ⊆ V^{ar j}`, as a
structure of `esoLang r ar`: `E(x, y)` holds iff `xy` is an edge, `R_j(x̄)` iff `x̄ ∈ R'_j`. -/
@[instance_reducible]
def esoStructure {V : Type} {r : ℕ} {ar : Fin r → ℕ} (G : SimpleGraph V)
    (S : (j : Fin r) → Set (Fin (ar j) → V)) : (esoLang r ar).Structure V where
  funMap := fun {_} f => Empty.elim f
  RelMap := fun {n} R xs =>
    match n, R, xs with
    | _, .edge, xs => G.Adj (xs 0) (xs 1)
    | _, .var j, xs => xs ∈ S j

/-- An **ESO sentence** over graphs `φ = ∃R₁ … ∃R_r ψ` (Depian et al., *A Uniform Algorithm for
Strict NP on Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…),
§6.2, p.52: "ESO formulas are of the form ∃R₁, …, ∃R_r ψ, where ψ is a first-order formula"): the
relation variables `R_j` of arities `ar j`, and `ψ` an arbitrary first-order sentence (any
quantifiers) over `E`, `R₁, …, R_r` and equality.

**Formalization Note** `ψ` is a Mathlib `FirstOrder.Language.Sentence` of `esoLang r ar`; it is not
restricted to universal or prenex form (that restriction would make `φ` an SNP sentence). -/
structure ESOSentence where
  /-- the number `r` of relation variables -/
  r : ℕ
  /-- the arity of each relation variable -/
  ar : Fin r → ℕ
  /-- the first-order part `ψ` -/
  ψ : (esoLang r ar).Sentence

/-- `G ⊨ φ` for an ESO sentence (Depian et al., §6.2, p.52): there are relations
`R'_j ⊆ V^{ar j}` such that the expansion `(V, E, R'₁, …, R'_r)` satisfies `ψ`. -/
def ESOSentence.Models {V : Type} (φ : ESOSentence) (G : SimpleGraph V) : Prop :=
  ∃ S : (j : Fin φ.r) → Set (Fin (φ.ar j) → V),
    letI : (esoLang φ.r φ.ar).Structure V := esoStructure G S
    FirstOrder.Language.Sentence.Realize V φ.ψ

end SNPTreedepth.Supplement


