-- Prove2me | Definitions.Def_FOMCMonDep_encSentence
-- name    : FOMCMonDep_encSentence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:33.442913+00:00
-- url     : https://prove2.me/theorems/6e9e5c8f-080c-48c2-84b3-b8595b0019e8
-- title:
--   Input code of a first-order sentence over graphs
-- statement:
--   The model checking algorithm takes both the graph $G$ and the sentence $\varphi$ as input. Sentences are first-order sentences with equality over the signature $\{E\}$ of graphs. A sentence is input as its **prefix (Polish) code**: $\bot\mapsto[0]$, $t_1=t_2\mapsto[1,t_1,t_2]$, $E(t_1,t_2)\mapsto[2,t_1,t_2]$, $\varphi\to\psi\mapsto 3$ followed by the codes of $\varphi$ and $\psi$, and $\forall\varphi\mapsto 4$ followed by the code of $\varphi$, where variables are coded by their indices.
--
--   The code is injective (proved in the mission's verification file), and every entry is a natural number at most the length of the code plus $4$, so it fits in a machine word of logarithmically many bits.
--
--   **Formalization Note** Sentences are Mathlib `Language.graph` sentences; bound variables are Mathlib's indices.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §1, p.2 (PDF 4)

import Mathlib

set_option autoImplicit false

open FirstOrder FirstOrder.Language

namespace FOMCMonDep

/-- The code of a term of the language of graphs with no free variables and `l` bound variables: the index of the
bound variable. (The language of graphs has no function symbols, and `Empty` has no elements.) -/
def encTerm {l : ℕ} : Language.graph.Term (Empty ⊕ Fin l) → ℤ
  | .var (.inl e) => e.elim
  | .var (.inr i) => ((i : ℕ) : ℤ)
  | .func f _ => f.elim

/-- The prefix (Polish) code of a formula of the language of graphs with `l` bound variables: `⊥` is `[0]`,
`t₁ = t₂` is `[1, t₁, t₂]`, `E(t₁, t₂)` is `[2, t₁, t₂]`, `φ → ψ` is `3` followed by the codes of `φ` and `ψ`,
and `∀ φ` is `4` followed by the code of `φ`. Bound variables are Mathlib's indices `Fin l`. -/
def encFormula : {l : ℕ} → Language.graph.BoundedFormula Empty l → List ℤ
  | _, .falsum => [0]
  | _, .equal t₁ t₂ => [1, encTerm t₁, encTerm t₂]
  | _, .rel .adj ts => [2, encTerm (ts 0), encTerm (ts 1)]
  | _, .imp φ ψ => 3 :: (encFormula φ ++ encFormula ψ)
  | _, .all φ => 4 :: encFormula φ

/-- **The input code of a first-order sentence over graphs.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §1, p.2 (PDF 4): "our
algorithm is uniform: it takes both G and φ as input". The paper fixes no input format for φ.

**Formalization Note.** A sentence is a Mathlib `Language.graph.Sentence`: first-order logic with equality over the
one binary symbol `E` (`adj`). It is input as its prefix code `encFormula`, an injective code (proved in the
mission's verification file) in which every entry is a natural number at most the length of the code plus `4`, so
every entry fits in a word of `O(log)` bits of the input length. -/
def encSentence (φ : Language.graph.Sentence) : List ℤ := encFormula φ

end FOMCMonDep


