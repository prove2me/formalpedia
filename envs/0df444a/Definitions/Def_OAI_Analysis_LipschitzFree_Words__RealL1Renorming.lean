-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_Words__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:03:50.636975+00:00
-- url     : https://prove2.me/theorems/9bd4b92a-e8b4-48c0-8247-f7e783565c69
-- title:
--   Words of fixed length over a finite alphabet and their number $|D|^n$
-- statement:
--   For a set $D$ (an alphabet, for instance the ports of a port graph) and $n\in\mathbb{N}$, let $W_n(D)$ be the set of words over $D$ of length exactly $n$, i.e. finite lists $w=(w_0,\dots,w_{n-1})$ of elements of $D$.
--
--   1. Listing the letters gives a bijection between $W_n(D)$ and the set of functions $\{0,1,\dots,n-1\}\to D$: a word $w$ corresponds to $i\mapsto w_i$, and a function $f$ corresponds to the word $(f(0),\dots,f(n-1))$.
--   2. If $D$ is finite, then $W_n(D)$ is finite and
--   $$|W_n(D)|=|D|^{\,n}.$$
--
--   These counts bound the number of walks of a given length in a port graph with finitely many ports.
--
--   **Formalization Note** `Words D n` is the subtype of `List D` of lists of length $n$, `Words.equivFun` is the bijection with `Fin n → D`, and `Words.card` is the cardinality formula.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Words.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Words.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming

namespace OAI

/-!
# Finite words of prescribed length
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical

def Words (D : Type*) (n : ℕ) := {w : List D // w.length = n}

namespace Words
variable {D : Type*} {n : ℕ}

def equivFun : Words D n ≃ (Fin n → D) where
  toFun w i := w.val.get ⟨i.val, by rw [w.property]; exact i.isLt⟩
  invFun f := ⟨List.ofFn f, List.length_ofFn⟩
  left_inv w := by
    rcases w with ⟨w, rfl⟩
    apply Subtype.ext
    simp
  right_inv f := by funext i; simp

instance [Fintype D] : Fintype (Words D n) := Fintype.ofEquiv _ equivFun.symm

@[simp] theorem card [Fintype D] : Fintype.card (Words D n) = Fintype.card D ^ n := by
  rw [Fintype.card_congr equivFun, Fintype.card_fun, Fintype.card_fin]

end Words
end DiscreteFree
end

end

end OAI


