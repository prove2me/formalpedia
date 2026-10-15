-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Words
-- name    : OAI_Analysis_LipschitzFree_Words
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:07:59.251574+00:00
-- url     : https://prove2.me/theorems/185b29e7-9953-4d24-83d7-17062f66f9a6
-- title:
--   Words of a fixed length $n$ over an alphabet $D$ and their number $|D|^n$
-- statement:
--   For a set $D$ (the alphabet) and $n\in\mathbb{N}$, let $\mathrm{W}_n(D)$ be the set of words (finite lists) over $D$ of length exactly $n$.
--
--   1. Reading off the letters gives a bijection
--   $$\mathrm{W}_n(D)\;\cong\;D^{\{0,1,\dots,n-1\}},\qquad w=w_0w_1\cdots w_{n-1}\ \mapsto\ (i\mapsto w_i),$$
--   whose inverse sends a function $f$ to the word $f(0)f(1)\cdots f(n-1)$.
--   2. If $D$ is finite, then $\mathrm{W}_n(D)$ is finite and
--   $$|\mathrm{W}_n(D)|=|D|^n .$$
--
--   Words of length $n$ over the port set of a port graph index the walks of $n$ moves from a given vertex, so this count is the basic bound for the number of such walks.
--
--   **Formalization Note** `Words D n` is the subtype `{w : List D // w.length = n}`; `Words.equivFun` is the bijection with `Fin n → D` (via `List.get` and `List.ofFn`), it induces the `Fintype` instance, and `Words.card` states the cardinality formula with `Fintype.card`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Words.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Words.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment

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


