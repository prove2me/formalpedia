-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity
-- name    : OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T18:55:24.236989+00:00
-- url     : https://prove2.me/theorems/9e7cfb76-3480-4078-b240-661c13a8f231
-- title:
--   Multiplicity of a group in a finite row set
-- statement:
--   Let $\iota$ and $\kappa$ be types, let $s\subset\iota$ be finite, and let $g:\iota\to\kappa$. For $a\in\kappa$, define
--
--   $$m_s(g,a)=\#\{i\in s:g(i)=a\}. $$
--
--   The definition assumes decidable equality on $\kappa$. It counts how many rows occupy each group and provides the original data for collision bounds. No finiteness assumption on either ambient type is required.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/CollisionCombinatorics.lean#L34-L36

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace OAI.PiExponent.Collision

open scoped BigOperators

def multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (a : κ) : ℕ :=
  (rows.filter fun i => group i = a).card

end OAI.PiExponent.Collision


