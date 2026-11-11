-- Prove2me | Definitions.Def_ConantTerry_Orders_tree_embeddings
-- name    : ConantTerry_Orders_tree_embeddings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:46.969978+00:00
-- url     : https://prove2.me/theorems/f5f0b24d-8dca-472c-8118-b9f3611387e7
-- title:
--   Branch-preserving tree embeddings and properness
-- statement:
--   An embedding between truncated binary-word trees is a map $\phi$ that preserves the bit at every branching step:
--   $$
--   \sigma\mathbin{{}^\frown}a\unlhd\tau
--   \Longrightarrow
--   \phi(\sigma)\mathbin{{}^\frown}a\unlhd\phi(\tau)
--   \qquad(a\in\{0,1\}).
--   $$
--   For $\phi:B_{\le s}\to B_{\le t}$, properness additionally requires
--   $$
--   |\sigma|=s\Longrightarrow|\phi(\sigma)|=t.
--   $$
--   For positive strict heights, properness of $\phi:B_{<s}\to B_{<t}$ requires $|\sigma|+1=s\Longrightarrow|\phi(\sigma)|+1=t$, expressing $B_{<s}=B_{\le s-1}$. Neither root preservation, level preservation nor injectivity is assumed in the embedding predicate. Injectivity is a conclusion of Proposition 2.2(a).
--
--   These definitions retain the orientation needed to restrict real-valued function trees; preservation of prefix order alone is insufficient. The generic branch predicate is stated on word subtypes so that both truncation conventions use exactly the same definition.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.7, Definition 2.1 and the strict-height convention in Proposition 2.2(b); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib
import Definitions.Def_ConantTerry_Orders_binary_words

namespace ConantTerry.Orders

/-- Definition 2.1(1), p.7, on any of the paper's truncated word sets.
The appended bit is preserved; neither root nor levels are fixed. -/
def IsTreeEmbedding {A B : Set (List Bool)} (φ : A → B) : Prop :=
  ∀ (σ τ : A) (a : Bool), List.IsPrefix (σ.val ++ [a]) τ.val →
    List.IsPrefix ((φ σ).val ++ [a]) (φ τ).val

/-- Definition 2.1(2), p.7: final-level leaves go to final-level leaves. -/
def IsProperEmbedding {s t : ℕ} (φ : WordsAtMost s → WordsAtMost t) : Prop :=
  IsTreeEmbedding φ ∧ ∀ σ : WordsAtMost s,
    σ.val.length = s → (φ σ).val.length = t

/-- Properness on strict truncations in Proposition 2.2(b).
For positive heights, `WordsBelow s` is `B_{≤s-1}`. Writing the last level
as `length + 1 = s` avoids truncated subtraction. -/
def IsProperBelow {s t : ℕ} (φ : WordsBelow s → WordsBelow t) : Prop :=
  IsTreeEmbedding φ ∧ ∀ σ : WordsBelow s,
    σ.val.length + 1 = s → (φ σ).val.length + 1 = t

end ConantTerry.Orders


