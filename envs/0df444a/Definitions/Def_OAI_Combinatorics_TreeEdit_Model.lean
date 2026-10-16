-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_Model
-- name    : OAI_Combinatorics_TreeEdit_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:11:56.268986+00:00
-- url     : https://prove2.me/theorems/f8fd5934-73b8-447d-bf3c-5e3e9247b335
-- title:
--   Longest common subsequence, deficit, fixed-length words and block encodings
-- statement:
--   This file fixes the basic string notions used to study unit-cost edit distance. Throughout, $\alpha$ and $\beta$ are arbitrary alphabets, a word over $\alpha$ is a finite sequence $x=x_1x_2\cdots x_\ell$ of symbols, and $|x|=\ell$ is its length. A word $z$ is a *subsequence* of $x$ if it is obtained from $x$ by deleting some positions, which need not be contiguous.
--
--   1. **Longest common subsequence.** For words $x,y$ over $\alpha$,
--
--      $$\operatorname{lcs}(x,y)=\max\bigl\{\,|z| : z \text{ is a subsequence of both } x \text{ and } y\,\bigr\}.$$
--
--   2. **Deficit.** $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$, the number of symbols of $x$ that a longest common subsequence leaves unmatched. It is one-sided in general; it is intended for words of equal length, where it is symmetric.
--
--   3. **Fixed-length words.** For $n\in\mathbb{N}$, $\mathrm{Word}(\alpha,n)$ is the set of words over $\alpha$ of length exactly $n$, with no restriction on the symbols at any position.
--
--   4. **Block encoding.** A fixed-width code $c:\alpha\to\mathrm{Word}(\beta,P)$ is extended to all finite words over $\alpha$, of any length, by concatenation:
--
--      $$\operatorname{enc}_c(x_1x_2\cdots x_\ell)=c(x_1)\,c(x_2)\cdots c(x_\ell),$$
--
--      a word over $\beta$ of length $\ell P$.
--
--   5. **Bit vectors as words.** A vector $v:\{0,\dots,P-1\}\to\{0,1\}$ is read as the binary word $v(0)v(1)\cdots v(P-1)\in\mathrm{Word}(\{0,1\},P)$.
--
--   Edit distance counts the least number of single-symbol insertions, deletions and substitutions turning one word into another. The longest common subsequence and the deficit are the combinatorial quantities through which separation of words is measured and edit distance is bounded from below, while block encodings transport words over a large alphabet to binary words of one common length.
--
--   **Formalization Note** `lcs x y` is the `sSup` of the set of lengths of common subsequences (`List.Sublist`); this set contains $0$ and is bounded by $|x|$, so the supremum is a maximum. `deficit` uses natural-number subtraction, which never truncates since $\operatorname{lcs}(x,y)\le|x|$. `Word α n` is the subtype of lists of length `n`, `encode c x` is `x.flatMap (fun a => (c a).val)`, and `vectorWord v` is `List.ofFn v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit

namespace OAI

namespace TreeEdit

universe u v

/-- The length of a longest arbitrary common subsequence. -/
noncomputable def lcs {α : Type u} (x y : List α) : ℕ :=
  sSup {n | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = n}

/-- One-sided deficit; used below only when the two lengths agree. -/
noncomputable def deficit {α : Type u} (x y : List α) : ℕ := x.length - lcs x y

/-- Fixed-length words, with symbols at every position arbitrary. -/
abbrev Word (α : Type u) (n : ℕ) := {x : List α // x.length = n}

/-- The concatenation extension of a fixed-width symbol code, on *all* finite words. -/
def encode {α : Type u} {β : Type v} {P : ℕ} (c : α → Word β P) (x : List α) : List β :=
  x.flatMap (fun a => (c a).val)

def vectorWord {P : ℕ} (v : Fin P → Bool) : Word Bool P :=
  ⟨List.ofFn v, List.length_ofFn⟩

end TreeEdit

end OAI


