-- Prove2me | Definitions.Def_GreedySuperstring_LowerBound_GapModel
-- name    : GreedySuperstring_LowerBound_GapModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:05.210399+00:00
-- url     : https://prove2.me/theorems/4826d65d-78fb-4a1e-99fb-e8d54efd5338
-- title:
--   Binary gap words and the three overlap matching tests
-- statement:
--   Use the two distinct symbol labels $[\mathrm{false}]$ and $[\mathrm{true}]$ for zero and one, in the published finite-word carrier. A word is binary if every symbol is one of these labels. For nonnegative pads $L,R$ and a list of positive gaps $g_1,\ldots,g_k$, set
--
--   $$[L\mid g_1\cdots g_k\mid R]=0^L1\,0^{g_1-1}1\cdots0^{g_k-1}1\,0^R.$$
--
--   The empty gap list gives $0^L10^R$, and its length is $L+1+R$; in general the length is $L+1+\sum_i g_i+R$. A gap is the distance between consecutive ones.
--
--   For gap lists $u,v$ of lengths $k,\ell$, the finite matching set $J$ consists of $0\le j\le\min(k,\ell)$ for which the last $j$ gaps of $u$ equal the first $j$ of $v$, the left pad $L'$ fits strictly below the preceding gap of $u$ (or $L'\le L$ at $j=k$), and the right pad $R$ fits strictly below the next gap of $v$ (or $R\le R'$ at $j=\ell$). These Boolean tests compute exactly Lemma 4.2's set; they do not assert its conclusion.
--
--   **Formalization Note** Gap-word construction is total, but every source use requires positive gaps; a zero gap would use truncated subtraction and lies outside that domain. Guarded optional indexing supplies no arbitrary out-of-range value. Natural list indices encode the source's one-based gap entries.
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, §4.1 and Lemma 4.2, printed p.15 = PDF p.15

import Mathlib
import Definitions.Def_Superstring
import Definitions.Def_GreedySuperstring_LowerBound_WordModel

namespace GreedySuperstring.LowerBound

def zeroSymbol : OAI.Superstring.Symbol := [false]
def oneSymbol : OAI.Superstring.Symbol := [true]

def IsBinary (w : OAI.Superstring.Word) : Prop :=
  ∀ a ∈ w, a = zeroSymbol ∨ a = oneSymbol

/-- Section 4.1, p.15. A gap is a distance, contributing g-1 zeros.
The source domain requires every gap positive. Empty gaps leave one 1. -/
def gapWord (L : ℕ) (gaps : List ℕ) (R : ℕ) : OAI.Superstring.Word :=
  List.replicate L zeroSymbol ++ [oneSymbol] ++
    gaps.flatMap (fun g => List.replicate (g - 1) zeroSymbol ++ [oneSymbol]) ++
    List.replicate R zeroSymbol

/-- Lemma 4.2's three tests. Accesses at j=k or j=ell are avoided;
optional indexing in the other branch has no arbitrary default value.
The tests are Boolean so that the finite set J is computational. -/
def gapTests (L R : ℕ) (u : List ℕ) (L' R' : ℕ) (v : List ℕ) (j : ℕ) : Bool :=
  decide (u.drop (u.length - j) = v.take j) &&
  (if j = u.length then decide (L' ≤ L)
   else (u[u.length - j - 1]?).any (fun g => decide (L' < g))) &&
  (if j = v.length then decide (R ≤ R')
   else (v[j]?).any (fun g => decide (R < g)))

/-- The finite set J includes j=0, and all k=0 or ell=0 boundary cases. -/
def gapMatches (L R : ℕ) (u : List ℕ) (L' R' : ℕ) (v : List ℕ) : Finset ℕ :=
  (Finset.range (min u.length v.length + 1)).filter (fun j => gapTests L R u L' R' v j = true)

end GreedySuperstring.LowerBound


