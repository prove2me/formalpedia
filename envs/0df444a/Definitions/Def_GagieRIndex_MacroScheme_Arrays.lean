-- Prove2me | Definitions.Def_GagieRIndex_MacroScheme_Arrays
-- name    : GagieRIndex_MacroScheme_Arrays
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:41.857337+00:00
-- url     : https://prove2.me/theorems/b124ee92-7946-49e2-80a4-8930886fb98e
-- title:
--   §2.1, §5.2, §6.1 and Lemma 17 — lcp, LCP, DLCP, DSA and the explicit cells $p_i+k$
-- statement:
--   For two strings $S,S'$, $\operatorname{lcp}(S,S')$ is the length of their longest common prefix. With $T[1..n]$ a text and $SA$ its suffix array, the longest common prefix array, the differential LCP array and the differential suffix array are
--   $$LCP[1]=0,\quad LCP[p]=\operatorname{lcp}(T[SA[p-1]..],\,T[SA[p]..])\ (p>1),$$
--   $$DLCP[1]=LCP[1],\quad DLCP[i]=LCP[i]-LCP[i-1]\ (i>1),\qquad DSA[1]=SA[1],\quad DSA[p]=SA[p]-SA[p-1]\ (p>1).$$
--   The differential arrays take integer values, since consecutive entries of $LCP$ or $SA$ may decrease.
--
--   For Lemma 17 the definition also fixes the set of **explicit cells**: a position $x\in[1..n]$ is explicit when $x\in\{p_i,\,p_i+1,\,p_i+2\}$ for some run start $p_i$ of $BWT$.
--
--   These arrays are the objects of §5–§6: runs of the BWT induce repeated substrings of $DSA$ and $DLCP$, which is what makes them compressible.
--
--   **Formalization Note** $DLCP$ and $DSA$ are $\mathbb Z$-valued. The explicit cells are the paper's $DLCP[p_i+k]$, $k\in\{0,1,2\}$, restricted to the cells that exist ($\le n$); when a run has length 1 or 2 they coincide with the next run's cells, and the set is taken as a union.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 7 (§2.1, lcp and LCP); p. 20 (§5.2, DSA); p. 26 (§6.1, DLCP); p. 28 (Lemma 17, explicit symbols)

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core
import Definitions.Def_GagieRIndex_Locate_Arrays

namespace GagieRIndex.MacroScheme

/-- `lcp(S, S′)`, the length of the longest common prefix of two strings (§2.1, p. 7). -/
def lcpLen : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => if a = b then lcpLen as bs + 1 else 0
  | _, _ => 0

/-- `LCP[1] = 0` and `LCP[p] = lcp(T[SA[p − 1]..], T[SA[p]..])` (§2.1, p. 7). -/
def LCP (n : ℕ) (T SA : ℕ → ℕ) (p : ℕ) : ℕ :=
  if p ≤ 1 then 0 else lcpLen (GagieRIndex.Locate.suffix n T (SA (p - 1))) (GagieRIndex.Locate.suffix n T (SA p))

/-- `DLCP[i] = LCP[i] − LCP[i − 1]` if `i > 1`, `DLCP[1] = LCP[1]` (§6.1, p. 26). -/
def DLCP (n : ℕ) (T SA : ℕ → ℕ) (p : ℕ) : ℤ :=
  if p ≤ 1 then (LCP n T SA 1 : ℤ) else (LCP n T SA p : ℤ) - LCP n T SA (p - 1)

/-- Position `x` is one of the explicit symbols `DLCP[p_i + k]`, `k ∈ {0,1,2}`, of Lemma 17 (p. 28):
`x ∈ [1..n]` and `x ∈ {p, p + 1, p + 2}` for some run start `p` of `BWT`. -/
def IsExplicit17 (n : ℕ) (T SA : ℕ → ℕ) (x : ℕ) : Prop :=
  1 ≤ x ∧ x ≤ n ∧ ∃ p, p ≤ x ∧ x ≤ p + 2 ∧ GagieRIndex.Locate.IsRunStart n T SA p

end GagieRIndex.MacroScheme


