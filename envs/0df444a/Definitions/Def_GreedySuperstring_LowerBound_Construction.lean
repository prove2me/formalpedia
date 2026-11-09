-- Prove2me | Definitions.Def_GreedySuperstring_LowerBound_Construction
-- name    : GreedySuperstring_LowerBound_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:20.755109+00:00
-- url     : https://prove2.me/theorems/f0dc95cb-4b6c-427b-983b-42372bbf680b
-- title:
--   The five-word family, explicit short word, and merged long-word candidates
-- statement:
--   For $r\ge1$ and $P\ge r-1$, put $M=P+8r$ and $p_i=P+r+i$, for $1\le i\le r$. Define
--
--   $$\begin{aligned}
--   X_i&=[P+2r\mid p_i\ M\ p_i\ M\mid P],&Y_i&=[P\mid M\ p_i\ M\ p_i\mid P+4r],\\
--   U_i&=[P\mid M\ M\ p_i\ M\mid P],&V_i&=[P\mid M\ p_i\ M\ M\mid P+r],\\
--   Z_i&=[P+r\mid M\ M\ p_i\mid0].
--   \end{aligned}$$
--
--   The input is the union of these five words over the source's indices. The explicit short-word candidate is
--
--   $$H=[P+r\mid M\ M\ p_1\ M\ p_1\ \cdots\ M\ M\ p_r\ M\ p_r\ M\ M\mid P+r].$$
--
--   The intermediate words are computed by actual merges: $A_i=\langle X_i,Y_i\rangle$, $B_i=\langle U_i,V_i\rangle$, $C_i=\langle B_i,Z_i\rangle$, and $T_i=\langle A_i,C_i\rangle$. The long-word candidate is $T_1\circ\cdots\circ T_r$. Set $\alpha_i=5P+17r+i+1$, $\beta=4P+18r+1$, and $\gamma=2P+4r+1$.
--
--   These definitions provide the concrete family for Lemma 4.3 and witnesses available to the goal's solvers. They assume no cardinality, substring-freeness, containment, explicit intermediate gap forms, greedy validity, or exact length. All such claims remain mathematical obligations.
--
--   **Formalization Note** Parameters and source indices are natural numbers; source index $i$ remains $i$, and ascending enumeration uses list index $j$ for $i=j+1$. The definitions are total outside the source domain; theorems retain its full restrictions. Binary labels preserve symbol length.
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, §4.2–§4.4, printed pp.16–19 = PDF pp.16–19

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_GapModel
import Definitions.Def_GreedySuperstring_LowerBound_GreedyModel

namespace GreedySuperstring.LowerBound

/-- Section 4.2, p.16. The source domain is 1 ≤ r and r ≤ P+1. -/
def commonGap (r P : ℕ) : ℕ := P + 8 * r

def privateGap (r P i : ℕ) : ℕ := P + r + i

def X (r P i : ℕ) : OAI.Superstring.Word :=
  gapWord (P + 2 * r) [privateGap r P i, commonGap r P, privateGap r P i, commonGap r P] P

def Y (r P i : ℕ) : OAI.Superstring.Word :=
  gapWord P [commonGap r P, privateGap r P i, commonGap r P, privateGap r P i] (P + 4 * r)

def U (r P i : ℕ) : OAI.Superstring.Word :=
  gapWord P [commonGap r P, commonGap r P, privateGap r P i, commonGap r P] P

def V (r P i : ℕ) : OAI.Superstring.Word :=
  gapWord P [commonGap r P, privateGap r P i, commonGap r P, commonGap r P] (P + r)

def Z (r P i : ℕ) : OAI.Superstring.Word :=
  gapWord (P + r) [commonGap r P, commonGap r P, privateGap r P i] 0

/-- The actual union of five words per source index; no cardinality or
substring-free certificate is part of the definition. -/
def inputFamily (r P : ℕ) : Finset OAI.Superstring.Word :=
  (Finset.Icc 1 r).biUnion (fun i => {X r P i, Y r P i, U r P i, V r P i, Z r P i})

/-- Section 4.3, p.17: the explicit shorter common-superstring candidate. -/
def shortWord (r P : ℕ) : OAI.Superstring.Word :=
  gapWord (P + r)
    (((List.range r).flatMap (fun j =>
      [commonGap r P, commonGap r P, privateGap r P (j + 1),
       commonGap r P, privateGap r P (j + 1)])) ++ [commonGap r P, commonGap r P]) (P + r)

/-- Section 4.4, pp.18-19: intermediate words are computed by actual merges. -/
def A (r P i : ℕ) : OAI.Superstring.Word := merge (X r P i) (Y r P i)
def B (r P i : ℕ) : OAI.Superstring.Word := merge (U r P i) (V r P i)
def C (r P i : ℕ) : OAI.Superstring.Word := merge (B r P i) (Z r P i)
def T (r P i : ℕ) : OAI.Superstring.Word := merge (A r P i) (C r P i)

def longWord (r P : ℕ) : OAI.Superstring.Word :=
  ((List.range r).map (fun j => T r P (j + 1))).flatten

def alpha (r P i : ℕ) : ℕ := 5 * P + 17 * r + i + 1
def beta (r P : ℕ) : ℕ := 4 * P + 18 * r + 1
def gamma (r P : ℕ) : ℕ := 2 * P + 4 * r + 1

end GreedySuperstring.LowerBound


