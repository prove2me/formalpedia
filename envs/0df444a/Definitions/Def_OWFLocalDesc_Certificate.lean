-- Prove2me | Definitions.Def_OWFLocalDesc_Certificate
-- name    : OWFLocalDesc_Certificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:03.691851+00:00
-- url     : https://prove2.me/theorems/c9dd822f-fc3a-4ffb-aaa9-2e1464ef95fa
-- title:
--   Public-randomness sample certificate (Definition 2.5)
-- statement:
--   For a sample size $m$, a **certificate** is a triple $(A,a,\beta)$ where $A\subseteq[m]$ is the set of retained points (anchors), $a\in\{0,1\}^{|A|}$ is a string of tags and $\beta\in\{0,1\}^*$ is the program.
--
--   For a point vector $x=(x_1,\dots,x_m)\in(\{0,1\}^n)^m$, the **anchor list** $L_A$ is the string
--   $$L_A = x_{i_1}a_1\,x_{i_2}a_2\cdots x_{i_k}a_k,$$
--   where $i_1<\dots<i_k$ enumerate $A$ and $a_1,\dots,a_k$ are the tags.
--
--   **Formalization Note** Indices are $0,\dots,m-1$ (`Fin m`) instead of $1,\dots,m$. The tags are a list whose length equals $|A|$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.12

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Certificate (Definition 2.5).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.12: "A
certificate is a triple (A, a, β), where A ⊆ [m] is the retained-point index set, a ∈ {0,1}^{|A|}
is a string of tags, and β is a finite binary string, the program."

**Formalization Note.** Indices are `Fin m` (zero-based; the paper's `[m] = {1,…,m}`). -/
structure Certificate (m : ℕ) where
  /-- The retained-point (anchor) index set `A`. -/
  A : Finset (Fin m)
  /-- The tags `a`, one bit per retained point, in increasing index order. -/
  tags : List Bool
  tags_length : tags.length = A.card
  /-- The program `β`. -/
  prog : List Bool

/-- **The anchor list `L_A`.** Definition 2.5, p.12: "As a sequential input, L_A is the string
x_{i1}a_1 ··· x_{ik}a_k, where i1 < ··· < ik enumerate A and a_1,…,a_k are the tags." -/
def Certificate.anchorList {m n : ℕ} (c : Certificate m) (x : Fin m → Fin n → Bool) :
    List Bool :=
  ((c.A.sort (· ≤ ·)).zip c.tags).flatMap fun p => List.ofFn (x p.1) ++ [p.2]

end OWFLocalDesc


