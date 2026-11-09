-- Prove2me | Definitions.Def_ForestPersuasion_Symmetric_DP
-- name    : ForestPersuasion_Symmetric_DP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:08.559758+00:00
-- url     : https://prove2.me/theorems/a627e76f-5872-433e-a3f9-08b3f3150ade
-- title:
--   Subtree minimum F and the child-count convolution N
-- statement:
--   Fix the free real dual coefficients. For each subtree root $j$, the value $F(j,\kappa,q)$ is the minimum of the original dual-constraint expression over grid vectors on $D_j$, subject to root posterior $q$ and exactly $\kappa$ adopting proper descendants. It is defined directly from that expression, independently of recursion (7).
--
--   The child minimum chooses a posterior and a proper-descendant adoption count for each child, with the sum of child counts plus child adoption indicators equal to $\kappa$. The quantity $M_{i,b,l}$ groups choices having total adoption count $b$ in a child subtree. Children are ordered by their vertex labels. The table $N$ uses
--   $$N^j_{0,b}=\begin{cases}0&b=0,\\+\infty&b>0,\end{cases}\qquad
--   N^j_{\xi,b}=\min_{0\le\zeta\le\min(b,d_{i_\xi})}\{N^j_{\xi-1,b-\zeta}+M_{i_\xi,\zeta,l}\}.$$
--
--   All constrained minima are in the extended reals. Their finite candidate costs exclude negative infinity, and an empty candidate set has value positive infinity. The table's total-function convention after the last child is irrelevant to the stated identities.
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), §5, minimum defining F, recursion (7) and N recursion, PDF pp. 14–15 (printed pp. 13–14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_LPs

open scoped NNReal ENNReal
open Classical
noncomputable section

namespace ForestPersuasion.Symmetric

/-- Descendant adoption count using only coordinates in D_j. No outside coordinates. -/
def subtreeK {n : ℕ} (I : Model n) (j : Fin n) (v : SubtreeVector I j) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun r : {r // r ∈ I.hierarchy.descendants j} =>
    r.val ∈ I.hierarchy.descendants i ∧ r.val ≠ i ∧ threshold I r.val ≤ (v r).val)).card

/-- The expression minimized in the definition of F (PDF p. 14).
Only internal edges of D_j contribute. -/
def subtreeCost {n : ℕ} (I : Model n) (C : DualCoefficients I) (j : Fin n)
    (v : SubtreeVector I j) : ℝ :=
  (∑ i : {i // i ∈ I.hierarchy.descendants j},
    (1 - (v i).val) * C.gamma i.val (subtreeK I j v i.val) (v i)) +
  ∑ a : {a // a ∈ I.hierarchy.descendants j},
    ∑ b : {b // b ∈ I.hierarchy.descendants j},
      if I.hierarchy.Edge a.val b.val then
        ((v a).val - (v b).val) * C.delta (a.val, b.val) (subtreeK I j v b.val) (v b)
      else 0

/-- F is the minimum of the original subtree expression, independently of recursion (7).
EReal iInf gives +∞ on an empty constraint set. All feasible costs form a finite real set. -/
def F {n : ℕ} (I : Model n) (C : DualCoefficients I) (j : Fin n) (κ : ℕ) (q : Grid I) : EReal :=
  ⨅ v : SubtreeVector I j, ⨅ (_ : v (selfNode I j) = q ∧ subtreeK I j v j = κ),
    (subtreeCost I C j v : EReal)

abbrev ChildChoice {n : ℕ} (I : Model n) (j : Fin n) :=
  (i : {i // i ∈ I.hierarchy.children j}) →
    Fin (I.hierarchy.descendants i.val).card × Grid I

def childCount {n : ℕ} (I : Model n) (j : Fin n) (c : ChildChoice I j) : ℕ :=
  ∑ i, ((c i).1.val + if threshold I i.val ≤ (c i).2.val then 1 else 0)

def childrenMinimum {n : ℕ} (I : Model n) (C : DualCoefficients I)
    (j : Fin n) (κ : ℕ) (q : Grid I) : EReal :=
  ⨅ c : ChildChoice I j, ⨅ (_ : childCount I j c = κ),
    ∑ i : {i // i ∈ I.hierarchy.children j},
      (F I C i.val (c i).1.val (c i).2 +
        (((q.val - (c i).2.val) * C.delta (j, i.val) (c i).1.val (c i).2 : ℝ) : EReal))

/-- M_{i,b,l} for a fixed parent j and parent grid value q=τ_l. -/
def Mmin {n : ℕ} (I : Model n) (C : DualCoefficients I)
    (j i : Fin n) (b : ℕ) (q : Grid I) : EReal :=
  ⨅ c : Fin (I.hierarchy.descendants i).card × Grid I,
    ⨅ (_ : c.1.val + (if threshold I i ≤ c.2.val then 1 else 0) = b),
      F I C i c.1.val c.2 + (((q.val - c.2.val) * C.delta (j, i) c.1.val c.2 : ℝ) : EReal)

/-- Increasing vertex order fixes the paper's arbitrary order i_1,...,i_s. -/
def childrenList {n : ℕ} (I : Model n) (j : Fin n) : List (Fin n) :=
  (I.hierarchy.children j).sort (· ≤ ·)

/-- N^j_{ξ,b} as defined on PDF pp. 14–15. Out-of-range child indices use j;
the statements use only ξ≤s(j), so this total-function convention is never read. -/
def N {n : ℕ} (I : Model n) (C : DualCoefficients I) (j : Fin n) (q : Grid I) :
    ℕ → ℕ → EReal
  | 0, b => if b = 0 then 0 else ⊤
  | ξ + 1, b =>
    let i := (childrenList I j).getD ξ j
    ⨅ ζ : Fin (min b (I.hierarchy.descendants i).card + 1),
      N I C j q ξ (b - ζ.val) + Mmin I C j i ζ.val q

end ForestPersuasion.Symmetric


