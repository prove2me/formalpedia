-- Prove2me | Definitions.Def_PochetWolsey_Mixing_Geometry
-- name    : PochetWolsey_Mixing_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:58.739492+00:00
-- url     : https://prove2.me/theorems/78e11f46-5f03-45c5-a203-61128f4c2a59
-- title:
--   Mixing vertices, recession directions, and extreme rays
-- statement:
--   For the mixing set with right-hand side $b\in\mathbb R^K$, let $f_0=0$ and $f_j=b_j-\lfloor b_j\rfloor$ for $1\le j\le K$. Define the candidate points and ray representatives by
--   $$
--   v^j=(f_j,(\lceil b_k-f_j\rceil)_{k=1}^K),\qquad
--   r^0=(1,-\mathbf1),\qquad r^k=(0,e_k).
--   $$
--   For any set $P\subseteq\mathbb R\times\mathbb R^K$, its recession set consists of directions $d$ such that $p+td\in P$ for every $p\in P$ and $t\ge0$. A nonzero direction $d$ is an extreme-ray direction when it belongs to this recession set and every decomposition $d=u+v$ into recession directions has both $u$ and $v$ nonnegative scalar multiples of $d$. These are candidate points and generic geometric predicates; their completeness for the mixing hull is a separate theorem.
--
--   **Formalization Note** Rays are considered up to positive scaling, with the displayed vectors serving as representatives. The zero direction is excluded from the extreme-ray predicate. The candidate point family may contain duplicates when fractional parts coincide. Recession of the empty set is the entire ambient space by this universal definition; the mixing hull used in the theorem is nonempty.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 189, 242 (PDF 203, 256), Definitions 6.8–6.9 and Proposition 8.3

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Model

namespace PochetWolsey.Mixing

noncomputable def vertex {K : ℕ} (b : Fin K → ℝ) (j : Option (Fin K)) : Point K :=
  (level b j, fun k => (⌈b k - level b j⌉ : ℝ))

def ray {K : ℕ} : Option (Fin K) → Point K
  | none => (1, fun _ => -1)
  | some k => (0, fun l => if l = k then 1 else 0)

def recession {K : ℕ} (P : Set (Point K)) : Set (Point K) :=
  {d | ∀ p ∈ P, ∀ t : ℝ, 0 ≤ t → p + t • d ∈ P}

def IsExtremeRay {K : ℕ} (P : Set (Point K)) (d : Point K) : Prop :=
  d ≠ 0 ∧ d ∈ recession P ∧
    ∀ u ∈ recession P, ∀ v ∈ recession P, d = u + v →
      (∃ a : ℝ, 0 ≤ a ∧ u = a • d) ∧ (∃ c : ℝ, 0 ≤ c ∧ v = c • d)

end PochetWolsey.Mixing


