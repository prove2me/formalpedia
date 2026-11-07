-- Prove2me | Definitions.Def_DoublingMST_ListsPairCover
-- name    : DoublingMST_ListsPairCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:29.778859+00:00
-- url     : https://prove2.me/theorems/af01e20c-8f00-4618-853e-e8a1e1392b63
-- title:
--   $\Psi$ and $\Phi$ in integer memory
-- statement:
--   The memory layout of the output of Lemma 3.3's algorithm. Cell $-1$ holds $|\Psi|$. The $i$-th pair $(u,v)$ of $\Psi$, in some order without repetition, occupies six cells: the label and level of $u$ in cells $-6i-2$, $-6i-3$; the label and level of $v$ in cells $-6i-4$, $-6i-5$; and in cells $-6i-6$, $-6i-7$ pointers to explicit lists of $B(u,2^{\mathrm{lev}(u)})$ and $B(v,2^{\mathrm{lev}(v)})$. Different pairs may share a list.
--
--   Sharing matches the paper's proof (p.55), which constructs one ball per net point.
--
--   **Formalization Note** The paper fixes no layout, so this one is a convention of this formalization.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 3.3, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_DoublingMST_ball
import Definitions.Def_DoublingMST_ListsPoints

namespace DoublingMST

/-- **Ψ and Φ in integer memory (the output of Lemma 3.3's algorithm).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 3.3, pp.14–15 (PDF pp.16–17): "computes … a collection Ψ of pairs of net points", and
"Φ = {(B(u, 2^{lev(u)}), B(v, 2^{lev(v)})) : (u, v) ∈ Ψ} is a t-WSPC of X, and it can be constructed in
time t^{O(ddim)}n log ∆."

`ListsPairCover d ι Ψ mem`: `mem (−1) = |Ψ|`, and the `i`-th pair `(u, v)` of `Ψ`, in some order
without repetition, occupies six cells below it:
* `mem (−6i − 2) = ι u`, `mem (−6i − 3) = lev u`, `mem (−6i − 4) = ι v`, `mem (−6i − 5) = lev v`;
* `mem (−6i − 6)` points to an explicit list of `B(u, 2^{lev u})`;
* `mem (−6i − 7)` points to an explicit list of `B(v, 2^{lev v})`.

**Formalization Note.** A fixed layout, chosen because the page fixes none. Lists may be shared:
the page constructs one ball per net point, and pairs refer to them. -/
def ListsPairCover {n : ℕ} (d : Fin n → Fin n → ℝ) (ι : Fin n → ℤ)
    (Ψ : Finset ((Fin n × ℕ) × (Fin n × ℕ))) (mem : ℤ → ℤ) : Prop :=
  ∃ l : List ((Fin n × ℕ) × (Fin n × ℕ)), l.Nodup ∧ l.toFinset = Ψ ∧ mem (-1) = l.length ∧
    ∀ i (hi : i < l.length),
      mem (-6 * (i : ℤ) - 2) = ι (l[i]).1.1 ∧ mem (-6 * (i : ℤ) - 3) = (l[i]).1.2 ∧
      mem (-6 * (i : ℤ) - 4) = ι (l[i]).2.1 ∧ mem (-6 * (i : ℤ) - 5) = (l[i]).2.2 ∧
      ListsPoints ι mem (mem (-6 * (i : ℤ) - 6)) (ball d (l[i]).1.1 ((2 : ℝ) ^ (l[i]).1.2)) ∧
      ListsPoints ι mem (mem (-6 * (i : ℤ) - 7)) (ball d (l[i]).2.1 ((2 : ℝ) ^ (l[i]).2.2))

end DoublingMST


