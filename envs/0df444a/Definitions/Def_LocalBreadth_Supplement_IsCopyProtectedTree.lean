-- Prove2me | Definitions.Def_LocalBreadth_Supplement_IsCopyProtectedTree
-- name    : LocalBreadth_Supplement_IsCopyProtectedTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:22:35.356211+00:00
-- url     : https://prove2.me/theorems/4e0cb1b8-521e-4a91-a0cb-9ce67efa6f51
-- title:
--   Protected trees on accuracy copies
-- statement:
--   For a profile $\alpha$, the **accuracy copy** $(K,k)$, $K\in\mathcal X$, $k\ge1$, carries the quota
--   $$q(K,k)=\big(\alpha(K)-2^{-k}\big)_+ .$$
--   A **protected tree on copies rooted at $(K,k)$** is defined as a $q$-protected tree, except that vertices carry copy labels $(L_v,k_v)$: equal underlying languages are permitted along an edge ($L_w\subseteq L_v$, $a_w>a_v$); a stop at $(L_v,k_v)$ uses the quota $q(L_v,k_v)$; for every copy $(M,n)$ with $M\in\mathcal X$, $n\ge1$ and $P_v\subseteq M\subseteq L_v$, the vertex $v$ has a child labelled $(M,n)$; and an edge whose underlying language does not change exposes no new points in the finite stopping game.
--
--   These trees coordinate all accuracy requirements inside one certificate, which is what exact attainment of a profile needs (Theorem 7.2).
--
--   **Formalization Note** The copy index is a separate function `idx` on vertices. Path feasibility is geometric feasibility on the (possibly non-strict) chain of underlying languages with the copy quotas per level; a level move between equal languages makes nothing new visible, which is the page's last sentence.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §7.5, Definition 7.14, p.67

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_IsProtectedTree

namespace LocalBreadth.Supplement

/-- The quota of the accuracy copy `(L, k)` (§7.5, p.67): `q(L, k) = (α(L) - 2^{-k})_+`. -/
noncomputable def copyQuota {P : Type} (α : Set P → ℝ) (L : Set P) (k : ℕ) : ℝ :=
  max (α L - ((1 : ℝ) / 2) ^ k) 0

/-- A **protected tree on accuracy copies** rooted at `(K, k)`. Kleinberg, Wei, STOC 2027 submission
(manuscript sha256 f924cbfc…), Definition 7.14, p.67: as in Definition 7.5, except that vertices carry
copy labels `(L_v, k_v)` (`k_v ≥ 1`); equal underlying language labels are permitted along an edge;
a stop at `(L_v, k_v)` uses quota `q(L_v, k_v)`; for every copy `(M, n)` with `P_v ⊆ M ⊆ L_v` the vertex
`v` has a child labelled `(M, n)`; and an edge whose underlying language does not change exposes no new
points in the finite stopping game.

**Formalization Note.** `idx v` is the copy index `k_v`. Children satisfy `L_w ⊆ L_v` (non-strict, as
the page permits equal labels) and `a_w > a_v`; the coverage clause ranges over `M ∈ X` with
`P_v ⊆ M ⊆ L_v` (including `M = L_v`) and every `n ≥ 1`. Path feasibility is Definition 7.4 on the
non-strict chain of underlying languages with per-level copy quotas; in the stopping game a level move
between equal languages enlarges the visible set by nothing, which is the page's last sentence. -/
def IsCopyProtectedTree {d : ℕ} (h : ℕ → ℝ) (α : Set (Fin d → ℤ) → ℝ) (X : Set (Set (Fin d → ℤ)))
    (K : Set (Fin d → ℤ)) (k : ℕ) (T : DecoratedTree (Fin d → ℤ)) (idx : List ℕ → ℕ) : Prop :=
  T.lang [] = K ∧ idx [] = k ∧
  (∀ v ∈ T.verts, T.lang v ∈ X ∧ (T.prot v : Set (Fin d → ℤ)) ⊆ T.lang v ∧ 1 ≤ T.cut v ∧
    0 ≤ T.rad v ∧ 1 ≤ idx v) ∧
  (∀ v n, v ++ [n] ∈ T.verts → T.lang (v ++ [n]) ⊆ T.lang v ∧ T.rad v < T.rad (v ++ [n])) ∧
  (∀ v ∈ T.verts, ∀ M ∈ X, ∀ n : ℕ, 1 ≤ n → (T.prot v : Set (Fin d → ℤ)) ⊆ M → M ⊆ T.lang v →
    ∃ m, v ++ [m] ∈ T.verts ∧ T.lang (v ++ [m]) = M ∧ idx (v ++ [m]) = n) ∧
  (∀ v ∈ T.verts, IsGeomFeasible h (fun i => T.lang (v.take i))
    (fun i => copyQuota α (T.lang (v.take i)) (idx (v.take i)))
    (fun i => T.cut (v.take i)) v.length (T.rad v))

end LocalBreadth.Supplement


