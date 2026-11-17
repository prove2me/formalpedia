-- Prove2me | Definitions.Def_ClusterDecomp_Supplement_Gn
-- name    : ClusterDecomp_Supplement_Gn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:58:02.368839+00:00
-- url     : https://prove2.me/theorems/541d6db4-6615-4973-b4b0-d1819745ce0a
-- title:
--   The Appendix B expander graph $G_n$ and its bipartition
-- statement:
--   Fix $d\ge3$ and $h\in(0,1]$. A simple graph $X$ on $n$ vertices satisfies condition (21) when it is $d$-regular and every $A\subseteq V(X)$ has at least
--
--   $$
--   hd\min\{|A|,n-|A|\}
--   $$
--
--   edges from $A$ to its complement. The standing expander-family condition says such a graph exists for arbitrarily large $n$.
--
--   Given two disjoint copies $X_1,X_2$ of $X$, put $m=\lfloor\sqrt n\rfloor$ and add sets $T=\{t_1,\ldots,t_m\}$ and $T'=\{t'_1,\ldots,t'_m\}$. Join every $t_i$ to every $t'_j$, join each $t_i$ to a distinct host $x_i\in X_1$, and each $t'_i$ to a distinct host $y_i\in X_2$. The resulting unweighted loopless graph is $G_n$, with $P_1=V(X_1)\cup T$ and $P_2=V(X_2)\cup T'$. Finally,
--
--   $$
--   c^*=\min\left\{\frac1{d+3},\frac{hd}{2(d+3)}\right\}.
--   $$
--
--   This is Definition B.2 and the constant of Proposition B.5.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), eq. (21), Definition B.2 p.36 (PDF p.38), Proposition B.5 p.37 (PDF p.39)

import Mathlib
import Definitions.Def_ClusterDecomp_WGraph

open Finset

namespace ClusterDecomp.Supplement

/-!
# The expander condition (21), the graph `G_n` and the partition `P_1, P_2` (Definition B.2), and `c*`

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), Appendix B, p.36 (PDF p.38: (21), Definition B.2) and
Proposition B.5, p.37 (PDF p.39: `c*`).

**Formalization Note.**
* `X : SimpleGraph (Fin n)`. `IsDRegular X d`: every vertex has exactly `d` neighbours. `edgeBoundary X A`
  is `e_X(A, V(X) ∖ A)`, the number of edges with one end in `A` and the other outside (counted as ordered
  pairs `(a, b)` with `a ∈ A`, `b ∉ A`, so each such edge once). Both use `Set.ncard`, so they depend on no
  decidability instance.
* `Expands21 X d h` is (21): `e_X(A, V(X) ∖ A) ≥ h·d·min{|A|, n − |A|}` for **all** `A ⊆ V(X)`.
  `ExpanderFamily d h` is the appendix's standing choice of `(d, h)`: for infinitely many `n` (for every `N`
  some `n ≥ N`) there is a `d`-regular `X` on `n` vertices satisfying (21).
* `G_n` has vertex type `GnV n = (Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m)` with `m = ⌊√n⌋ = Nat.sqrt n`:
  `inl (inl a)` is the copy of `a` in `X_1`, `inl (inr i)` is `t_i`, `inr (inl b)` is the copy of `b` in `X_2`,
  `inr (inr j)` is `t′_j`. The hosts are `x, y : Fin m → Fin n` (`x_i ∈ V(X_1)`, `y_i ∈ V(X_2)`); the
  theorem assumes them injective ("distinct vertices"). Edges: `E(X_1)`, `E(X_2)`, all `t_i t′_j`, and
  `t_i x_i`, `t′_i y_i`. `G_n` is the `WGraph` with weight `1` on these pairs and `0` elsewhere (no loops).
* `P1 n = V(X_1) ∪ T` is the image of `inl`, `P2 n = V(X_2) ∪ T′` the image of `inr`.
* `cStar d h = min{1/(d+3), hd/(2(d+3))}`.
-/

open ClusterDecomp

/-- `X` is `d`-regular. -/
def IsDRegular {n : ℕ} (X : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  ∀ v, (X.neighborSet v).ncard = d

/-- `e_X(A, V(X) ∖ A)`, the number of edges of `X` leaving `A`. -/
noncomputable def edgeBoundary {n : ℕ} (X : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ :=
  {p : Fin n × Fin n | p.1 ∈ A ∧ p.2 ∉ A ∧ X.Adj p.1 p.2}.ncard

/-- Condition (21): `e_X(A, V(X) ∖ A) ≥ h·d·min{|A|, n − |A|}` for all `A ⊆ V(X)`. -/
def Expands21 {n : ℕ} (X : SimpleGraph (Fin n)) (d : ℕ) (h : ℝ) : Prop :=
  ∀ A : Finset (Fin n), h * d * (min A.card (n - A.card) : ℕ) ≤ (edgeBoundary X A : ℝ)

/-- The standing assumption of Appendix B on `(d, h)`: for infinitely many `n` there is a `d`-regular graph
on `n` vertices satisfying (21). -/
def ExpanderFamily (d : ℕ) (h : ℝ) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, ∃ X : SimpleGraph (Fin n), IsDRegular X d ∧ Expands21 X d h

/-- The vertex type `V(X_1) ⊔ T ⊔ V(X_2) ⊔ T′` of `G_n`, with `|T| = |T′| = ⌊√n⌋`. -/
abbrev GnV (n : ℕ) : Type := (Fin n ⊕ Fin (Nat.sqrt n)) ⊕ (Fin n ⊕ Fin (Nat.sqrt n))

/-- The adjacency of `G_n` (Definition B.2). -/
def GnAdj {n : ℕ} (X : SimpleGraph (Fin n)) (x y : Fin (Nat.sqrt n) → Fin n) : GnV n → GnV n → Prop
  | .inl (.inl a), .inl (.inl b) => X.Adj a b
  | .inr (.inl a), .inr (.inl b) => X.Adj a b
  | .inl (.inr _), .inr (.inr _) => True
  | .inr (.inr _), .inl (.inr _) => True
  | .inl (.inr i), .inl (.inl a) => a = x i
  | .inl (.inl a), .inl (.inr i) => a = x i
  | .inr (.inr i), .inr (.inl b) => b = y i
  | .inr (.inl b), .inr (.inr i) => b = y i
  | _, _ => False

/-- The adjacency relation of `G_n` is symmetric. -/
theorem GnAdj_symm {n : ℕ} (X : SimpleGraph (Fin n)) (x y : Fin (Nat.sqrt n) → Fin n) (u v : GnV n) :
    GnAdj X x y u v → GnAdj X x y v u := by
  rcases u with (a | i) | (a | i) <;> rcases v with (b | j) | (b | j) <;>
    simp [GnAdj, X.adj_comm]

open Classical in
/-- The unweighted graph `G_n` of Definition B.2, as a `WGraph` with `0/1` weights. -/
noncomputable def Gn {n : ℕ} (X : SimpleGraph (Fin n)) (x y : Fin (Nat.sqrt n) → Fin n) :
    WGraph (GnV n) where
  w u v := if GnAdj X x y u v then 1 else 0
  symm u v := by
    by_cases h : GnAdj X x y u v
    · rw [if_pos h, if_pos (GnAdj_symm X x y u v h)]
    · have h' : ¬ GnAdj X x y v u := fun h' => h (GnAdj_symm X x y v u h')
      rw [if_neg h, if_neg h']
  nonneg u v := by split_ifs <;> norm_num

/-- `P_1 = V(X_1) ∪ T`. -/
def P1 (n : ℕ) : Finset (GnV n) := univ.map Function.Embedding.inl

/-- `P_2 = V(X_2) ∪ T′`. -/
def P2 (n : ℕ) : Finset (GnV n) := univ.map Function.Embedding.inr

/-- `c* = min{1/(d+3), hd/(2(d+3))}` (Proposition B.5). -/
noncomputable def cStar (d : ℕ) (h : ℝ) : ℝ :=
  min (1 / ((d : ℝ) + 3)) (h * d / (2 * ((d : ℝ) + 3)))

end ClusterDecomp.Supplement


