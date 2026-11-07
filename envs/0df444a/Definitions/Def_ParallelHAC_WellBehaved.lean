-- Prove2me | Definitions.Def_ParallelHAC_WellBehaved
-- name    : ParallelHAC_WellBehaved
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:33.327197+00:00
-- url     : https://prove2.me/theorems/209da341-4acd-4840-8307-958f2db3bb1b
-- title:
--   Well-behaved linkage function (Definitions 1–6)
-- statement:
--   Let $P$ be a finite set of $n=|P|$ points and let $d$ assign a real number $d(A,B)$ to every pair of clusters (subsets) $A,B$ of $P$; write $d(u,v):=d(\{u\},\{v\})$. Fix a dimension parameter $k$ and constants $\kappa,a,c_\Delta,b$. The linkage $d$ is **well-behaved** on $P$ when, for all nonempty clusters $A,B,C\subseteq P$:
--
--   1. **Linkage.** $d(A,B)\ge 0$ and $d(A,B)=d(B,A)$.
--   2. **$\alpha$-packability** (Definition 1) with $\alpha=a(\log_2 n+1)^a$. For every $r>0$ and every family $\mathcal C$ of pairwise disjoint nonempty clusters with $d(B,C)\ge r$ for all distinct $B,C\in\mathcal C$, every centre $A$ and every radius $R\ge r$,
--   $$\bigl|\{C\in\mathcal C : d(A,C)\le R,\ |C|\le|A|\}\bigr|\le \alpha\Bigl(1+\frac Rr\Bigr)^{\kappa k}.$$
--   3. **Approximate triangle inequality** (Definition 2). If $|B|\ge\min(|A|,|C|)$ then $d(A,C)\le c_\Delta\,(d(A,B)+d(B,C))$.
--   4. **Weight-stability** (Definition 3). If $A\cap B=\emptyset$ then $d(A\cup B,A)\le \frac{|B|}{|A|+|B|}\,d(A,B)$.
--   5. **Average-reducibility** (Definition 4). If $A\cap B=\emptyset$ and $|C|\ge|A|+|B|$ then
--   $$d(A\cup B,C)\ge\frac{d(A,C)+d(B,C)}2-d(A,B).$$
--   6. **Poly-bounded diameter** (Definition 5). If $\Delta\ge d(u,v)$ for all $u,v\in P$, then $d(A,B)\le \Delta\cdot b\,n^{b}$ for disjoint $A,B$.
--
--   These are the properties of Euclidean distance (packing, triangle inequality) and the stability properties under merges that the dendrogram height bound needs; centroid and Ward's linkage satisfy them (Theorems 1–2 of the paper).
--
--   **Formalization Note** The point set is a finite set in an arbitrary type (the paper's $\mathbb R^k$ is one instance; the dimension enters only through the packing exponent $\kappa k$). The paper requires the axioms for all subsets of $\mathbb R^k$; here they are required only for nonempty subsets of $P$, and packing only for pairwise disjoint families — weaker hypotheses. The paper's $\alpha=\tilde O(1)$, $O(k)$ and $\mathrm{poly}(|P|)$ are pinned by the constants $a$, $\kappa$, $b$. The maximum $\Delta=\max_{u,v\in P}d(u,v)$ is encoded by quantifying over its upper bounds.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §1 p.1 (PDF p.4); §2.1 Definitions 1–6, pp.5–6 (PDF pp.8–9)

import Mathlib

namespace ParallelHAC

/-!
# Well-behaved linkage functions (Definitions 1–6)

Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, *Parallel Hierarchical
Agglomerative Clustering in Low Dimensions*, arXiv:2507.20047 (sha256 a21061c8…),
§1 p.1 (the linkage function), §2.1 pp.5–6, Definitions 1–6.

**Formalization Note.**
* The point type `V` is abstract: Definitions 1–5 never use coordinates, and the paper uses low
  dimension only through the packing bound of Definition 1 (p.5). The paper's setting is the
  instance `V = EuclideanSpace ℝ (Fin k)`; here `k` is the dimension parameter of the packing
  bound.
* A linkage function is `d : Finset V → Finset V → ℝ`. All axioms are imposed only on nonempty
  subsets of the point set `P` being clustered (HAC only ever evaluates `d` there); this is a
  weaker hypothesis than the paper's "for every `A, B, C ⊆ ℝ^k`".
* Definition 1's `α = Õ(1)` is pinned as `α = a · (log₂ n + 1)^a` with `n = |P|`, and its
  exponent `O(k)` as `κ · k`. The packed families are restricted to pairwise disjoint families of
  nonempty subsets of `P` (again a weaker hypothesis; the only family the paper packs is part of
  a clustering, Lemma 16).
* Definition 2's constant is `cΔ`; Definition 5's `poly(|P|)` is pinned as `b · |P|^b`, and
  `∆ = max_{u,v∈P} d(u,v)` is encoded by quantifying over every upper bound `Δ` of the
  singleton distances `d({u},{v})`, `u, v ∈ P` (equivalent, since the maximum is one of them).
-/

/-- A linkage function `d` is **well-behaved** on the point set `P` (Definition 6, p.6) with
dimension parameter `k`, packing constants `κ, a`, triangle constant `cΔ` and diameter constant
`b`: it is a symmetric nonnegative linkage (p.1), `α`-packable with `α = a(log₂ |P| + 1)^a` and
exponent `κ k` (Definition 1, p.5), approximately satisfies the triangle inequality with constant
`cΔ` (Definition 2, p.5), is weight-stable (Definition 3, p.6), average-reducible (Definition 4,
p.6) and has poly-bounded diameter with polynomial `b |P|^b` (Definition 5, p.6).
Source: arXiv:2507.20047 (sha256 a21061c8…), pp.1, 5–6.

**Formalization Note.** Every condition is required only for nonempty subsets of `P`. -/
structure WellBehaved {V : Type*} [DecidableEq V] (P : Finset V) (k : ℕ) (κ a cΔ b : ℝ)
    (d : Finset V → Finset V → ℝ) : Prop where
  /-- `d` takes values in `ℝ_{≥0}` (p.1). -/
  nonneg : ∀ A B : Finset V, A.Nonempty → A ⊆ P → B.Nonempty → B ⊆ P → 0 ≤ d A B
  /-- `d` is symmetric (p.1). -/
  symm : ∀ A B : Finset V, A.Nonempty → A ⊆ P → B.Nonempty → B ⊆ P → d A B = d B A
  /-- Definition 1 (α-packability), with `α = a (log₂ |P| + 1)^a` and `O(k) = κ k`: for every
  `r > 0` and every family `𝒞` whose distinct members are at linkage distance `≥ r`, every centre
  `A` and every radius `R ≥ r`, the members `C ∈ 𝒞` with `d(A, C) ≤ R` and `|C| ≤ |A|` number at
  most `α (1 + R/r)^{κ k}`. -/
  packable : ∀ r : ℝ, 0 < r → ∀ 𝒞 : Finset (Finset V),
    (∀ C ∈ 𝒞, C.Nonempty ∧ C ⊆ P) → (𝒞 : Set (Finset V)).PairwiseDisjoint id →
    (∀ B ∈ 𝒞, ∀ C ∈ 𝒞, B ≠ C → r ≤ d B C) →
    ∀ A : Finset V, A.Nonempty → A ⊆ P → ∀ R : ℝ, r ≤ R →
      ((𝒞.filter (fun C => d A C ≤ R ∧ C.card ≤ A.card)).card : ℝ) ≤
        a * (Real.logb 2 P.card + 1) ^ a * (1 + R / r) ^ (κ * k)
  /-- Definition 2 (approximate triangle inequality): `d(A, C) ≤ cΔ (d(A, B) + d(B, C))`
  whenever `|B| ≥ min(|A|, |C|)`; the sets need not be disjoint. -/
  approxTriangle : ∀ A B C : Finset V, A.Nonempty → A ⊆ P → B.Nonempty → B ⊆ P →
    C.Nonempty → C ⊆ P → min A.card C.card ≤ B.card → d A C ≤ cΔ * (d A B + d B C)
  /-- Definition 3 (weight-stability): for disjoint `A, B`,
  `d(A ∪ B, A) ≤ |B| / (|A| + |B|) · d(A, B)`. -/
  weightStable : ∀ A B : Finset V, A.Nonempty → A ⊆ P → B.Nonempty → B ⊆ P → Disjoint A B →
    d (A ∪ B) A ≤ (B.card : ℝ) / ((A.card : ℝ) + B.card) * d A B
  /-- Definition 4 (average-reducibility): for disjoint `A, B` and any `C` with
  `|C| ≥ |A| + |B|`, `d(A ∪ B, C) ≥ (d(A, C) + d(B, C))/2 − d(A, B)`. -/
  avgReducible : ∀ A B C : Finset V, A.Nonempty → A ⊆ P → B.Nonempty → B ⊆ P →
    C.Nonempty → C ⊆ P → Disjoint A B → A.card + B.card ≤ C.card →
    (d A C + d B C) / 2 - d A B ≤ d (A ∪ B) C
  /-- Definition 5 (poly-bounded diameter), with `poly(|P|) = b |P|^b`: if `Δ` bounds every
  singleton distance `d({u}, {v})`, `u, v ∈ P`, then `d(A, B) ≤ Δ · b |P|^b` for disjoint
  `A, B ⊆ P`. -/
  polyDiam : ∀ Δ : ℝ, (∀ u ∈ P, ∀ v ∈ P, d {u} {v} ≤ Δ) →
    ∀ A B : Finset V, A.Nonempty → A ⊆ P → B.Nonempty → B ⊆ P → Disjoint A B →
      d A B ≤ Δ * (b * (P.card : ℝ) ^ b)

end ParallelHAC


