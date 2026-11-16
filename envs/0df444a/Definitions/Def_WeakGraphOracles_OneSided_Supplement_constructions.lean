-- Prove2me | Definitions.Def_WeakGraphOracles_OneSided_Supplement_constructions
-- name    : WeakGraphOracles_OneSided_Supplement_constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:50.635045+00:00
-- url     : https://prove2.me/theorems/5f77b5a5-8889-41e7-91e0-f8f76be33441
-- title:
--   Blow-ups $H(t)$, high-girth comparison graphs and the constructions of Sections 7.5–7.6
-- statement:
--   These are the graphs of the lower-bound constructions of Sections 7.5 and 7.6, for a pattern $H$ on $k=|V(H)|$ vertices and an input size $n$.
--
--   The degree parameter is $t=\lfloor n^{1/(2k+2)}\rfloor$. A comparison graph is a $t$-regular graph $R$ (every vertex has exactly $t$ neighbours) of girth larger than $k$ (every cycle has more than $k$ edges) on $r$ vertices with $0<r\le 4k\,t^k$, the order supplied by the cited Fact 5.1.
--
--   The blow-up $H(t)$ replaces each vertex $a$ of $H$ by a class of $t$ vertices and joins $(a,i)$ to $(b,j)$ exactly when $ab$ is an edge of $H$. In Case A, $n_1$ is the largest multiple of $ktr$ that is at most $n$; $G_{far}$ consists of $n_1/(kt)$ disjoint copies of $H(t)$ and $n-n_1$ isolated vertices, and $G_{free}$ of $n_1/r$ disjoint copies of $R$ and the same number of isolated vertices. In Case B, $n_1=r\lfloor n/r\rfloor$ and $G_{far}$ consists of $\lfloor n/r\rfloor$ disjoint copies of $R$ and $n-n_1<r$ isolated vertices; the free graph there is the complete graph $K_n$. The copies occupy the labels $0,\dots,n_1-1$ in consecutive blocks; any fixed placement serves, because the lower bounds use uniformly random relabelings.
--
--   For a set $C$ of induced embeddings of $H$ into $G$, the pair load $c(x,y)$ is the number of members of $C$ whose image contains both $x$ and $y$, and $c_{\max}=\max_{x\ne y}c(x,y)$. The constant of Lemma 7.4 is $c=2^{-k}k^{-4}$.
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 10 (PDF p. 11), Fact 5.1; p. 18 (PDF p. 19), §7.5 (parameters, blow-up, the two distributions); pp. 19–20 (PDF pp. 20–21), §7.6, Lemma 7.3, Cases A and B, Lemma 7.4

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_graphs

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- `t = ⌊n^{1/(2k+2)}⌋`, the degree parameter of Sections 7.5–7.6. -/
noncomputable def sectionT (k n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) + 2))⌋₊

/-- Every vertex of `R` has exactly `t` neighbours. -/
def IsRegularDeg {r : ℕ} (R : SimpleGraph (Fin r)) (t : ℕ) : Prop :=
  ∀ v : Fin r, (R.neighborSet v).ncard = t

/-- Every cycle of `R` has length larger than `g` (girth `> g`). -/
def GirthGt {r : ℕ} (R : SimpleGraph (Fin r)) (g : ℕ) : Prop :=
  ∀ (v : Fin r) (p : R.Walk v v), p.IsCycle → g < p.length

/-- The comparison graph `R = R_{t,k}` of Sections 7.5–7.6: `t`-regular, girth
larger than `k`, on `0 < r ≤ 4k t^k` vertices (the order supplied by Fact 5.1;
the graph Fact 5.1 provides is nonempty). -/
def ComparisonGraph (k t : ℕ) {r : ℕ} (R : SimpleGraph (Fin r)) : Prop :=
  0 < r ∧ IsRegularDeg R t ∧ GirthGt R k ∧ r ≤ 4 * k * t ^ k

/-- Disjoint copies of the blow-up `H(t)` on the labels `0, …, n₁-1`, the
remaining labels isolated. Label `x < n₁` lies in copy `x / (k t)` and in the
class of `a = (x mod k t) / t ∈ V(H)`; two labels are adjacent iff they lie in
the same copy and their classes are adjacent in `H` (complete bipartite
adjacency exactly on `H`-edges). Here `k = |V(H)|`. -/
def blowUpUnion (H : Pattern) (t n₁ n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y =>
    x.val < n₁ ∧ y.val < n₁ ∧ x.val / (H.order * t) = y.val / (H.order * t) ∧
      ∃ a b : Fin H.order, a.val = x.val % (H.order * t) / t ∧
        b.val = y.val % (H.order * t) / t ∧ H.graph.Adj a b

/-- Disjoint copies of `R` on the labels `0, …, n₁-1` (copy `x / r`, vertex
`x mod r`), the remaining labels isolated. -/
def copiesUnion {r : ℕ} (R : SimpleGraph (Fin r)) (n₁ n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y =>
    x.val < n₁ ∧ y.val < n₁ ∧ x.val / r = y.val / r ∧
      ∃ a b : Fin r, a.val = x.val % r ∧ b.val = y.val % r ∧ R.Adj a b

/-- Case A: `n₁` is the largest multiple of `k t r` with `n₁ ≤ n`. -/
def caseAN1 (k t r n : ℕ) : ℕ := n / (k * t * r) * (k * t * r)

/-- Case B: `n₁ = r ⌊n / r⌋`. -/
def caseBN1 (r n : ℕ) : ℕ := n / r * r

/-- Sections 7.5 and 7.6, Case A: `G_far`, `n₁/(kt)` disjoint copies of `H(t)`
and `n − n₁` isolated vertices, with `t = ⌊n^{1/(2k+2)}⌋`, `k = |V(H)|`. -/
noncomputable def caseAFar (H : Pattern) (n r : ℕ) : SimpleGraph (Fin n) :=
  blowUpUnion H (sectionT H.order n) (caseAN1 H.order (sectionT H.order n) r n) n

/-- Sections 7.5 and 7.6, Case A: `G_free`, `n₁/r` disjoint copies of `R` and the
same `n − n₁` isolated vertices. -/
noncomputable def caseAFree (H : Pattern) (n : ℕ) {r : ℕ} (R : SimpleGraph (Fin r)) :
    SimpleGraph (Fin n) :=
  copiesUnion R (caseAN1 H.order (sectionT H.order n) r n) n

/-- Section 7.6, Case B: `G_far`, `⌊n/r⌋` disjoint copies of `R` and
`n − r⌊n/r⌋ < r` isolated vertices. (`G_free` is the complete graph `K_n`.) -/
def caseBFar (n : ℕ) {r : ℕ} (R : SimpleGraph (Fin r)) : SimpleGraph (Fin n) :=
  copiesUnion R (caseBN1 r n) n

/-- `c(x,y)`: the number of induced embeddings in `C` whose image contains both
`x` and `y`. -/
noncomputable def pairLoad {H : Pattern} {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : Finset (H.graph ↪g G)) (x y : Fin n) : ℕ := by
  classical
  exact (C.filter fun φ : H.graph ↪g G => (∃ a, φ a = x) ∧ ∃ b, φ b = y).card

/-- `c_max = max_{x ≠ y} c(x,y)` (zero when there is no pair `x ≠ y`). -/
noncomputable def maxPairLoad {H : Pattern} {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : Finset (H.graph ↪g G)) : ℕ :=
  (Finset.univ : Finset (Fin n)).offDiag.sup fun p => pairLoad C p.1 p.2

/-- The constant `c = 2^{-k} k^{-4}` of Lemma 7.4. -/
noncomputable def inducedConst (k : ℕ) : ℝ := 1 / ((2 : ℝ) ^ k * (k : ℝ) ^ 4)

end WeakGraphOracles.OneSided.Supplement


