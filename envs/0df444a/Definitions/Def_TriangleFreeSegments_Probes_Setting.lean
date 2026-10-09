-- Prove2me | Definitions.Def_TriangleFreeSegments_Probes_Setting
-- name    : TriangleFreeSegments_Probes_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:26.268301+00:00
-- url     : https://prove2.me/theorems/d831f0d0-7dc2-47eb-9a1e-ced9bb4538b1
-- title:
--   §1–§2, pp. 1–3 — segment families, intersection graphs, probes (i)–(iv), diagonals, the sequences s_k and p_k
-- statement:
--   This file fixes the objects of the paper. Throughout, the plane is $\mathbb R^2=\mathbb R\times\mathbb R$ with first coordinate $x$ (horizontal) and second coordinate $y$ (vertical).
--
--   1. **Line segments.** For two points $u,v$ of the plane, $\operatorname{seg}(u,v)=\{(1-t)u+tv : t\in[0,1]\}$ is the closed segment with endpoints $u$ and $v$. A family of segments is an indexed family $(u_i,v_i)_{i\in\iota}$ of endpoint pairs.
--   2. **Intersection graph** (§1, p. 1). For a family $(F_i)_{i\in\iota}$ of plane sets, the intersection graph has vertex set $\iota$, and two distinct indices $i\neq j$ are adjacent exactly when $F_i\cap F_j\neq\emptyset$. Chromatic number, cliques and "triangle-free" (no clique of size $3$) are those of this graph.
--   3. **Rectangles.** An axis-aligned rectangle is $R=[a,c]\times[b,d]$, so $a,c$ bound $x$ and $b,d$ bound $y$; its interior is $(a,c)\times(b,d)$. Positive area ($a<c$, $b<d$) is assumed separately where needed.
--   4. **Probes** (§2, p. 2). Given $R=[a,c]\times[b,d]$ and numbers $a',b',d'$, the rectangle $P=[a',c]\times[b',d']$ shares the line $x=c$ of the right edge of $R$; its left boundary is $\{a'\}\times[b',d']$. For a family $\mathcal S$ of closed segments, $P$ is a **probe for $(\mathcal S,R)$** if
--      - (i) $a<a'<c$ and $b<b'<d'<d$;
--      - (ii) no segment of $\mathcal S$ meets the left boundary of $P$;
--      - (iii) no segment of $\mathcal S$ has an endpoint in the closed rectangle $P$;
--      - (iv) any two distinct segments of $\mathcal S$ that both meet $P$ are disjoint.
--   5. **Diagonal** (p. 3). The diagonal $D_P$ of the probe $P$ is the segment from its bottom-left corner $(a',b')$ to its top-right corner $(c,d')$.
--   6. **The sequences** (p. 3). $s_1=p_1=1$ and, for $i\ge1$,
--   $$
--   s_{i+1}=(p_i+1)s_i+p_i^2,\qquad p_{i+1}=2p_i^2 ,
--   $$
--      so $(s_k)=1,3,13,181,\dots$ and $(p_k)=1,2,8,128,\dots$.
--   7. **Probe system** (the conclusion of Lemma 2 for given data). For $k\in\mathbb N$, a rectangle $R$, a family $\mathcal S=(\sigma_i)_{i<N}$ of segments and a family $(P_j)_{j<M}$ of rectangles of the form above, the probe system property says: every $\sigma_i$ has two distinct endpoints; the $N$ segments are pairwise distinct; every $\sigma_i$ lies in the interior of $R$; the intersection graph of $\mathcal S$ is triangle-free; every $P_j$ is a probe for $(\mathcal S,R)$; the closed rectangles $P_j$ are pairwise disjoint; and for every proper coloring $\phi$ of the intersection graph of $\mathcal S$, with colors in an arbitrary set, there is a $j$ such that $\phi$ takes at least $k$ distinct values on the segments meeting $P_j$.
--
--   These objects are shared by every statement of the mission: Lemma 2, its base case and induction step, the diagonal claim and the family $\tilde{\mathcal S}_k$ are all phrased with them.
--
--   **Formalization Note** Segments are Mathlib's closed `segment ℝ u v` in `ℝ × ℝ`; a family is indexed by a type (by `Fin N` in Lemma 2), and the probe is stored by its three free coordinates $(a',b',d')$, its right edge being $x=c$ by construction. The sequences are 1-based as on the page: `sSeq k` and `pSeq k` are $s_k$ and $p_k$ for $k\ge1$, and their value at $k=0$ is a junk value (equal to the value at $k=1$); every statement assumes $k\ge1$. "Uses at least $k$ colors" is $k\le$ the cardinality (`Set.ncard`) of the image of the set of segments meeting the probe, a finite set. The standing assumption "contained in the interior of $R$" is a separate clause of the probe system (and a separate hypothesis of the diagonal claim), not part of the probe predicate.
-- source:
--   Pawlik et al., Triangle-free intersection graphs of line segments with large chromatic number, arXiv:1209.1595v5, pp. 1–3: §1 (intersection graph, triangle-free, chromatic number, p. 1), §2 (probe conditions (i)–(iv), p. 2; sequences s_i, p_i and diagonal D_Q, p. 3; conclusion of Lemma 2, p. 3)

import Mathlib

namespace TriangleFreeSegments.Probes

/-- The closed line segment with endpoints `e.1` and `e.2` in the plane `ℝ × ℝ`
(first coordinate `x`, second coordinate `y`). -/
def seg (e : (ℝ × ℝ) × (ℝ × ℝ)) : Set (ℝ × ℝ) := segment ℝ e.1 e.2

/-- The intersection graph of an indexed family of plane sets: two distinct indices are
adjacent iff their sets intersect (p. 1). -/
def interGraph {ι : Type} (F : ι → Set (ℝ × ℝ)) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (F i ∩ F j).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Set.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- An axis-aligned rectangle `R = [a, c] × [b, d]`: `x ∈ [a, c]`, `y ∈ [b, d]`
(the page's letter order). Positive area is a separate hypothesis. -/
structure Rect where
  a : ℝ
  c : ℝ
  b : ℝ
  d : ℝ

/-- The interior `(a, c) × (b, d)` of `R`. -/
def Rect.inner (R : Rect) : Set (ℝ × ℝ) := Set.Ioo R.a R.c ×ˢ Set.Ioo R.b R.d

/-- The free coordinates `a′, b′, d′` of a probe `P = [a′, c] × [b′, d′]` of `R`. -/
structure ProbeData where
  a' : ℝ
  b' : ℝ
  d' : ℝ

/-- The closed rectangle `P = [a′, c] × [b′, d′]`; its right edge lies on the line `x = c`
of the right edge of `R`. -/
def probeRect (R : Rect) (P : ProbeData) : Set (ℝ × ℝ) :=
  Set.Icc P.a' R.c ×ˢ Set.Icc P.b' P.d'

/-- The left boundary `{a′} × [b′, d′]` of a probe. -/
def leftEdge (P : ProbeData) : Set (ℝ × ℝ) := {P.a'} ×ˢ Set.Icc P.b' P.d'

/-- Conditions (i)–(iv) of p. 2: `P = [a′, c] × [b′, d′]` is a probe for `(𝒮, R)`, where
`𝒮` is the family of closed segments `seg (e i)`. -/
def IsProbe {ι : Type} (e : ι → (ℝ × ℝ) × (ℝ × ℝ)) (R : Rect) (P : ProbeData) : Prop :=
  -- (i) a < a′ < c and b < b′ < d′ < d
  (R.a < P.a' ∧ P.a' < R.c ∧ R.b < P.b' ∧ P.b' < P.d' ∧ P.d' < R.d) ∧
  -- (ii) no segment meets the left boundary of P
  (∀ i, Disjoint (seg (e i)) (leftEdge P)) ∧
  -- (iii) no segment has an endpoint inside or on the boundary of P
  (∀ i, (e i).1 ∉ probeRect R P ∧ (e i).2 ∉ probeRect R P) ∧
  -- (iv) the segments meeting P are pairwise disjoint
  (∀ i j, i ≠ j → (seg (e i) ∩ probeRect R P).Nonempty →
    (seg (e j) ∩ probeRect R P).Nonempty → Disjoint (seg (e i)) (seg (e j)))

/-- The diagonal `D_P` of the probe `P`: the segment from its bottom-left corner `(a′, b′)`
to its top-right corner `(c, d′)` (p. 3). -/
def diag (R : Rect) (P : ProbeData) : (ℝ × ℝ) × (ℝ × ℝ) := ((P.a', P.b'), (R.c, P.d'))

/-- `sp i = (s_{i+1}, p_{i+1})`: `s₁ = p₁ = 1`, `s_{i+1} = (p_i + 1) s_i + p_i²`,
`p_{i+1} = 2 p_i²` (p. 3). -/
def sp : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | i + 1 => (((sp i).2 + 1) * (sp i).1 + (sp i).2 ^ 2, 2 * (sp i).2 ^ 2)

/-- `s_k`, 1-based as on p. 3 (the value at `k = 0` is a junk value; statements assume `1 ≤ k`). -/
def sSeq (k : ℕ) : ℕ := (sp (k - 1)).1

/-- `p_k`, 1-based as on p. 3 (the value at `k = 0` is a junk value; statements assume `1 ≤ k`). -/
def pSeq (k : ℕ) : ℕ := (sp (k - 1)).2

/-- The conclusion of Lemma 2 for given data: `e` is a triangle-free family of `N` distinct
non-degenerate line segments in the interior of `R`, `pr` is a family of `M` pairwise disjoint
probes for it, and every proper coloring uses at least `k` colors on the segments meeting
some probe. -/
def ProbeSystem (k : ℕ) (R : Rect) {N M : ℕ} (e : Fin N → (ℝ × ℝ) × (ℝ × ℝ))
    (pr : Fin M → ProbeData) : Prop :=
  (∀ i, (e i).1 ≠ (e i).2) ∧
  Function.Injective (fun i => seg (e i)) ∧
  (∀ i, seg (e i) ⊆ R.inner) ∧
  (interGraph (fun i => seg (e i))).CliqueFree 3 ∧
  (∀ j, IsProbe e R (pr j)) ∧
  (Pairwise fun j j' => Disjoint (probeRect R (pr j)) (probeRect R (pr j'))) ∧
  (∀ (α : Type) (φ : Fin N → α),
    (∀ i j, (interGraph (fun i => seg (e i))).Adj i j → φ i ≠ φ j) →
    ∃ j, k ≤ (φ '' {i | (seg (e i) ∩ probeRect R (pr j)).Nonempty}).ncard)

end TriangleFreeSegments.Probes


