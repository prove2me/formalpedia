-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_Hierarchy
-- name    : BootstrapRecolorVerify_MetricGap_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:07.325629+00:00
-- url     : https://prove2.me/theorems/256a40d6-d22d-4cf3-ab8e-9ac5f29e9290
-- title:
--   Part II parameters, labeled lifts, exceptional edges and smooth distances
-- statement:
--   For a sufficiently large positive integer $r$, set $L=2^{r+1}$, $\Delta=L^2$, $\theta=r^{-4}$, $\Lambda=128r\Delta$, $n=\Lambda^{10000L}$, $n_i=n^i$, and $a_j=2^{r+1-j}=L^{1-j/(r+1)}$. Vertices recursively acquire a cloud coordinate. Every old edge is replaced by a labeled bijection, and each cloud contains $\Delta$ independent perfect matchings. Consecutive pairs in a uniform permutation encode a uniform perfect matching, with a constant number of encodings per matching. Edge identities retain every parallel edge.
--
--   At stage $i$, mark inherited exceptional descendants, all edges of simple cycles of at most $10L$ edges, and all edges in connected subgraphs with at most $s_i=n_{i-1}(r\Delta)^{L+1}$ vertices and more than $(1+1/(100L))$ times as many edges. Give a marked edge length $L^2$ and an unmarked level-$j$ edge length $a_j$, always with weight $4/(\Delta a_j)$. Earlier histories remain frozen.
--
--   Let $d_i$ be the extended nonnegative shortest-path distance, and set $\epsilon=3\log r/L$, $D=(1-(1-\epsilon)^L)^{-1}$. The smooth metric is
--
--   $$\rho_i(u,v)=\frac{a_i}{\epsilon}\left(1-(1-\epsilon)^{\min(d_i(u,v)/a_i,L)}\right),\qquad M_i=\frac{a_i}{\epsilon D},\qquad b=\frac{M_1}{2L}.$$
--
--   Ancestor projection extends earlier metrics. Distinct leaf terminals have distance $2L+d_r(u,v)$; a terminal has distance zero from itself. The normalized exceptional increase is the sum of each edge's weighted length increment divided by $|V(G_r)|$.
--
--   This provides concrete graph and distance data shared by all Part II statements. It assumes no embedding or cost conclusion.
--
--   **Formalization Note** A disconnected pair has shortest-path distance $+\infty$; capping precedes conversion to a real number. Integer edge lengths make the real exponent identical to the source's integer exponent. The unbounded distance is converted for the terminal metric only in the sufficiently-large accepted regime, where spectral expansion forces connectivity.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), §3 pp.5–8; §6.1 (7)–(12), §6.2 (13)–(15), p.20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=20; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib

open scoped Classical ENNReal

namespace BootstrapRecolorVerify.MetricGap

/-- Part II parameters, (7)--(8), pp.20--21. All logarithms are natural. -/
def L (r : ℕ) : ℕ := 2 ^ (r + 1)
def delta (r : ℕ) : ℕ := L r ^ 2
def Lambda (r : ℕ) : ℕ := 128 * r * delta r
def baseSize (r : ℕ) : ℕ := Lambda r ^ (10000 * L r)
def cloudSize (r i : ℕ) : ℕ := baseSize r ^ i
noncomputable def theta (r : ℕ) : ℝ := (r : ℝ) ^ (-4 : ℤ)
noncomputable def epsilon (r : ℕ) : ℝ := 3 * Real.log r / L r
noncomputable def distortion (r : ℕ) : ℝ := 1 / (1 - (1 - epsilon r) ^ L r)
/-- `L^(1-ηj) = 2^(r+1-j)` on the stated domain `j ≤ r`. -/
def scale (r j : ℕ) : ℕ := 2 ^ (r + 1 - j)
noncomputable def edgeWeight (r j : ℕ) : ℝ := 4 / (delta r * (scale r j : ℝ))
noncomputable def cap (r i : ℕ) : ℝ := scale r i / (epsilon r * distortion r)
noncomputable def baseBound (r : ℕ) : ℝ := cap r 1 / (2 * L r)
noncomputable def spectralGap (r : ℕ) (C : ℝ) : ℝ := 1 - C / L r
noncomputable def alpha (r : ℕ) : ℝ := 1 / (100 * L r)
def localSize (r i : ℕ) : ℕ := cloudSize r (i - 1) * (r * delta r) ^ (L r + 1)

/-- Vertices carry their successive cloud coordinates (§3, pp.5--6).
Level zero has one vertex; level `i+1` replaces each vertex by a cloud. -/
def Vertex (r : ℕ) : ℕ → Type
  | 0 => Unit
  | i + 1 => Vertex r i × Fin (cloudSize r (i + 1))

instance vertexFintype (r : ℕ) : (i : ℕ) → Fintype (Vertex r i)
  | 0 => inferInstanceAs (Fintype Unit)
  | i + 1 => @instFintypeProd _ _ (vertexFintype r i) inferInstance

/-- Edge identities retain both the matching label and the descendant coordinate.
Internal edges use half as many positions as vertices. No parallel edges are merged. -/
def Edge (r : ℕ) : ℕ → Type
  | 0 => Empty
  | i + 1 => (Edge r i × Fin (cloudSize r (i + 1))) ⊕
      (Vertex r i × Fin (delta r) × Fin (cloudSize r (i + 1) / 2))

instance edgeFintype (r : ℕ) : (i : ℕ) → Fintype (Edge r i)
  | 0 => inferInstanceAs (Fintype Empty)
  | i + 1 => by
      letI := edgeFintype r i
      change Fintype ((_ × _) ⊕ (_ × _ × _))
      infer_instance

/-- A uniform permutation paired in consecutive positions generates a uniform
perfect matching. The constant number `2^(s/2)(s/2)!` of encodings per matching
means that the redundant labels do not change any graph law. Independent
permutations are used for all labels and clouds (§3, p.5; Appendix B.1). -/
abbrev InternalArray (r i : ℕ) :=
  Vertex r i → Fin (delta r) → Equiv.Perm (Fin (cloudSize r (i + 1)))
abbrev LiftArray (r i : ℕ) :=
  Edge r i → Equiv.Perm (Fin (cloudSize r (i + 1)))
abbrev Stage (r i : ℕ) := InternalArray r i × LiftArray r i

/-- The complete matching history. No expansion, embedding, cost or gap conclusion
is a field of this data type. -/
def History (r : ℕ) : ℕ → Type
  | 0 => Unit
  | i + 1 => History r i × Stage r i

noncomputable instance historyFintype (r : ℕ) : (i : ℕ) → Fintype (History r i)
  | 0 => inferInstanceAs (Fintype Unit)
  | i + 1 => by
      letI := historyFintype r i
      change Fintype (_ × _)
      infer_instance

/-- The two positions of one unordered matching edge, for an even cloud size. -/
def evenPosition {s : ℕ} (a : Fin (s / 2)) : Fin s := ⟨2 * a.val, by omega⟩
def oddPosition {s : ℕ} (a : Fin (s / 2)) : Fin s := ⟨2 * a.val + 1, by omega⟩

/-- Incidence of every labeled edge of an expanded random lift (§3, p.5).
The inherited orientation is only an indexing device for undirected sums. -/
def endpoints {r : ℕ} : {i : ℕ} → History r i → Edge r i → Vertex r i × Vertex r i
  | 0, _, e => Empty.elim e
  | _i + 1, H, Sum.inl (e, a) =>
      let uv := endpoints H.1 e
      ((uv.1, a), (uv.2, H.2.2 e a))
  | _i + 1, H, Sum.inr (u, label, a) =>
      let p := H.2.1 u label
      ((u, p (evenPosition a)), (u, p (oddPosition a)))

def edgeLevel {r : ℕ} : {i : ℕ} → Edge r i → ℕ
  | 0, e => Empty.elim e
  | _ + 1, Sum.inl (e, _) => edgeLevel e
  | i + 1, Sum.inr _ => i + 1

/-- Ancestor projection. Proof arguments express the domain of the source's π. -/
def project (r : ℕ) : {i : ℕ} → (j : ℕ) → j ≤ i → Vertex r i → Vertex r j
  | i, j, h, v =>
    if he : j = i then he ▸ v
    else match i with
      | 0 => False.elim (by omega)
      | i + 1 => project r j (by omega) v.1

/-- Earlier graphs are frozen when constructed; later exceptional marks never
modify the history used for an earlier distance (§6.1, p.22). -/
def historyPrefix (r : ℕ) : {i : ℕ} → (j : ℕ) → j ≤ i → History r i → History r j
  | i, j, h, H =>
    if he : j = i then he ▸ H
    else match i with
      | 0 => False.elim (by omega)
      | i + 1 => historyPrefix r j (by omega) H.1

/-- Undirected incidence; the identity `e` is not discarded. -/
def Joins {r i : ℕ} (H : History r i) (e : Edge r i) (u v : Vertex r i) : Prop :=
  (endpoints H e = (u, v)) ∨ (endpoints H e = (v, u))

/-- Simple cycles include two distinct parallel edges; backtracking along the
same edge is excluded by injectivity of `es` (§6.1, p.22). -/
def OnShortCycle {r i : ℕ} (H : History r i) (e : Edge r i) : Prop :=
  ∃ (m : ℕ) (_ : 2 ≤ m), m ≤ 10 * L r ∧
    ∃ (vs : Fin m → Vertex r i) (es : Fin m → Edge r i),
      Function.Injective vs ∧ Function.Injective es ∧
      (∀ a, Joins H (es a) (vs a) (vs ⟨(a.val + 1) % m, Nat.mod_lt _ (by omega)⟩)) ∧
      ∃ a, es a = e

/-- Connected subgraphs with too many edges; multiplicity is counted in `F.card`.
The connectedness is in the selected subgraph, not the ambient graph. -/
def InSmallDenseSubgraph {r i : ℕ} (H : History r i) (e : Edge r i) : Prop :=
  ∃ (S : Finset (Vertex r i)) (F : Finset (Edge r i)),
    e ∈ F ∧ S.card ≤ localSize r i ∧
    (1 + alpha r) * S.card < (F.card : ℝ) ∧
    (∀ f ∈ F, (endpoints H f).1 ∈ S ∧ (endpoints H f).2 ∈ S) ∧
    ∀ u ∈ S, ∀ v ∈ S,
      Relation.ReflTransGen (fun x y => ∃ f ∈ F, Joins H f x y) u v

/-- Inherited exceptions and all newly bad edges, at every level (§6.1, p.22). -/
def Exceptional {r : ℕ} : {i : ℕ} → History r i → Edge r i → Prop
  | 0, _, e => Empty.elim e
  | _ + 1, H, e =>
      (match e with
        | Sum.inl (old, _) => Exceptional H.1 old
        | Sum.inr _ => False) ∨ OnShortCycle H e ∨ InSmallDenseSubgraph H e

noncomputable def edgeLength {r i : ℕ} (H : History r i) (e : Edge r i) : ℕ :=
  if Exceptional H e then L r ^ 2 else scale r (edgeLevel e)

/-- Walk lengths in the labeled multigraph. Empty walks are permitted. -/
inductive PathLength {r i : ℕ} (H : History r i) : Vertex r i → Vertex r i → ℕ → Prop
  | nil (u) : PathLength H u u 0
  | cons {u v z n} (e : Edge r i) : Joins H e u v → PathLength H v z n →
      PathLength H u z (edgeLength H e + n)

/-- Extended nonnegative shortest-path distance: disconnected pairs have distance
∞, not zero. On the accepted hierarchy all clouds, hence all graphs, are connected. -/
noncomputable def graphDistance {r i : ℕ} (H : History r i) (u v : Vertex r i) : ℝ≥0∞ :=
  sInf {x | ∃ n : ℕ, PathLength H u v n ∧ x = (n : ℝ≥0∞)}

/-- Smooth cap (13), p.22. Cap BEFORE conversion to real numbers. Integer walk
lengths make the real exponent identical to the source's integer exponent. -/
noncomputable def rho {r i : ℕ} (H : History r i) (u v : Vertex r i) : ℝ :=
  (scale r i : ℝ) / epsilon r *
    (1 - (1 - epsilon r) ^
      ((min (graphDistance H u v) ((L r * scale r i : ℕ) : ℝ≥0∞)).toReal /
        (scale r i : ℝ)))

/-- Projected earlier smooth metric (§6.2, pp.22--23). -/
noncomputable def projectedRho {r i : ℕ} (H : History r i) (j : ℕ) (h : j ≤ i)
    (u v : Vertex r i) : ℝ :=
  rho (historyPrefix r j h H) (project r j h u) (project r j h v)

/-- Terminal leaves have length L; equal terminals have distance zero (§4, p.8). -/
noncomputable def terminalDistance {r i : ℕ} (H : History r i) (u v : Vertex r i) : ℝ :=
  if u = v then 0 else 2 * L r + (graphDistance H u v).toReal

/-- Normalized exceptional increase over the baseline 2r (Claim 6.3, p.24).
Subtract baseline lengths edge by edge, retaining every parallel edge. -/
noncomputable def excessWeightedLength {r : ℕ} (H : History r r) : ℝ :=
  (Fintype.card (Vertex r r) : ℝ)⁻¹ * ∑ e : Edge r r,
    edgeWeight r (edgeLevel e) * ((edgeLength H e : ℝ) - scale r (edgeLevel e))

end BootstrapRecolorVerify.MetricGap


