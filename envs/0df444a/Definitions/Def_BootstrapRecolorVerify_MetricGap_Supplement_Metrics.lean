-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Metrics
-- name    : BootstrapRecolorVerify_MetricGap_Supplement_Metrics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:29:33.747978+00:00
-- url     : https://prove2.me/theorems/c3479253-7a65-4024-acf3-5c752a798315
-- title:
--   Part I real lengths, hard caps and deterministic good event
-- statement:
--   In a raw Part I hierarchy, give a level-$j$ edge weight $L^{-(1-\eta j)}$ and length $L^{1-\eta j}$ unless exceptional, in which case its length is $L^2$. Let $d_i$ be the shortest-path distance with these lengths; before restricting to connected histories, disconnected pairs have distance $+\infty$. Define
--
--   $$\rho_i(u,v)=\min\{d_i(u,v),L^{2-\eta i}\}.$$
--
--   Earlier capped metrics are extended to later vertices by ancestor projection. The terminal leaves attached at length $L$ have distance zero when equal and $2L+d_i(u,v)$ when distinct.
--
--   The cloud-connectedness event requires every internal cloud graph at every stage to be connected. The separate deterministic good event consists exactly of cloud expansion and local sparsity: each internal 3-regular cloud has normalized Laplacian second eigenvalue at least $1/45$, and every induced vertex set $S\subseteq V(G_i)$ with $|S|\le N_{i-1}n$ has at most $(1+\alpha)|S|$ edges, counting parallel edges separately. In particular, no embedding, radius inequality, proxy-cost estimate or gap is part of this event.
--
--   These are the metric and graph properties used by the deterministic companion theorem and its supporting lemma.
--
--   **Formalization Note** Distances are extended nonnegative infima of actual undirected walk lengths. The hard cap is applied before conversion to a real number. Expansion is encoded by the equivalent mean-zero quadratic inequality $\sum_{uv\in E(U)}(f(u)-f(v))^2\ge(3/45)\sum_{u\in U}f(u)^2$; edges are unordered and counted once. The induced-set sparsity condition is equivalent to sparsity for all subgraphs of the indicated size.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), §3 p.6; §4 capped metric and Claims 4.2/4.5 pp.8–10, p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=8; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Hierarchy

open scoped Classical ENNReal

namespace BootstrapRecolorVerify.MetricGap.Supplement

/-- Weighted shortest-path distance on the published undirected multigraph walk
interface. Empty walks are admitted; no walk gives +∞, never a default real zero. -/
noncomputable def weightedDistance {V E : Type*} (inc : E → Sym2 V)
    (len : E → ℝ≥0∞) (u v : V) : ℝ≥0∞ :=
  sInf {x | ∃ es : List E, PoSUndirected.IsWalk inc u v es ∧ x = (es.map len).sum}

noncomputable def edgeWeight (r n j : ℕ) : ℝ :=
  1 / Real.rpow (lengthScale r n) (1 - eta r * j)

/-- All Part I lengths are real (§3 p.6). -/
noncomputable def edgeLength {n i : ℕ} (r : ℕ) (H : History n i) (e : Edge n i) : ℝ :=
  if Exceptional r H e then lengthScale r n ^ 2
  else Real.rpow (lengthScale r n) (1 - eta r * edgeLevel e)

noncomputable def graphDistance {n i : ℕ} (r : ℕ) (H : History n i)
    (u v : Vertex n i) : ℝ≥0∞ :=
  weightedDistance (ends H) (fun e => ENNReal.ofReal (edgeLength r H e)) u v

/-- Hard cap, with conversion to real AFTER the cap, including on disconnected
raw histories. There is no rounding of L or of any real power. -/
noncomputable def rho {n i : ℕ} (r : ℕ) (H : History n i) (u v : Vertex n i) : ℝ :=
  (min (graphDistance r H u v)
    (ENNReal.ofReal (Real.rpow (lengthScale r n) (2 - eta r * i)))).toReal

noncomputable def projectedRho {n i : ℕ} (r : ℕ) (H : History n i)
    (j : ℕ) (h : j ≤ i) (u v : Vertex n i) : ℝ :=
  rho r (historyPrefix n j h H) (project n j h u) (project n j h v)

/-- Terminal leaves have length L; distances between different components remain
infinite until the connected-instance interface is used. Equal leaves cost zero. -/
noncomputable def terminalDistance {n i : ℕ} (r : ℕ) (H : History n i)
    (u v : Vertex n i) : ℝ≥0∞ :=
  if u = v then 0 else ENNReal.ofReal (2 * lengthScale r n) + graphDistance r H u v

/-- The three internal matching labels, each undirected edge once. -/
def internalPair {n i : ℕ} (A : InternalArray n i) (u : Vertex n i)
    (e : Fin 3 × Fin (cloudSize n (i + 1) / 2)) :
    Fin (cloudSize n (i + 1)) × Fin (cloudSize n (i + 1)) :=
  (A u e.1 (evenPosition e.2), A u e.1 (oddPosition e.2))

def internalEnds {n i : ℕ} (A : InternalArray n i) (u : Vertex n i)
    (e : Fin 3 × Fin (cloudSize n (i + 1) / 2)) : Sym2 (Fin (cloudSize n (i + 1))) :=
  s((internalPair A u e).1, (internalPair A u e).2)

/-- The connectedness event on which §3 p.6 defines its finite instance. This is
an event under the raw law, not a conditioning or a rejection rule. -/
def AllCloudsConnected {n r : ℕ} (H : History n r) : Prop :=
  ∀ k : ℕ, ∀ h : k + 1 ≤ r, ∀ u : Vertex n k,
    ∀ a b : Fin (cloudSize n (k + 1)),
      ∃ es, PoSUndirected.IsWalk (internalEnds (historyPrefix n (k + 1) h H).2.1 u) a b es

/-- Claim 4.2, λ₂(I−A/3) ≥ 1/45, in its equivalent mean-zero Rayleigh form.
Only the internal cloud edges occur in the quadratic form, with multiplicity.
For a 3-regular cloud, ∑edges(f(u)−f(v))² / 3 is the normalized Laplacian form. -/
def CloudExpansion {n r : ℕ} (H : History n r) : Prop :=
  ∀ k : ℕ, ∀ h : k + 1 ≤ r, ∀ u : Vertex n k,
    ∀ f : Fin (cloudSize n (k + 1)) → ℝ, (∑ a, f a) = 0 →
      (3 / 45 : ℝ) * ∑ a, (f a) ^ 2 ≤
        ∑ e : Fin 3 × Fin (cloudSize n (k + 1) / 2),
          (f (internalPair (historyPrefix n (k + 1) h H).2.1 u e).1 -
           f (internalPair (historyPrefix n (k + 1) h H).2.1 u e).2) ^ 2

/-- Claim 4.5 / Definition 4.4: all induced small vertex sets have at most
(1+α)|S| internal edges. This is equivalent to requiring sparsity of every
subgraph on at most N_(i−1)n vertices, since edge deletion cannot increase a count. -/
def LocalSparsity {n r : ℕ} (H : History n r) : Prop :=
  ∀ k : ℕ, ∀ h : k + 1 ≤ r, ∀ S : Finset (Vertex n (k + 1)),
    S.card ≤ Fintype.card (Vertex n k) * n →
      ((Finset.univ.filter fun e : Edge n (k + 1) =>
        (endpoints (historyPrefix n (k + 1) h H) e).1 ∈ S ∧
        (endpoints (historyPrefix n (k + 1) h H) e).2 ∈ S).card : ℝ) ≤
          (1 + sparsityAlpha r n) * S.card

/-- Exactly §4's two standing properties; no metric embedding, center estimate,
proxy bound or gap assertion is assumed. -/
def GoodHistory {n r : ℕ} (H : History n r) : Prop :=
  CloudExpansion H ∧ LocalSparsity H

end BootstrapRecolorVerify.MetricGap.Supplement


