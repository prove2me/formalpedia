-- Prove2me | Definitions.Def_AdaptiveRefresh_Main_Graph
-- name    : AdaptiveRefresh_Main_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:00:29.99123+00:00
-- url     : https://prove2.me/theorems/166ca39a-1110-4580-b56d-546a4160c8a3
-- title:
--   Identified weighted multigraphs, Laplacians and spectral approximation
-- statement:
--   Let $V=\{0,\ldots,n-1\}$. A graph is a finite list of edge records, each with a distinct natural identity, two different vertices, and a positive real weight. Identities retain parallel edges separately. Output edges may have nonnegative reweights and must match live input identities and endpoints. The number of stored identities is the output size. Parallel weights are aggregated only for adjacency and Laplacian matrices:
--
--   $$d_G(u)=\sum_v w_{uv},\qquad A_G=(w_{uv}),\qquad L_G=\operatorname{diag}(d_G)-A_G.$$
--
--   The relative approximation predicate requires symmetry and both quadratic inequalities for every real vector. Matrix norms are the Euclidean operator norm. A conductance lower bound is expressed over all nonempty proper cuts, and the initial maximum degree is the maximum of the vertex degrees and zero. On an empty vertex set it is zero. The polynomial weight promise is only $w_e\le\max(2,n)^b$; it has no lower weight or ratio constraint.
--
--   This adapter reuses the published weighted-graph matrix definitions and exact relative approximation predicate. It supplies edge identities and support, which those predicates alone do not record.
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), §1 Eq. (1), printed p. 1 (PDF p. 2); §3 and Property 3.1, printed p. 5 (PDF p. 6). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph

set_option autoImplicit false

namespace AdaptiveRefresh.Main

/-- An edge record; identities distinguish parallel edges. Validity is imposed on graphs. -/
structure Edge where
  id : ℕ
  u : ℕ
  v : ℕ
  weight : ℝ

abbrev Graph := List Edge

/-- A loopless weighted multigraph on the labelled vertex set `Fin n`. -/
def ValidGraph (n : ℕ) (G : Graph) : Prop :=
  (G.map Edge.id).Nodup ∧ ∀ e ∈ G, e.u < n ∧ e.v < n ∧ e.u ≠ e.v ∧ 0 < e.weight

/-- Polynomial upper weight promise, with no lower weight or ratio promise. -/
def WeightBound (b n : ℕ) (G : Graph) : Prop :=
  ∀ e ∈ G, e.weight ≤ (max 2 n : ℕ) ^ b

/-- Aggregate parallel identities only at the matrix interface. -/
noncomputable def pairWeights (n : ℕ) (G : Graph) : Fin n → Fin n → ℝ :=
  fun u v => (G.map fun e =>
    if (e.u = u.val ∧ e.v = v.val) ∨ (e.v = u.val ∧ e.u = v.val)
    then e.weight else 0).sum

noncomputable def laplacian (n : ℕ) (G : Graph) : Matrix (Fin n) (Fin n) ℝ :=
  SpectralSparsify.Sampling.lapMat (pairWeights n G)

noncomputable def adjacency (n : ℕ) (G : Graph) : Matrix (Fin n) (Fin n) ℝ :=
  SpectralSparsify.Sampling.adjMat (pairWeights n G)

noncomputable def degree (n : ℕ) (G : Graph) (u : Fin n) : ℝ :=
  SpectralSparsify.Sampling.wDegree (pairWeights n G) u

noncomputable def slotWeights (n : ℕ) (G : Graph)
    (e : WeightedSpectralSketch.LowerBound.EdgeSlot (Fin n)) : ℝ :=
  Sym2.lift ⟨fun u v => pairWeights n G u v,
    by intro u v; simp only [pairWeights]; congr 1; apply List.map_congr_left
       intro a ha; congr 1; aesop⟩ e.val

/-- Support, nonnegative reweighting and distinct output edge identities are separate from accuracy. -/
def ReweightedSubgraph (n : ℕ) (G H : Graph) : Prop :=
  (H.map Edge.id).Nodup ∧ ∀ e ∈ H,
    e.u < n ∧ e.v < n ∧ e.u ≠ e.v ∧ 0 ≤ e.weight ∧
    ∃ f ∈ G, e.id = f.id ∧
      ((e.u = f.u ∧ e.v = f.v) ∨ (e.u = f.v ∧ e.v = f.u))

/-- Both exact `(1 ± ε)` quadratic inequalities, using the audited published predicate. -/
noncomputable def SpectralApprox (n : ℕ) (ε : ℝ) (G H : Graph) : Prop :=
  WeightedSpectralSketch.LowerBound.IsSpectralApprox ε (slotWeights n G) (laplacian n H)

/-- Euclidean operator norm, via the continuous linear map on Euclidean space. -/
noncomputable def opNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM.toFun A‖

/-- Quadratic-form Loewner order; no entrywise order is used. -/
def Loewner {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ x : Fin d → ℝ, (∑ u, ∑ v, x u * A u v * x v) ≤
    ∑ u, ∑ v, x u * B u v * x v

/-- Conductance lower bound, stated over every nonempty proper cut. -/
noncomputable def Expander (n : ℕ) (φ : ℝ) (G : Graph) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    φ * min (∑ u ∈ S, degree n G u) (∑ u ∈ Sᶜ, degree n G u) ≤
      ∑ u ∈ S, ∑ v ∈ Sᶜ, pairWeights n G u v

noncomputable def initialMaxDegree (n : ℕ) (G : Graph) : ℝ :=
  (List.ofFn (degree n G)).foldl max 0

end AdaptiveRefresh.Main


