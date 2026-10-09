-- Prove2me | Definitions.Def_TaitTobin_Irregularity_Setting
-- name    : TaitTobin_Irregularity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:21.051452+00:00
-- url     : https://prove2.me/theorems/36c7add4-b14d-4ba4-8ec0-686798c61704
-- title:
--   §4, pp. 13–14 — average degree, maximizers of λ₁ − d among connected graphs, the pineapple PA(p, q)
-- statement:
--   This file fixes the objects of Section 4 of Tait and Tobin. Graphs are finite simple graphs; an $n$-vertex graph has vertex set $\{0,\dots,n-1\}$. For a graph $G$, $\lambda_1(G)$ is the largest eigenvalue of its adjacency matrix (the published spectral radius `specRad`), and $e(G)$ is its number of edges.
--
--   1. **Average degree.** For a graph $G$ on $n$ vertices,
--   $$d(G) = \frac{2e(G)}{n},$$
--   computed as a real number.
--   2. **Maximizers of irregularity.** A graph $G$ on $n$ vertices is a *maximizer of $\lambda_1 - d$* if $G$ is connected and
--   $$\lambda_1(G') - d(G') \le \lambda_1(G) - d(G) \quad\text{for every connected graph } G' \text{ on the same } n \text{ vertices}.$$
--   3. **The pineapple $PA(p,q)$** (Figure 3 of the paper). On the $p+q$ vertices $0,\dots,p+q-1$, the first $p$ vertices $0,\dots,p-1$ form a complete graph $K_p$, and each of the remaining $q$ vertices $p,\dots,p+q-1$ is a pendant vertex joined only to the clique vertex $0$. For $p = 0$ there is no clique vertex and $PA(0,q)$ has no edges; $PA(p,0)$ is the complete graph $K_p$, and $PA(1,q)$, $PA(2,q)$ are stars.
--
--   The quantity $\lambda_1 - d$ is a measure of how far a graph is from regular (it is $0$ exactly for regular graphs). The conjecture of Aouchiche et al. and Theorem 21 of the paper are stated in terms of these objects.
--
--   **Formalization Note** The average degree divides by the number of vertices of the vertex type; on the empty vertex type it is $0$ by Lean's division convention, which never matters since every graph in the mission is connected, hence nonempty. A decidability instance for the pineapple's adjacency is included so that small pineapples can be computed.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, pp. 13–14, §4 (standing setting, p. 13; Figure 3, p. 14)

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad

namespace TaitTobin.Irregularity

open WangKangXue.SpectralTuran

/-- `d(G) = 2e(G)/n`, the average degree of a graph on a finite vertex type (p. 13), computed in
`ℝ`. On the empty vertex type the value is `0` (division by zero); every statement of the mission
is about connected, hence nonempty, graphs. -/
noncomputable def avgDeg {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact 2 * (G.edgeFinset.card : ℝ) / Fintype.card V

/-- `G` is connected and maximizes `λ₁ − d` among all connected graphs on `Fin n` (p. 13). -/
def IsIrregMax {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.Connected ∧ ∀ G' : SimpleGraph (Fin n), G'.Connected →
    specRad G' - avgDeg G' ≤ specRad G - avgDeg G

/-- The pineapple `PA(p, q)` (Figure 3, p. 14) on `p + q` vertices: the vertices `0, …, p - 1`
form a clique `K_p`, and each of the `q` vertices `p, …, p + q - 1` is a pendant vertex adjacent
only to the clique vertex `0`. For `p = 0` there is no clique vertex to attach to, and
`PA(0, q)` has no edges. -/
def pineapple (p q : ℕ) : SimpleGraph (Fin (p + q)) where
  Adj a b := a ≠ b ∧
    (((a : ℕ) < p ∧ (b : ℕ) < p) ∨ (0 < p ∧ (a : ℕ) = 0 ∧ p ≤ (b : ℕ)) ∨
      (0 < p ∧ (b : ℕ) = 0 ∧ p ≤ (a : ℕ)))
  symm := ⟨fun a b h => ⟨Ne.symm h.1, by tauto⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance (p q : ℕ) : DecidableRel (pineapple p q).Adj := fun a b => by
  unfold pineapple
  infer_instance

end TaitTobin.Irregularity


