-- Prove2me | Definitions.Def_BinaryThreeLCC_Main_Spectral
-- name    : BinaryThreeLCC_Main_Spectral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:49.479649+00:00
-- url     : https://prove2.me/theorems/204ccbd6-e63d-43ab-9086-3e2b74ccb341
-- title:
--   Multigraph adjacency, normalized spectra, conductance and matrix products
-- statement:
--   Each edge copy contributes to both symmetric adjacency entries; a loop contributes twice on the diagonal, matching undirected degree. Define the normalized Laplacian and conductance by
--
--   $$L_G=I-A_G/d,\qquad \phi(G)=\min_{1\le|S|\le|V|/2}\frac{e_G(S,V\setminus S)}{d|S|}.$$
--
--   The second-smallest eigenvalue is the published Alon–Milman spectral definition, using the Hermitian eigenvalue list with multiplicity. The second-largest eigenvalue of a symmetric matrix A is obtained by negating the second-smallest eigenvalue of -A. They are used for symmetric matrices on at least two vertices. The finite conductance set is nonempty on that domain. The normalization bridge uses the row-stochastic chain $P=A_G/d$ and uniform mass $1/|V|$. Squared Euclidean norm is the sum of coordinate squares, and a reversed list product implements $M_r\cdots M_1$, with empty product $I$.
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Fact 3.6, printed p.9, PDF p.11; Definition 5.4, printed p.14, PDF p.16; Claim 5.6, printed p.15, PDF p.17; Lemma 5.7, printed p.18, PDF p.20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Graphs
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_mm_basic

set_option autoImplicit false

namespace BinaryThreeLCC.Main

open ContPatrol

/-- Adjacency counts each edge in both directions, and a loop twice on the diagonal. -/
noncomputable def adjacency {V E : Type} [Fintype E] (G : Multigraph V E) : Matrix V V ℝ := by
  classical
  exact fun u v => ∑ e : E,
    ((if G.src e = v ∧ G.tgt e = u then 1 else 0) +
     (if G.src e = u ∧ G.tgt e = v then 1 else 0))

noncomputable def normalizedLaplacian {V E : Type} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (d : ℝ) : Matrix V V ℝ := 1 - d⁻¹ • adjacency G

/-- Published second-smallest eigenvalue, with multiplicity, of a symmetric real matrix.
It returns zero outside the symmetric domain or with fewer than two rows. -/
noncomputable abbrev secondSmallest {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : ℝ := AlonMilman.PropertyT.lambda1 A

/-- Negation reverses the eigenvalue order, preserving every multiplicity. -/
noncomputable def secondLargest {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : ℝ := -AlonMilman.PropertyT.lambda1 (-A)

noncomputable def undirectedCut {V E : Type} [Fintype E]
    (G : Multigraph V E) (S : Finset V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e =>
    (G.src e ∈ S ∧ G.tgt e ∉ S) ∨ (G.tgt e ∈ S ∧ G.src e ∉ S))).card

noncomputable def conductance {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (d : ℝ) : ℝ := by
  classical
  exact sInf {x : ℝ | ∃ S : Finset V, 1 ≤ S.card ∧ 2 * S.card ≤ Fintype.card V ∧
    x = (undirectedCut G S : ℝ) / (d * S.card)}

/-- Row convention for the normalized Markov chain, used in the Cheeger bridge. -/
noncomputable def normalizedChain {V E : Type} [Fintype E]
    (G : Multigraph V E) (d : ℝ) : Matrix V V ℝ := d⁻¹ • adjacency G

noncomputable abbrev uniformMass {V : Type} [Fintype V] : V → ℝ :=
  MarkovMixing.uniformDist V

noncomputable def squaredNorm {V : Type} [Fintype V] (x : V → ℝ) : ℝ := ∑ v, x v ^ 2

noncomputable def matrixProduct {V : Type} [Fintype V] [DecidableEq V]
    {r : ℕ} (A : Fin r → Matrix V V ℝ) : Matrix V V ℝ := (List.ofFn A).reverse.prod

noncomputable def unitVector {V : Type} [DecidableEq V] (v : V) : V → ℝ := Pi.single v 1

end BinaryThreeLCC.Main


