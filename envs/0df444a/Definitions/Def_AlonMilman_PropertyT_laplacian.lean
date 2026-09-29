-- Prove2me | Definitions.Def_AlonMilman_PropertyT_laplacian
-- name    : AlonMilman_PropertyT_laplacian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:29:45.237315+00:00
-- url     : https://prove2.me/theorems/41ea392b-2df9-41c4-95c4-ebaec94dcc53
-- title:
--   The matrix Q = diag(d(v)) − A of a finite multigraph
-- statement:
--   A finite multigraph on a finite vertex set $V$ is described by its multiplicity matrix $M = (M_{v,w})_{v,w\in V}$ of nonnegative integers, where $M_{v,w}$ is the number of edges joining $v$ and $w$ (a positive diagonal entry $M_{v,v}$ counts loops at $v$). The degree of $v$ is the row sum $d(v) = \sum_{w \in V} M_{v,w}$. The matrix $Q = Q_G$ of the multigraph is
--
--   $$Q = \operatorname{diag}\big(d(v)\big)_{v \in V} - M,$$
--
--   viewed as a real matrix, so $Q_{v,v} = d(v) - M_{v,v}$ and $Q_{v,w} = -M_{v,w}$ for $v \ne w$.
--
--   This is the matrix $Q = \operatorname{diag}(d(v)) - A_G$ of Alon and Milman, Section 2, extended to multigraphs. A loop at $v$ adds the same amount to $d(v)$ and to $M_{v,v}$ and therefore does not change $Q$; for the Cayley multigraph $G(T, \phi(S))$ this gives exactly the matrix $|S| \cdot I - \sum_{s \in S} \pi(\phi(s))$ computed in the proof of Lemma 4.8.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 76, Section 2 (Q = diag(d(v)) − A_G); p. 85, proof of Lemma 4.8 (Q of a Cayley graph)

import Mathlib

namespace AlonMilman.PropertyT

/-- The matrix `Q = diag(d(v)) − A` of a finite multigraph (Alon–Milman 1985, p. 76), where the
multigraph on the vertex type `n` is given by its multiplicity matrix `M : Matrix n n ℕ`
(`M v w` = number of edges between `v` and `w`), `d(v) = ∑_w M v w` is the degree of `v`, and
`A = M` cast to `ℝ`. A loop at `v` (`M v v > 0`) adds the same amount to `d(v)` and to `A v v`,
so it contributes `0` to `Q`. -/
noncomputable def laplacian {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℕ) :
    Matrix n n ℝ :=
  Matrix.diagonal (fun v => ∑ w, (M v w : ℝ)) - M.map (fun m => (m : ℝ))

end AlonMilman.PropertyT


