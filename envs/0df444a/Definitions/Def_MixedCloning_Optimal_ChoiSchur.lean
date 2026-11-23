-- Prove2me | Definitions.Def_MixedCloning_Optimal_ChoiSchur
-- name    : MixedCloning_Optimal_ChoiSchur
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:19.503591+00:00
-- url     : https://prove2.me/theorems/3af08e0f-edfd-4299-8a3b-ff2c8d9e3ff6
-- title:
--   Lemma 14 — normalized Choi blocks in Schur–Weyl coordinates
-- statement:
--   For $\lambda\vdash n$ and $\mu\vdash m$ of height at most $r$, Schur–Weyl coordinates are indexed by a Specht multiplicity followed by a Schur-module coordinate. The full Choi matrix of a channel acts on the product of the input and output coordinate spaces.
--
--   In the proof of Lemma 14, its $(\lambda,\mu)$ block has the form
--   $$
--   I_{P_\lambda}\otimes \frac{I_{P_\mu}}{\dim P_\mu}\otimes J_{\lambda\mu}.
--   $$
--   The operation `choiSchurBlock` recovers $J_{\lambda\mu}$ by summing over the Specht coordinates and dividing by $\dim P_\lambda$. The companion `rightTrace` operation traces out the second Schur-module factor. Thus trace preservation is expressed by
--   $$
--   \sum_\mu \operatorname{tr}_{Q_\mu}J_{\lambda\mu}=I_{Q_\lambda}.
--   $$
--
--   Finally, `choiSchurExpression` is the scalar
--   $$
--   \sum_\lambda \frac{\dim P_\lambda}{r^n}
--    \sum_\mu \operatorname{Re}\operatorname{tr}\!\left(
--    J_{\lambda\mu}\int q_\lambda(P)^T\otimes q_\mu(P)\,dP\right),
--   $$
--   which is the Schur–Choi form of the Haar-average overlap in Lemma 14.
-- source:
--   Grinko–Fanizza–Scharnhorst–Spilecki, STOC 2027 submission #243, Lemma 14 and its proof, PDF p.18, especially the displayed Schur-basis forms of the Choi matrix and Eq. (6).

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Young diagrams of a fixed size and bounded height, viewed as a finite type. -/
abbrev SchurLabel (n r : ℕ) := {L : YoungDiagram // L ∈ partitions n r}

/-- Schur–Weyl coordinates, with the Specht multiplicity before the Schur module. -/
abbrev FullSchurIndex (d n r : ℕ) :=
  Σ L : SchurLabel n r, Fin (spechtDim L.val) × SchurIndex L.val d

/-- Coordinates on the input-output Choi space after the two Schur transforms. -/
abbrev ChoiSchurIndex (d n m r : ℕ) := FullSchurIndex d n r × FullSchurIndex d m r

/-- Trace out the second factor of a bipartite matrix. -/
def rightTrace {a b : Type} [Fintype b] (X : Op (a × b)) : Op a :=
  fun i j => ∑ z : b, X (i, z) (j, z)

/-- Recover the unscaled Schur-module Choi block from a full Choi matrix.
The full matrix has the identity on the input Specht factor and `1/dim(P_M)`
times the identity on the output Specht factor. Summing those coordinates and
dividing by `dim(P_L)` therefore removes the multiplicity factors. -/
def choiSchurBlock {d n m r : ℕ} (J : Op (ChoiSchurIndex d n m r))
    (L : SchurLabel n r) (M : SchurLabel m r) :
    Op (SchurIndex L.val d × SchurIndex M.val d) :=
  ((spechtDim L.val : ℂ)⁻¹) • fun i j =>
    ∑ p : Fin (spechtDim L.val), ∑ q : Fin (spechtDim M.val),
      J (⟨L, (p, i.1)⟩, ⟨M, (q, i.2)⟩)
        (⟨L, (p, j.1)⟩, ⟨M, (q, j.2)⟩)

/-- The Haar-averaged overlap written in normalized Schur–Choi blocks. -/
def choiSchurExpression {d n m r : ℕ} (J : Op (ChoiSchurIndex d n m r))
    (b : (L : YoungDiagram) → SchurBasis L d) : ℝ :=
  ∑ L : SchurLabel n r, (spechtDim L.val : ℝ) / (r : ℝ)^n *
    ∑ M : SchurLabel m r,
      ((choiSchurBlock J L M) *
        transposedIntegral r L.val M.val (b L.val) (b M.val)).trace.re

end MixedCloning.Optimal


