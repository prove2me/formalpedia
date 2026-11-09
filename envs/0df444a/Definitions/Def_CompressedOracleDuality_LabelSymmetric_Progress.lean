-- Prove2me | Definitions.Def_CompressedOracleDuality_LabelSymmetric_Progress
-- name    : CompressedOracleDuality_LabelSymmetric_Progress
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:32.666292+00:00
-- url     : https://prove2.me/theorems/44bff607-e700-4be0-9274-b37626c289ef
-- title:
--   Collision projections, progress and per-query leakage
-- statement:
--   On the joint memory–database space, $\Pi_{=0}$ keeps the amplitudes with collision-free databases and sets all other amplitudes to zero. Its complementary projection $\Pi_{\ge1}$ keeps precisely colliding databases. If $|\psi_t\rangle$ is the compressed run after $t$ queries, define
--   $$\Delta_t=\|\Pi_{\ge1}|\psi_t\rangle\|,\qquad L_t=\|\Pi_{\ge1}\mathrm{CStO}\,\Pi_{=0}|\psi_t\rangle\|.$$
--   The projections act on the database and leave the memory unchanged. These quantities describe measured collision progress and the contribution of a single query; the inequalities bounding them are separate statements.
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 21, standard compressed oracle setup preceding (54)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- §4.1: diagonal orthogonal projectors on collision-free/colliding databases. -/
def projectDatabase {n : ℕ} {W : Type} [Fintype W]
    (colliding : Bool) (ψ : EuclideanSpace ℂ (Memory n W × Database n)) :
    EuclideanSpace ℂ (Memory n W × Database n) :=
  open Classical in
  WithLp.toLp 2 fun p =>
    if (if colliding then ¬ CollisionFree p.2 else CollisionFree p.2) then ψ p else 0

def progressAt {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) : ℝ :=
  ‖projectDatabase true (compressedStateAt A t)‖

/-- The norm of Π_{≥1} CStO Π_{=0} ψ_t in (54). -/
def queryLeakage {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) : ℝ :=
  ‖projectDatabase true
    (act (compressedOracle (2 ^ n) n W) (projectDatabase false (compressedStateAt A t)))‖

end CompressedOracleDuality.LabelSymmetric


