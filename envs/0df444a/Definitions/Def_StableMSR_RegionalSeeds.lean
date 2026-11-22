-- Prove2me | Definitions.Def_StableMSR_RegionalSeeds
-- name    : StableMSR_RegionalSeeds
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-21T13:17:38.79499+00:00
-- url     : https://prove2.me/theorems/925bd207-b394-42e3-b006-4cea351d3773
-- title:
--   Regional partition menus from center and distance-witness guesses
-- statement:
--   Restrict each guessed ball/threshold equivalence test to a supplied set W of points. Materialize the resulting classes and retain only feasible partitions of W. The trace of an optimal partition consists of all its nonempty intersections with W.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Lemmas 3.3 and 3.8 and Algorithm 1. Local-window variant of the large-cluster enumeration.

import Definitions.Def_StableMSR_FewBallRows
set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
namespace StableMSR.Recovery.RegionalSeeds
def seedWorld (x : World) (h : ℕ) : World := {x with k:=h+1}
noncomputable def tracePartition {n : ℕ} (O : Partition n) (W : Cluster n) : Partition n :=
  ((O.filter (fun C=>(C∩W).Nonempty)).image (fun C=>C∩W))
noncomputable def classes {n : ℕ} (W : Cluster n) (R : Relation) : Partition n :=
  W.image (fun i=>W.filter (fun j=>R i.val j.val))
noncomputable def traceMenu (x : World) (h : ℕ) (W : Cluster x.n) : Finset (Partition x.n) :=
  (((Finset.range (h+1)).product (Finset.range (rows x.n (h+1)))).image
    (fun gu=>classes W (digitRel (seedWorld x h) gu.1 gu.2))).filter
      (fun P=>Feasible W P.card P)
end StableMSR.Recovery.RegionalSeeds


