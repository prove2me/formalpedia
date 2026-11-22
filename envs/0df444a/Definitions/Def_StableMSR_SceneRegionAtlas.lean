-- Prove2me | Definitions.Def_StableMSR_SceneRegionAtlas
-- name    : StableMSR_SceneRegionAtlas
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T23:31:24.739484+00:00
-- url     : https://prove2.me/theorems/defde35b-62d1-4fa3-be41-3936a6e15f48
-- title:
--   Extract a canonical regional geometry table directly from an original scene
-- statement:
--   The two input header cells select a scene and a candidate representative. An equality comparison with earlier labels yields its exact canonical region, including empty regions. The preparation reads the original scale endpoints, and the output gives the canonical window graph and the point-by-window incidence matrix.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_RegionAtlas
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowProfiles (piece)
namespace StableMSR.Recovery.WindowGeometry
def tableHeight (x : World) := 2+x.n+x.n*x.n
def color (x : World) (u a : ℕ) := x.mem (sceneBase x u+2+a)
def canonical (x : World) (u i a : ℕ) := i< x.n ∧ color x u i=color x u a ∧
  ∀q< x.n,q< i → color x u q≠color x u a
noncomputable def prepare (x : World) (r _j : ℕ) (_s : Bool) : ℤ :=
  let u:=(x.mem 0).toNat;let i:=(x.mem 1).toNat
  if r=0 then x.mem (sceneBase x u) else if r=1 then x.mem (sceneBase x u+1)
  else if canonical x u i (WindowProfiles.subR x r 2) then 1 else 0
noncomputable def SceneAtlas (x : World) (u i : ℕ) (m : ℕ→ℤ) :=
  let y:={x with mem:=m};let W:=piece x u i;let R:=scale x u;let N:=greedyNet x.dist R W
  (∀v : Point x.n,(0< witness y (2+v.val) 0 ↔ v∈N) ∧ center y (2+v.val) 0=((anchor x.dist W R v).val:ℤ)) ∧
  (∀a v : Point x.n,0< center y (pairRow x.n a.val v.val) 0 ↔ v∈window x.dist W R a) ∧
  ∀a v : ↥N,0< witness y (pairRow x.n a.val.val v.val.val) 0 ↔ (interactionGraph x.dist R W).Adj a v
end StableMSR.Recovery.WindowGeometry


