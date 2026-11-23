-- Prove2me | Definitions.Def_StableMSR_SingleWindowCodes
-- name    : StableMSR_SingleWindowCodes
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T00:04:40.332323+00:00
-- url     : https://prove2.me/theorems/00529b60-298f-4e40-b821-c31c164dbe03
-- title:
--   Numeric window input to the executable singleton separator compiler
-- statement:
--   Instantiates the executable finite circuit constructor on the canonical net and interaction graph of a metric region. Integer ball-word labels decode to feasible trace partitions; compatibility and owned point masks are the mission definitions.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleSeparatorCircuit
import Definitions.Def_StableMSR_SingleWindowGrammar
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.OracleQueries StableMSR.Recovery.RegionalSeeds
open StableMSR.Recovery.FewBallRows StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.WindowCSP
namespace StableMSR.Recovery.SingleCodes
def encode (h g u : ℕ) := u*(h+1)+g
def words (n h : ℕ) : List ℕ := (List.range (h+1)).flatMap (fun g=>(List.range (rows n (h+1))).map (fun u=>encode h g u))
noncomputable def decode (x : World) (W : Cluster x.n) (h c : ℕ) :=
  classes W (digitRel (seedWorld x h) (c%(h+1)) (c/(h+1)))
noncomputable def menu (x : World) (W : Cluster x.n) (h : ℕ) :=
  (words x.n h).filter fun c=>let P:=decode x W h c;decide (Feasible W P.card P)
noncomputable def lookup {n : ℕ} {α : Type} (f : Point n→α) (a : ℕ) (default : α) := if p:a< n then f ⟨a,p⟩ else default
noncomputable def blockList {n : ℕ} (P : Partition n) : List (List ℕ) := P.toList.map (fun C=>C.toList.map Fin.val)
/-- The normalized input of the executable array compiler, defined directly on the mathematical scene and distance oracle. A menu entry is an integer ball word. -/
noncomputable def instanceOf (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) : SingleCircuit.Instance where
  n:=x.n
  active:=fun a=>lookup (fun v=>decide (v∈Supplement.greedyNet x.dist R W)) a false
  edge:=fun a b=>lookup (fun v=>lookup (fun u=>decide (v≠u ∧ x.dist v u≤8*R ∧ x.dist u v≤8*R)) b false) a false
  menu:=fun a=>lookup (fun v=>menu x (window x.dist W R v) h) a []
  test:=fun a b c k=>lookup (fun v=>lookup (fun u=>decide (compatible (anchor x.dist W R) v u (decode x (window x.dist W R v) h c) (decode x (window x.dist W R u) h k))) b false) a false
  owned:=fun a c=>lookup (fun v=>blockList (WindowCSP.owned (anchor x.dist W R) v (decode x (window x.dist W R v) h c))) a []
noncomputable def regionalCircuit (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) :=SingleCircuit.compileRegion (instanceOf x W R h) w
end StableMSR.Recovery.SingleCodes


