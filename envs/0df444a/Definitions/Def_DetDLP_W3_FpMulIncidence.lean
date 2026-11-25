-- Prove2me | Definitions.Def_DetDLP_W3_FpMulIncidence
-- name    : DetDLP_W3_FpMulIncidence
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:52:40.682968+00:00
-- url     : https://prove2.me/theorems/2047771d-7fa6-4581-9882-0c949e522430
-- title:
--   Incidence layout of a prime-field multiplier
-- statement:
--   Replacing every multiplier wire by its two endpoint incidences preserves the gate tests on every Boolean assignment. For word width $d$, there are fewer than $2200(d+1)$ incidences. Variable vertices have degree two, and each gate retains its original degree, less than $136(d+1)^{3/4}$. The external pins therefore describe the same multiplication certificates as in the original network.

import Definitions.Def_DetDLP_W3_FpIncidence
import Definitions.Def_DetDLP_W3_ModMulChain

set_option autoImplicit false
namespace DetDLP
open w4_M5Network w4_M5GraphBounds w4_M5PortTensor

def w3_forgetSides (H : BipartiteMultigraph) : WireGraph where
  nV := H.nV
  nE := H.nE
  endpoints := H.endpoints
  loopless e h := H.bipartite e (congrArg H.side h)

def w3_m5HalfGate (G : WireGraph) : Fin (G.nE+G.nE) → Fin G.nV :=
  Fin.addCases (fun e => (G.endpoints e).1) (fun e => (G.endpoints e).2)

def w3_m5Layout (G : WireGraph) : w3_FactorLayout where
  ng := G.nV
  nb := G.nE
  ne := G.nE + G.nE
  gate := w3_m5HalfGate G
  bit := G.forgetHalf
  rep := G.leftHalf
  rep_bit := G.forget_leftHalf

theorem w3_m5LayoutEnds (G : WireGraph) (e : Fin (G.nE+G.nE)) :
    (w3_factorGraph (w3_m5Layout G)).endpoints e = G.subdivision.endpoints e := by
  induction e using Fin.addCases with
  | left f => simp [w3_factorGraph,w3_m5Layout,w3_m5HalfGate,WireGraph.subdivision,WireGraph.forgetHalf]
  | right f => simp only [w3_factorGraph,w3_m5Layout,w3_m5HalfGate,WireGraph.subdivision,WireGraph.forgetHalf,Fin.addCases_right,id_eq]

theorem w3_m5LayoutDeg (G : WireGraph) (v : Fin (G.nV+G.nE)) :
    (w3_factorGraph (w3_m5Layout G)).deg v = G.subdivision.deg v := by
  unfold WireGraph.deg BipartiteMultigraph.deg WireGraph.ports BipartiteMultigraph.ports
  congr 1; apply List.filter_congr; intro e _
  rw [w3_m5LayoutEnds G e]
  rfl

theorem w3_m5LayoutBitDeg (G : WireGraph) (b : Fin G.nE) :
    (w3_factorGraph (w3_m5Layout G)).deg (Fin.natAdd G.nV b) = 2 :=
  (w3_m5LayoutDeg G _).trans (G.subdivision_deg_equalityVertex b)

theorem w3_m5LayoutGateDeg (G : WireGraph) (v : Fin G.nV) :
    (w3_factorGraph (w3_m5Layout G)).deg (Fin.castAdd G.nE v) = G.deg v :=
  (w3_m5LayoutDeg G _).trans (G.subdivision_deg_oldVertex v)

def w3_m5LocalInc (G : WireGraph) (v : Fin G.nV) (j : Fin (G.deg v)) :
    {f : Fin (G.nE+G.nE) // (w3_m5Layout G).gate f = v} := by
  let e := (G.ports v).get j
  refine ⟨G.incidentHalf v e,?_⟩
  have h := (G.mem_ports v e).mp (List.get_mem _ j)
  change w3_m5HalfGate G (G.incidentHalf v e) = v
  unfold WireGraph.incidentHalf
  split
  · rename_i hl; exact (Fin.addCases_left ..).trans hl
  · rename_i hr; exact (Fin.addCases_right ..).trans (h.resolve_left hr)

def w3_m5FactorTest (G : WireGraph) (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool) :
    w3_factorTest (w3_m5Layout G) := fun v x => T v (fun j => x (w3_m5LocalInc G v j))

theorem w3_m5FactorTest_spec (G : WireGraph) (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (x : Fin G.nE → Bool) (v : Fin G.nV) :
    w3_m5FactorTest G T v (fun e => x ((w3_m5Layout G).bit e.1)) =
      T v (fun j => x ((G.ports v).get j)) := by
  apply congrArg (T v); funext j
  exact congrArg x (G.forget_incidentHalf _ _)

abbrev w3_fpMulLayout (d : ℕ) (hd : 1 ≤ d) := w3_m5Layout (w3_forgetSides (graph d hd))

def w3_fpMulTests (d : ℕ) (hd : 1 ≤ d) : w3_factorTest (w3_fpMulLayout d hd) :=
  w3_m5FactorTest (w3_forgetSides (graph d hd)) (tensor hd)

theorem w3_fpMulPins_inc {d : ℕ} (hd : 1 ≤ d) (x y : ℕ) (r : w3_mulRun d hd) :
    w3_mulPins hd x y r ↔ (∀ i, r.2 (ext hd i) = w3_mulBus d x y r.1.val i) ∧
    ∀ g, w3_fpMulTests d hd g (fun e => r.2 ((w3_fpMulLayout d hd).bit e.1)) = true := by
  apply and_congr_right; intro _
  apply forall_congr'; intro v
  exact Iff.of_eq (congrArg (· = true) (w3_m5FactorTest_spec (w3_forgetSides (graph d hd)) (tensor hd) r.2 v).symm)

theorem w3_fpMulIncidenceBounds {d : ℕ} (hd : 1 ≤ d) :
    (w3_fpMulLayout d hd).ne < 2200*(d+1) ∧
    (∀ b, (w3_factorGraph (w3_fpMulLayout d hd)).deg (Fin.natAdd (w3_fpMulLayout d hd).ng b) = 2) ∧
    ∀ v, ((w3_factorGraph (w3_fpMulLayout d hd)).deg (Fin.castAdd (w3_fpMulLayout d hd).nb v) : ℝ) <
      136*((d:ℝ)+1)^((3:ℝ)/4) := by
  refine ⟨?_,w3_m5LayoutBitDeg _,?_⟩
  · change (graph d hd).nE + (graph d hd).nE < _
    have := graph_edge_bound hd; omega
  · intro v
    have he := w3_m5LayoutGateDeg (w3_forgetSides (graph d hd)) v

    have h : (graph d hd).deg v ≤ (graph d hd).maxDeg := Finset.le_sup (f := (graph d hd).deg) (Finset.mem_univ v)
    exact (Nat.cast_le.mpr (he.le.trans h)).trans_lt (graph_maxDeg_bound hd)

end DetDLP


