-- Prove2me | Definitions.Def_DetDLP_S8N_MomentDimensions
-- name    : DetDLP_S8N_MomentDimensions
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T12:08:11.369464+00:00
-- url     : https://prove2.me/theorems/3e471aeb-c1b7-5037-9330-ffad445a2bf9
-- title:
--   Elliptic-curve moment circuit dimension functions
-- statement:
--   Defines polynomial-time vertex and edge counting functions on words and proves that they give the actual dimensions for each well-formed moment query.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8N_PortPoly
import Definitions.Def_DetDLP_S8N_MomentPhysicalRows


section
set_option autoImplicit false

namespace DetDLP.S8N.MomentIncidences

def hash (d e : ℕ) := 4*e + 36*d + 10
def atom (d e : ℕ) := 85*(d+1) + 7*hash d e + 12*d + 1
def map (d e : ℕ) := 50*(d+1) + 4*hash d e + 2 + 6*d
def step (d e : ℕ) := 170*(d+1) + 15*hash d e + 31*d + 5
def fold (n d e : ℕ) := 2 + 4*d + n*step d e
def target (d : ℕ) := 10*(d+1) + 3*d

end DetDLP.S8N.MomentIncidences

namespace DetDLP.S8N.MomentDimensions

open Groundwork MomentIncidences

def routed (c o m d e k : ℕ) :=
  (m*(30*(d+1)) + k) + (c*(m*atom d e) +
    o*(target d + (2*m*MomentIncidences.map d e + 2*fold (m-1) d e)))

def anchored (c o m d e k : ℕ) :=
  PortPoly.anchorCount c o m d e + (1 + routed c o m d e k)

def incidences (w : List Bool) :=
  let b := S8G.FpMoment.Code.width (S8M.PortPoly.prime w)
  let d := b+1
  let j := PortPoly.idx w
  anchored (min j 2) (if j = 3 then 1 else 0) (S8G.FpMoment.Code.slots b) d
    (S8H.PointAddresses.wires d) (PortPoly.prefixBits w).length

def nv (w : List Bool) := (PortPoly.decoded w).1 + incidences w + incidences w
def ne (w : List Bool) := incidences w + (incidences w + incidences w)

attribute [local fun_prop] PolyT.add PolyT.mul PolyT.sub PolyT.const PolyT.length

theorem anchored_poly {α : Type} [Enc α] {c o m d e k : α → ℕ}
    (hc : PolyT c) (ho : PolyT o) (hm : PolyT m) (hd : PolyT d) (he : PolyT e) (hk : PolyT k) :
    PolyT (fun x => anchored (c x) (o x) (m x) (d x) (e x) (k x)) := by
  unfold anchored routed PortPoly.anchorCount MomentIncidences.atom
    MomentIncidences.map MomentIncidences.fold MomentIncidences.step
    MomentIncidences.hash MomentIncidences.target
  fun_prop (disch := assumption)

theorem incidences_poly : PolyT incidences := by
  have hb := S8G.FpMoment.Code.width_poly DetDLP.S8N.PortPoly.prime_poly
  have hd := PolyT.add hb (PolyT.const 1)
  have hm := S8G.FpMoment.Code.slots_poly hb
  have he := S8H.PointAddresses.mul_poly.nb hd
  have hc : PolyT (fun w => min (PortPoly.idx w) 2) := by
    simp only [min_def]
    exact PolyT.ite' (PolyT.decide_le PortPoly.idx_poly (PolyT.const 2)) PortPoly.idx_poly (PolyT.const 2)
  have ho : PolyT (fun w => if PortPoly.idx w = 3 then 1 else 0) :=
    PolyT.ite' (PolyT.decide_eq PortPoly.idx_poly (PolyT.const 3)) (PolyT.const 1) (PolyT.const 0)
  exact anchored_poly hc ho hm hd he (PolyT.length PortPoly.prefix_poly)

theorem nv_poly : PolyT nv :=
  PolyT.add (PolyT.add PortPoly.decoded_poly.1 incidences_poly) incidences_poly

theorem ne_poly : PolyT ne :=
  PolyT.add incidences_poly (PolyT.add incidences_poly incidences_poly)

end DetDLP.S8N.MomentDimensions
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentGeometry
open Groundwork DetDLP_W1_Queries S8H0 S8H.PortCombinators S8J.CircuitRealizes RegisterMap NamedBlocks
open S8M S8M.PortPoly RoutesV2
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev word (j : Fin 4) (T : ℕ) (η : List Bool) :=
  M89S1.queryWord 2 (encodeCurveInput p E) [countWord j.val, countWord T, η]

theorem prime_word (j : Fin 4) (T : ℕ) (η : List Bool) : S8M.PortPoly.prime (word E j T η) = p := by
  simp [word, M89S1.queryWord, S8M.PortPoly.prime, DetDLP_W1_Queries.second, encodeCurveInput, encodeNatListBin]

abbrev shape (p m : ℕ) (j : Fin 4) :=
  RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)

noncomputable abbrev net {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  joinB (PointGraph.zeroLast (shape p m j).size)
    (RoutesV2.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E) E.b₂.val
      (-1 : ZMod p).val (3 : ZMod p).val (-27 * E.c₄).val j η id)

noncomputable abbrev core {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  AnchoredLayout.block (net E hm j T η).core ((shape p m j).size + 1)

noncomputable abbrev wires {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  AnchoredLayout.wiring (net E hm j T η).core (net E hm j T η).name

theorem anchor_eq (m d e : ℕ) (j : Fin 4) : PortPoly.anchorCount (copies j) (outputs j) m d e = (RoutesV2.bank j m d e).size + 1 := by
  simp only [PortPoly.anchorCount,RoutesV2.bank,productShape,targetShape,ECSeedBank.ecSeedShape,S8G.SeedAndAtomBank.seedSlot,ECFoldRoutes.foldShape,ECAtomSlot.slotShape,S8H4.Routes.bank,GateRoutes.S,RegisterMap.bank,ECMapRows.mapShape,ECAddRoutes.addShape,ECMapRows.slot,RegisterMap.run,RegisterMap.triple,RegisterMap.mul,GateRoutes.auxShape,Shape.size]; ring

end DetDLP.S8N.MomentGeometry
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentDimensions

open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes RangeRows
open S8G.SeedAndAtomBank S8M MomentIncidences

theorem network_count {s : Shape} {m d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (p T : ℕ) (c : Coeff) (b2 neg1 three c4 : ℕ) (j : Fin 4) (η : List Bool)
    (q : Path (RoutesV2.bank j m d (mulEdges hd)) s) :
    count (RoutesV2.network hd hm p T c b2 neg1 three c4 j η q) =
      routed (RoutesV2.copies j) (RoutesV2.outputs j) m d (mulEdges hd) η.length := by
  unfold RoutesV2.network routed
  rw [join_count, seed_count, join_count]
  congr 1
  apply congrArg₂ (·+·)
  · apply all_count
    intro a
    exact all_count m _ (fun _ => atom_count ..)
  · apply all_count
    intro t
    dsimp only
    rw [join_count, target_count, join_count]
    congr 1
    exact congrArg₂ (·+·)
      (all_count (2*m) _ (fun _ => map_count ..))
      (all_count 2 _ (fun _ => fold_count ..))

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

theorem core_count {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :
    (MomentGeometry.core E hm j T η).A.ne =
      anchored (RoutesV2.copies j) (RoutesV2.outputs j) m (GateSemantics.d p)
        (GateSemantics.e p) η.length := by
  change ((MomentGeometry.shape p m j).size+1) + (1 + count (RoutesV2.network _ _ _ _ _ _ _ _ _ _ _ _)) = _
  rw [network_count]
  exact congrArg (· + _) (MomentGeometry.anchor_eq m (GateSemantics.d p) (GateSemantics.e p) j).symm

theorem incidences_word (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool) :
    incidences (MomentGeometry.word E j T η) = (MomentGeometry.core E hm j T η).A.ne := by
  rw [core_count]
  have hfields : PortPoly.idx (MomentGeometry.word E j T η) = j.val ∧
      PortPoly.prefixBits (MomentGeometry.word E j T η) = η := by
    simp [PortPoly.idx, PortPoly.prefixBits, MomentGeometry.word, M89S1.queryWord,
      DetDLP_W1_Queries.third, DetDLP_W1_Queries.second]
  simp only [incidences, MomentGeometry.prime_word, S8G.FpMoment.Code.width_eq,
    S8G.FpMoment.Code.slots_eq, hfields.1, hfields.2, RoutesV2.copies, RoutesV2.outputs,
    S8H.PointAddresses.wires_eq (GateSemantics.hd p)]

theorem nv_of_gateCount (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool)
    (hgate : (PortPoly.decoded (MomentGeometry.word E j T η)).1 = (MomentGeometry.core E hm j T η).A.ng) :
    nv (MomentGeometry.word E j T η) =
      (S8J.CircuitRealizes.G (MomentGeometry.core E hm j T η) (MomentGeometry.wires E hm j T η)).nV := by
  rw [nv, hgate, incidences_word E hm]
  rfl

theorem ne_word (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool) :
    ne (MomentGeometry.word E j T η) =
      (S8J.CircuitRealizes.G (MomentGeometry.core E hm j T η) (MomentGeometry.wires E hm j T η)).nE := by
  rw [ne, incidences_word E hm]
  rfl

end DetDLP.S8N.MomentDimensions
end


