-- Prove2me | Definitions.Def_DetDLP_M3B_ECPhysicalNet
-- name    : DetDLP_M3B_ECPhysicalNet
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:35:03.77646+00:00
-- url     : https://prove2.me/theorems/4d605aac-e60a-405f-b9e6-14a666c103a0
-- title:
--   EC Stage II physical register network
-- statement:
--   Complete physical register layout, tests, edge bounds, prefix verification, and lookup-bus address readout for the short-Weierstrass Stage II separator.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.2 (pp. 14-15)

import Definitions.Def_DetDLP_M3B_ECChainBlocks
import Definitions.Def_DetDLP_M3B_ECArithBlock
import Definitions.Def_DetDLP_M3B_ECChains

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace DetDLP.M3B.ECPhysicalNet
open S8H0 RegisterMap NamedBlocks GateRoutes HashRows S8H.ECPointArithmetic
open ECArithBlock ECChainBlocks ECCert
variable {p m k : ℕ} [Fact p.Prime]

abbrev busWidth (p k : ℕ) := ECAddrGadget.width p k
abbrev SlotCell (p k : ℕ) := Shape.pair (Sh p) (.pair (.word (width p)) (.pair (.word (width p+1)) (.vec 3 (.word (busWidth p k)))))
abbrev ShapeOf (p m k : ℕ) := Shape.pair (.vec (4*m) (SlotCell p k))
  (.pair (.vec 2 (Chain p (2*m))) (PointCell (width p)))
abbrev R := ShapeOf p m k

def cell (i : Fin (4*m)) : Path (SlotCell p k) (ShapeOf p m k) := fun a => .fst (.vec i a)
def slot (i : Fin (4*m)) : Path (Sh p) (ShapeOf p m k) := fun a => cell i (.fst a)
def bankName (i : Fin (4*m)) : Fin ((Sh p).size+1) → Fin ((ShapeOf p m k).size+1) :=
  Fin.lastCases (Fin.last _) fun j => ((finProdFinEquiv (i,j.castAdd _)).castAdd _).castSucc

def slotPath (i : Fin (4*m)) : SlotPath p (ShapeOf p m k) where
  bank := bankName i
  hash := fun j => .reg (slot i (CurveRows.outbit 6 j))
  diff := fun j => .reg (cell i (.snd (.fst (.word j))))
  carry := fun j => .reg (cell i (.snd (.snd (.fst (.word j)))))
theorem bankName_index (i : Fin (4*m)) (a : Addr (Sh p)) :
    bankName (k:=k) i a.index.castSucc = (slot (k:=k) i a).index.castSucc :=
  Fin.lastCases_castSucc a.index

private theorem localHash (u : GateSemantics.U p) (j : Fin (width p)) :
    u (CurveRows.outbit (e:=GateSemantics.e p) 6 j).index.castSucc = rawHash u j :=
  (Addr.correct (CurveRows.outbit (e:=GateSemantics.e p) 6 j) (u ∘ Fin.castSucc)).symm

theorem hash_route (i : Fin (4*m)) (v : Fin ((ShapeOf p m k).size+1) → Bool) (j : Fin (width p)) :
    ((slotPath i).hash j).eval v = rawHash (v ∘ (slotPath i).bank) j := by
  have h := congrArg v (bankName_index (p:=p) (m:=m) (k:=k) i (CurveRows.outbit 6 j)).symm
  exact h.trans (localHash (v ∘ bankName (p:=p) (m:=m) (k:=k) i) j)

def busAddr (i : Fin (4*m)) (b : Fin 3) (j : Fin (busWidth p k)) : Addr (ShapeOf p m k) :=
  cell i (.snd (.snd (.snd (.vec b (.word j)))))
def inputs : ECArithNet.Inputs (ShapeOf p m k) (4*m) (busWidth p k) where
  parity i := .reg (slot i (CurveRows.ybit ⟨0,GateSemantics.hd p⟩))
  hash i := RangeRows.pad ((slotPath i).hash)
  selected i j := .reg (busAddr i 0 j)
  addr i j := busAddr i 1 j
  carry i j := .reg (busAddr i 2 j)

def ix (side : Bool) (i : Fin (2*m)) : Fin (4*m) := ⟨2*i.val+side.toNat,by cases side <;> simp <;> omega⟩
def sideIdx (side : Bool) : Fin 2 := if side then 1 else 0
def chainPath (side : Bool) : Path (Chain p (2*m)) (ShapeOf p m k) := fun a => .snd (.fst (.vec (sideIdx side) a))
def terminal : Path (PointCell (width p)) (ShapeOf p m k) := fun a => .snd (.snd a)
def factorWires (side : Bool) (i : Fin (2*m)) : ECChainBlocks.Wires (ShapeOf p m k) :=
  (.pin false, GateRoutes.word (fun a => slot (ix side i) (RangeRows.xa (.fst a))),
    GateRoutes.word (fun a => slot (ix side i) (RangeRows.ya (.fst a))))
variable (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) (T : ℕ)
variable (P : E.toAffine.Point)
noncomputable def chainIn (side : Bool) : Fin (2*m+1) → ECChainBlocks.Wires (ShapeOf p m k) :=
  Fin.cases (publicPoint (coords (if side then (0 : E.toAffine.Point) else P))) (factorWires side)
noncomputable def slotAt (i : Fin (4*m)) := ECArithBlock.slotBlock E seed ⟨i.val/4,by omega⟩ T (slotPath (p:=p) (k:=k) i)
noncomputable def sideBlock (side : Bool) := chainBlock E (chainPath (m:=m) side) (chainIn (k:=k) E P side) terminal
noncomputable def arithmetic := joinB (manyB (4*m) (slotAt (k:=k) E seed T))
  (joinB (sideBlock (m:=m) (k:=k) E P false) (sideBlock (m:=m) (k:=k) E P true))

def pointIdx (i : Fin m) (j : Fin 2) : Fin (2*m) := ⟨2*i.val+j.val,by omega⟩
def refs : List (Ref (ShapeOf p m k)) := ECPrefix.refs (b:=bitLen p)
  (fun s i j b => (factorWires s (pointIdx i j)).2.1 b.val)
  (fun s i j b => (factorWires s (pointIdx i j)).2.2 b.val)
variable (pre : List Bool)
noncomputable abbrev layout := ECArithNet.withLookups inputs T (arithmetic (k:=k) E seed T P) refs pre k (le_max_right _ _)
noncomputable abbrev test := ECArithNet.physicalTest inputs T (arithmetic (k:=k) E seed T P) refs pre k (le_max_right _ _)
noncomputable def namedEquiv := ECArithNet.physicalEquiv inputs T (arithmetic (k:=k) E seed T P) refs pre k (le_max_right _ _)

def slotBudget (p : ℕ) := 28*GateSemantics.e p + 400*(width p+2)
theorem slot_edges (i : Fin (4*m)) : (slotAt (k:=k) E seed T i).core.A.ne ≤ slotBudget p := by
  simp (disch := decide) only [slotAt,slotBlock,baseBlock,rewire,threshold,onCurve,parityRow,products,RangeRows.block,
    RangeRows.many,HashRows.block,HashRows.product,HashRows.sumRows,RangeRows.checker,joinB,eqs,
    NamedBlocks.add,rows,mapped,S8J.join,S8C.AddLayout.layout,PointGraph.zeroLast,slotBudget,
    AnchoredLayout.anchors,w3_fpMulLayout,w3_m5Layout,w3_forgetSides,GateSemantics.e,GateSemantics.d,if_pos,if_neg]
  omega

theorem arithmetic_edges : (arithmetic (k:=k) E seed T P).core.A.ne ≤
    4*m*slotBudget p + 2*edgeBound (width p) (GateSemantics.e p) (2*m) := by
  rw [two_mul (edgeBound ..)]
  exact Nat.add_le_add (manyB_edges _ _ (slot_edges E seed T)) (Nat.add_le_add (chainBlock_edges ..) (chainBlock_edges ..))

private theorem bankEdges {r : Shape} {n d : ℕ} (I : ECArithNet.Inputs r n d) (th : ℕ) :
    (ECArithNet.bank I th).core.A.ne = n*(7*d) := by
  induction n with
  | zero => exact (Nat.zero_mul _).symm
  | succ n ih =>
    let tail : ECArithNet.Inputs r n d := ⟨fun i => I.parity i.succ, fun i => I.hash i.succ,
      fun i => I.selected i.succ,fun i => I.addr i.succ,fun i => I.carry i.succ⟩
    change (ECAddrGadget.block th (I.parity 0) (I.hash 0) (I.selected 0) (fun j => .reg (I.addr 0 j)) (I.carry 0)).core.A.ne +
      (ECArithNet.bank tail th).core.A.ne = _
    rw [ECAddrGadget.edges,ih]; ring

theorem refs_length : (refs (p:=p) (m:=m) (k:=k)).length = 4*m*(3*bitLen p) := by
  simp [refs,ECPrefix.refs,ECPrefix.side,ECPrefix.one,List.length_flatMap,List.finRange_succ]; ring

noncomputable def body := ECArithNet.body inputs T (arithmetic (k:=k) E seed T P) refs pre

theorem body_edges : (body (k:=k) E seed T P pre).core.A.ne ≤
    4*m*slotBudget p + 2*edgeBound (width p) (GateSemantics.e p) (2*m) +
    (4*m*(7*busWidth p k) + max 1 (4*m*(3*bitLen p))) := by
  apply Nat.add_le_add (arithmetic_edges ..)
  apply Nat.add_le_add (bankEdges ..).le
  rw [← refs_length (k:=k)]; exact ECArithNet.prefix_edges ..

theorem layout_edges : (layout (k:=k) E seed T P pre).ne ≤
    3*((ShapeOf p m k).size+1 + (4*m*slotBudget p + 2*edgeBound (width p) (GateSemantics.e p) (2*m) +
    (4*m*(7*busWidth p k) + max 1 (4*m*(3*bitLen p))))) + 4*m*k := by
  let u := (ShapeOf p m k).size+1+(body (k:=k) E seed T P pre).core.A.ne
  change u+(u+u)+4*m*k ≤ _
  dsimp only [u]; have H := body_edges (k:=k) E seed T P pre; omega

section Decode
open GateSemantics
variable [E.IsElliptic]
variable (v : Fin ((ShapeOf p m k).size+1) → Bool)
variable (i : Fin (4*m)) (b : Fin m) (hb : i.val/4 = b.val)
variable (hs : (slotAt E seed T i).OK v) (ha : (ECArithNet.bank inputs T).OK v)

/-- Extract the checked slot, retaining exactly the actual bus words. -/
noncomputable def checkedSlot : ECArithNet.Checked E seed T k b := by
  let z : SlotPath p (ShapeOf p m k) := slotPath i
  let u := v ∘ z.bank
  have eq : (⟨i.val/4,by omega⟩ : Fin m) = b := Fin.ext hb
  change (slotBlock E seed _ T z).OK v at hs
  rw [eq] at hs
  have H := (slotBlock_iff E seed b T z v (hash_route i v)).mp hs
  let h := H.2.choose
  let D := GateSemantics.typed u h
  let w : Slot E seed T b := ⟨((false,D.1.2),D.2,diffCert z v),
    (S8H4.ElemTiles.encode_iff E seed b T (bitLen p) [] _).2 H.2.choose_spec.2⟩
  let I := inputs (p:=p) (m:=m) (k:=k)
  let aux : ECAddrGadget.Aux (busWidth p k) := (fun j => (I.selected i j).eval v,
    fun j => (Ref.reg (I.addr i j)).eval v,fun j => (I.carry i j).eval v)
  refine ⟨(w,aux),?_⟩
  have G := (ECArithNet.bank_iff I T v).mp ha i
  have hp' : (I.parity i).eval v = ECAddrGadget.odd w :=
    (congrArg v (bankName_index (p:=p) (k:=k) i (CurveRows.ybit ⟨0,hd p⟩)).symm).trans (parity_value u h)
  have hh : (fun j => (I.hash i j).eval v) = ECAddrGadget.digits (busWidth p k) (ECAddrGadget.hash w) := by
    funext j; change _ = ((typed u h).2.1 6).1.val.testBit j.val
    rw [outVal u h 6]; exact RangeRows.pad_eval z.hash v (rawHash u) (hash_route i v) j
  change ECAddrGadget.good T _ _ aux at G
  rw [hp',hh] at G; exact G

private theorem checkedCoord (q : Bool) (j : Fin (bitLen p)) :
    let w := (checkedSlot E seed T v i b hb hs ha).1.1
    let coord : Path (triple (width p)) (Sh p) := if q then RangeRows.ya else RangeRows.xa
    (GateRoutes.word (fun a => slot i (coord (.fst a))) j.val).eval v =
      (if q then w.1.1.2.2 else w.1.1.2.1).val.testBit j.val := by
  let z : SlotPath p (ShapeOf p m k) := slotPath i
  let u := v ∘ z.bank
  have eq : (⟨i.val/4,by omega⟩ : Fin m) = b := Fin.ext hb
  have hs' : (slotBlock E seed b T z).OK v := eq ▸ hs
  let h := ((slotBlock_iff E seed b T z v (hash_route i v)).mp hs').2.choose
  have hj : j.val < width p := Nat.lt_succ_of_lt j.isLt
  let l : Fin (width p) := ⟨j.val,hj⟩
  have route (a : Addr (Sh p)) : (Ref.reg (slot (k:=k) i a)).eval v = a.get (raw u) :=
    (congrArg v (bankName_index i a).symm).trans (Addr.correct a (u ∘ Fin.castSucc)).symm
  cases q <;> dsimp only [Bool.false_eq_true,↓reduceIte]
  · change (padded _ j.val).eval v = ((typed u h).1.2.1.val).testBit j.val
    rw [coordX]; simp only [padded,dif_pos hj]; exact (route (RangeRows.xa (.fst (.word l)))).trans (ResidueWires.value_bit _ l).symm
  · change (padded _ j.val).eval v = ((typed u h).1.2.2.val).testBit j.val
    rw [coordY]; simp only [padded,dif_pos hj]; exact (route (RangeRows.ya (.fst (.word l)))).trans (ResidueWires.value_bit _ l).symm

variable (F : Fin m → List (Point E)) (hT : T ≤ p) (hk : 2*T ≤ 2^k) (hF : ListsOK E F seed T)
include hk in
theorem address_readout :
    bitsToNat (fun j : Fin k => (Ref.reg (busAddr i 1 (Fin.castLE (le_max_right _ _) j))).eval v) =
      ECAddress.address E seed T b ((F b).get (indexEquiv E F seed T w3_m5_modmul_r2 hT hF b
        (checkedSlot E seed T v i b hb hs ha).1.1)) := by
  let a := checkedSlot E seed T v i b hb hs ha
  exact ECAddrGadget.low_address a.1.1 k F w3_m5_modmul_r2 hT hF hk a.2
end Decode

section Table
variable [E.IsElliptic]
open S8J
abbrev Accepted := {x // Accept (layout (k:=k) E seed T P pre) (test (k:=k) E seed T P pre) x}
private theorem slotOwner (b : Fin m) (j : Fin 2) (s : Bool) : (ix s (pointIdx b j)).val/4 = b.val := by
  cases s <;> simp [ix,pointIdx] <;> omega
noncomputable def checkedTable (x : Accepted (k:=k) E seed T P pre) : ECArithNet.CheckedTable E seed T k :=
  let a := namedEquiv (k:=k) E seed T P pre x
  let rows := (manyB_iff _ a.val).mp ((joinB_iff ..).mp a.2.1).1
  fun b j s => checkedSlot E seed T a.val (ix s (pointIdx b j)) b (slotOwner b j s) (rows _) a.2.2.1

variable (F : Fin m → List (Point E)) (hT : T ≤ p) (hk : 2*T ≤ 2^k) (hF : ListsOK E F seed T)
noncomputable def tuple (x : Accepted (k:=k) E seed T P pre) :=
  ECArithNet.tableDecode E F seed T k w3_m5_modmul_r2 hT hk hF (checkedTable E seed T P pre x)

theorem accepted_address (x : Accepted (k:=k) E seed T P pre) (b : Fin m) (j : Fin 2) (s : Bool) :
    let a := namedEquiv (k:=k) E seed T P pre x
    let t := tuple E seed T P pre F hT hk hF x
    bitsToNat (fun l : Fin k => (Ref.reg (busAddr (ix s (pointIdx b j)) 1 (Fin.castLE (le_max_right _ _) l))).eval a.val) =
      ECAddress.address E seed T b ((F b).get (if s then t.2 b j else t.1 b j)) :=
  ECArithNet.address_at E F seed T k w3_m5_modmul_r2 hT hk hF (checkedTable E seed T P pre x) b j s
private theorem namedAt {r : Shape} {n d k' : ℕ} (I : ECArithNet.Inputs r n d) (th : ℕ)
    (A : B (r.size+1)) (rs : List (Ref r)) (pr : List Bool) (hd : k' ≤ d)
    (x : {x // Accept (ECArithNet.withLookups I th A rs pr k' hd) (ECArithNet.physicalTest I th A rs pr k' hd) x})
    (j : Fin (r.size+1)) : (ECArithNet.physicalEquiv I th A rs pr k' hd x).1 j =
      x.1 (j.castAdd (ECArithNet.body I th A rs pr).core.A.ne) := by
  let b := ECArithNet.body I th A rs pr
  let a := AnchoredLayout.block b.core (r.size+1)
  let W := AnchoredLayout.wiring b.core b.name
  let L := S8J.CircuitRealizes.circuit a W
  change x.val (L.bit (L.rep (W.rep j))) = x.val (W.rep j)
  exact congrArg x.val (L.rep_bit (W.rep j))

theorem physical_address (x : Accepted (k:=k) E seed T P pre) (b : Fin m) (j : Fin 2) (s : Bool) :
    let t := tuple E seed T P pre F hT hk hF x
    bitsToNat (fun l : Fin k => x.val ((busAddr (ix s (pointIdx b j)) 1
      (Fin.castLE (le_max_right _ _) l)).index.castSucc.castAdd (body (k:=k) E seed T P pre).core.A.ne)) =
      ECAddress.address E seed T b ((F b).get (if s then t.2 b j else t.1 b j)) := by
  apply Eq.trans _ (accepted_address E seed T P pre F hT hk hF x b j s)
  apply congrArg bitsToNat; funext l
  exact (namedAt inputs T (arithmetic (k:=k) E seed T P) refs pre (le_max_right _ _) x _).symm

theorem accepted_prefix (x : Accepted (k:=k) E seed T P pre) : prefixOK E F pre (tuple E seed T P pre F hT hk hF x) := by
  let a := namedEquiv E seed T P pre x
  let w := ECArithNet.forgetTable E seed T k hT hk (checkedTable E seed T P pre x)
  have rows := (manyB_iff _ a.val).mp ((joinB_iff ..).mp a.2.1).1
  apply (ECPrefix.prefix_correct E F seed T w3_m5_modmul_r2 hT hF _ _ a.val w _ _ pre).mp
  · exact (ECArithNet.prefix_iff ..).2 a.2.2.2
  · intro s b j l; exact checkedCoord E seed T a.val _ b (slotOwner b j s) (rows _) a.2.2.1 false l
  · intro s b j l; exact checkedCoord E seed T a.val _ b (slotOwner b j s) (rows _) a.2.2.1 true l
end Table

end DetDLP.M3B.ECPhysicalNet


