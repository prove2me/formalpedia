-- Prove2me | Definitions.Def_DetDLP_D4SoloPlanDefs
-- name    : DetDLP_D4SoloPlanDefs
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:12:50.596453+00:00
-- url     : https://prove2.me/theorems/67adf146-b5f4-5db1-9dcf-679be4dd072e
-- title:
--   Core Data Structures and Branch/Plan Constructors for Section 4.3 Partial Unrolling
-- statement:
--   Defines the data structures and lightweight constructors shared across the Section 4.3 / Appendix D.4 partial-unroll rank enumerator and concrete source evaluator: the oracle-call witness predicate `CallCovered`, the Hermite binary modulus `soloPoly`, fuel and polynomial-bound combinators `A_fuel` and `compExp`, quotient-ring homomorphisms `polyToB`, `castU`, `castB`, reattachment witnesses `ReattachWit`, branch constructors `mkPlanBranchAux`, and the guarded contraction plan constructor `mkSoloPlanFromBr`.
-- source:
--   A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Section 4.3 & Appendix D.4 (Def_DetDLP_D4SoloPlanDefs.lean)

import Definitions.Def_DetDLP_D4SoloForest2
import Definitions.Def_DetDLP_D4UnrollBudget
import Theorems.Thm_DetDLP_d4_reattach_poly_and_spec

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace DetDLP.D4SoloPlanDefs

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section

/-- Call-witness record for bounding `runCallsV2` time, space, and `maxLen`. -/
def CallCovered {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc guard bBudget : ℕ) (e : Call) : Prop :=
  ∃ (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd)
    (j : ℕ)
    (pendingNodes doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
    (tagB : Bool) (b' u' loss' : ℕ) (accVal : B f x.l (guard + x.p)),
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let a := D3Stopped.shift x.S nd.d
    let u_w := D3Stopped.width x.S nd.d
    let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
    let bnd := polyBound H_loc (D4NodeQuery.request nd.G nd.host a u_w nd.pCurr x.l f j).length +
      polyBound K_loc (n + (stepInput nd.G a u_w nd.pCurr x.l f cert.lbl).length) + c_loc
    nd.d < Nat.clog 32 (4 * x.m) ∧
    j ≤ cert.nBranches ∧
    b' ≤ bBudget ∧
    u' < 2 ^ bBudget ∧
    loss' ≤ guard ∧
    pendingNodes.length + doneNodes.length ≤ 64 ^ Nat.clog 32 (4 * x.m) ∧
    (∀ m ∈ pendingNodes, m.d ≤ Nat.clog 32 (4 * x.m)) ∧
    (∀ m ∈ doneNodes, m.d ≤ Nat.clog 32 (4 * x.m)) ∧
    e.1 = phaseStateV2 [tagB] ctx (pendingNodes.map (·.toWorkItem.bits))
      (doneNodes.map (·.toWorkItem.bits)) b' u' (residue f x.l (guard + x.p) hf accVal) loss' ∧
    e.2.1 = D4NodeQuery.request nd.G nd.host a u_w nd.pCurr x.l f j ∧
    RunsWithin M_node o_node e.2.1 e.2.2 bnd bnd

def soloPoly (S : ℕ) : ℤ[X] :=
  DetDLP_M13A_IrredHermite.polynomial ℤ
    (DetDLP_M13A_IrredHermite.findIrredPoly (4 * D3Stopped.level S))

def A_fuel (C K_loc : ℕ) : ℕ :=
  256 * (C + 1) * (K_loc + 1)

def polyToB (f : ℤ[X]) (l q : ℕ) : ℤ[X] →+* B f l q :=
  (AdjoinRoot.mk ((X : (U f q)[X]) ^ l)).comp
    (Polynomial.mapRingHom ((AdjoinRoot.of _).comp (Int.castRingHom (ZMod (2 ^ q)))))

def castU (f : ℤ[X]) (g p : ℕ) : U f (g + p) →+* U f p :=
  AdjoinRoot.lift
    ((AdjoinRoot.of _).comp (ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left p g)) (ZMod (2 ^ p))))
    (AdjoinRoot.root _)
    (by
      have hhom : ((AdjoinRoot.of (f.map (Int.castRingHom (ZMod (2 ^ p))))).comp
          (ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_left p g)) (ZMod (2 ^ p)))).comp
            (Int.castRingHom (ZMod (2 ^ (g + p)))) =
          (AdjoinRoot.of (f.map (Int.castRingHom (ZMod (2 ^ p))))).comp
            (Int.castRingHom (ZMod (2 ^ p))) :=
        RingHom.ext_int _ _
      rw [Polynomial.eval₂_map, hhom, ← Polynomial.eval₂_map]
      exact AdjoinRoot.eval₂_root _)

def castB (f : ℤ[X]) (l g p : ℕ) : B f l (g + p) →+* B f l p :=
  AdjoinRoot.lift
    ((AdjoinRoot.of _).comp (castU f g p))
    (AdjoinRoot.root _)
    (by
      rw [Polynomial.eval₂_X_pow, ← Polynomial.eval₂_X_pow
        (AdjoinRoot.of ((X : (U f p)[X]) ^ l)) (AdjoinRoot.root ((X : (U f p)[X]) ^ l))]
      exact AdjoinRoot.eval₂_root _)

def emptyStoppedSpec {C c : ℕ} (x : Input C c) (f : ℤ[X]) (deg : ℕ) :
    StoppedSpec x.G emptyGraphConst f x.l x.p deg where
  vTable w := Fin.elim0 w
  validOrig w := Fin.elim0 w
  packet w := Fin.elim0 w

structure ReattachWit {C c : ℕ} (x : Input C c) (n : ℕ)
    (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n) where
  old : Fin x.spec.lookupVerts.card ≃ ↥x.spec.lookupVerts
  rank : D4CoreCut.B x.G x.spec.lookupVerts ≃ Fin (4 * x.m * x.k)
  lp : (v : Fin x.spec.lookupVerts.card) →
    Fin (x.G.deg (old v).val) ≃ Fin ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).deg (v.castAdd n))
  rp : (j : Fin n) →
    Fin ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).deg (Fin.natAdd x.spec.lookupVerts.card j)) ≃
      {e : D4CoreCut.B x.G x.spec.lookupVerts // leafFn e = j}
  hrank : ∀ i, (rank i).val = i.val
  hlp : ∀ v i,
    D4CoreCut.origB x.G x.spec.lookupVerts
      (((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).ports (v.castAdd n)).get (lp v i)) =
    (x.G.ports (old v).val).get i
  hrp : ∀ j i, (rp j i).val =
    ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).ports (Fin.natAdd x.spec.lookupVerts.card j)).get i
  hcontr : ∀ (A : Type) [CommRing A]
    (T : (v : ↥x.spec.lookupVerts) → (Fin (x.G.deg v.val) → Bool) → A)
    (F : (j : Fin n) → ({e : D4CoreCut.B x.G x.spec.lookupVerts // leafFn e = j} → Bool) → A),
    BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn)
      (Fin.addCases (fun v t => T (old v) (fun i => t (lp v i)))
        (fun j t => F j (fun e => t ((rp j).symm e)))) =
      ∑ η : Fin (4 * x.m * x.k) → Bool,
        (∏ v : Fin x.spec.lookupVerts.card,
          T (old v) (fun i => η (rank (((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).ports (v.castAdd n)).get (lp v i))))) *
        ∏ j : Fin n, F j (fun e => η (rank e.val))

def getReattachWit {C c : ℕ} (x : Input C c) (n : ℕ)
    (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n) : ReattachWit x n leafFn :=
  let h0 := (DetDLP.d4_reattach_poly_and_spec.2 x n leafFn).2.2.2.2
  let old := Classical.choose h0
  let h1 := Classical.choose_spec h0
  let rank := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let lp := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let rp := Classical.choose h3
  let hs := Classical.choose_spec h3
  ⟨old, rank, lp, rp, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

def hitLeafFn {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (doneNodes : List (SoloNode x f PktOK))
    (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))) :
    D4CoreCut.B x.G x.spec.lookupVerts → Fin doneNodes.length :=
  fun i => Classical.choose (unique_leaf_of_pinFirsts_perm doneNodes hperm (i.cast hbLen))

def missLeafFn {C c : ℕ} (x : Input C c)
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k) :
    D4CoreCut.B x.G x.spec.lookupVerts → Fin (4 * x.m) :=
  fun i => ⟨i.val / x.k, (Nat.div_lt_iff_lt_mul x.hk).mpr (by rw [← hbLen]; exact i.isLt)⟩

structure PlanBranchData {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l)
    (q : ℕ) where
  n : ℕ
  leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n
  wVal : B f x.l q
  rightSrc : Fin n → Bits
  rightV : (j : Fin n) →
    (Fin ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).deg (Fin.natAdd x.spec.lookupVerts.card j)) → Bool) →
    B f x.l q

def HitDegProp {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (doneNodes : List (SoloNode x f PktOK))
    (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))) : Prop :=
  ∀ j : Fin doneNodes.length,
    (D4CoreCut.reattach x.G x.spec.lookupVerts doneNodes.length (hitLeafFn x hbLen doneNodes hperm)).deg
      (Fin.natAdd x.spec.lookupVerts.card j) = (doneNodes.get j).pins.length

def mkPlanBranchAux {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc : ℕ)
    (guard B_bud : ℕ) (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
    (hvalid : treeAll SoloLeafData.Valid certTree)
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
      HitDegProp x hbLen doneNodes hperm)
    (u : Fin (2 ^ B_bud)) : PlanBranchData x f (pktOKOf E_pkt o_pkt K_loc x f hf) (guard + x.p) :=
  let L := x.spec.lookupVerts
  let q := guard + x.p
  match hread : certTree.read B_bud u.val with
  | none =>
    let n := 4 * x.m
    let lfFn := missLeafFn x hbLen
    let H := D4CoreCut.reattach x.G L n lfFn
    ⟨n, lfFn, 0,
      fun _ => emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l,
      fun j β => (emptyStoppedSpec x f (H.deg (Fin.natAdd L.card j))).value hf x.A q β⟩
  | some lf =>
    have hlf : lf.Valid := treeAll_read hvalid B_bud u.val hread
    let lfFn := hitLeafFn x hbLen lf.doneNodes hlf.2.2.2
    ⟨lf.doneNodes.length, lfFn, lf.weight,
      fun j =>
        let nd := lf.doneNodes.get j
        stoppedDesc x.desc x.S x.l nd.pCurr nd.d f nd.G nd.toStoppedSpec.tableBits,
      fun j β =>
        let nd := lf.doneNodes.get j
        let hdeg := hdeg_all lf.doneNodes hlf.2.2.2 j
        nd.toStoppedSpec.value hf x.A q (fun kp => β (kp.cast hdeg.symm))⟩

def VertPortBounded {C c : ℕ} {x : Input C c} {G : BipartiteMultigraph} {f : ℤ[X]}
    {PktOK : PktPred f x.l} {pCurr dNode : ℕ} {w : Fin G.nV} (B_port : ℕ) :
    SoloVert x G f PktOK pCurr dNode w → Prop
  | .orig _ _ _ portMap _ _ => ∀ m ∈ portMap, m ≤ B_port
  | .pkt _ _ _ _ _ _ _ _ none _ => True
  | .pkt _ _ _ _ _ _ _ _ (some pm) _ => ∀ m ∈ pm, m ≤ B_port

def NodePortsBounded {C c : ℕ} {x : Input C c} {f : ℤ[X]} {PktOK : PktPred f x.l}
    (B_port : ℕ) (nd : SoloNode x f PktOK) : Prop :=
  ∀ w : Fin nd.G.nV, VertPortBounded B_port (nd.verts w)

def SoloUnrollAllPortsBounded {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} :
    (k : ℕ) → (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)) →
    SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc k nd → Prop
  | 0, nd, _ => NodePortsBounded x.S nd
  | _ + 1, nd, PSum.inl _ => NodePortsBounded x.S nd
  | k + 1, nd, PSum.inr ⟨cert, sub⟩ =>
    NodePortsBounded x.S nd ∧ ∀ ν g, SoloUnrollAllPortsBounded k (cert.childNode ν g) (sub ν g)

def callPair (s a : Wd) : Wd := DetDLP_W1_Queries.frame s ++ a

def soloCallStep (pre : Wd → Wd) (post : Wd → Wd) (w : Wd) : Wd :=
  let s := first (true :: w)
  let a := more (true :: w)
  bif a.isEmpty then false :: callPair s (pre s) else true :: post (pack [s, a])

def compExp (K₁ K₂ : ℕ) : ℕ := K₁ * (K₂ + 1) ^ K₁ + K₂ * K₁

def expSum {S l d k p : ℕ} {f : ℤ[X]} {hf : f.Monic} {z : B f l p}
    (q A : ℕ) (e : Expansion S f hf l d k p z) : B f l q :=
  ∑ r : e.Ranks, (2 : B f l q) ^ (A * D4GuardTree.slots k - Expansion.rawLossSum e r) *
    red f l q (Expansion.rawCoeff e r) * e.leaves q r

def itemExpSum {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} (hdeg : 0 < f.natDegree) (η : Fin (4 * x.m * x.k) → Bool)
    (q A : ℕ) (it : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) : B f x.l q :=
  expSum q A (SoloUnroll.toExpansion hdeg η it.1 it.2.1 it.2.2)

def planVOfBr {C c : ℕ} (x : Input C c) (f : ℤ[X]) {PktOK : PktPred f x.l}
    (guard B_bud : ℕ) (br : Fin (2 ^ B_bud) → PlanBranchData x f PktOK (guard + x.p))
    (u : Fin (2 ^ B_bud)) :
    Tensor (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn) (B f x.l (guard + x.p)) :=
  let w := getReattachWit x (br u).n (br u).leafFn
  Fin.addCases
    (fun v β => liftBase f x.l (guard + x.p) (x.A (w.old v).val (fun i => β (w.lp v i))))
    (br u).rightV

def mkSoloPlanFromBr {C c : ℕ} (x : Input C c)
    (f : ℤ[X]) (hf : f.Monic) (hdeg_f : f.natDegree = 4 * Nat.clog 2 x.S)
    (hpos : 0 < f.natDegree)
    {PktOK : PktPred f x.l}
    (guard B_bud : ℕ)
    (br : Fin (2 ^ B_bud) → PlanBranchData x f PktOK (guard + x.p))
    (hverts : ∀ u : Fin (2 ^ B_bud),
      (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).nV ≤
        4 * x.m + 64 ^ Nat.clog 32 (4 * x.m))
    (hdegree : ∀ u : Fin (2 ^ B_bud),
      (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).maxDeg * x.m ≤
        1217 * (C + 1) ^ 3 * x.b)
    (hcorrect :
      answer x = encodeNatListBin (List.ofFn fun j : Fin x.l =>
        word f x.l (guard + x.p) hf
          (∑ u : Fin (2 ^ B_bud), (br u).wVal *
            BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn)
              (planVOfBr x f guard B_bud br u))
          j ⟨0, hpos⟩ / 2 ^ guard)) :
    Plan x :=
  let L := x.spec.lookupVerts
  let q := guard + x.p
  { f := f
    hf := hf
    deg := hdeg_f
    zero := ⟨0, hpos⟩
    zero_val := rfl
    guard := guard
    N := 2 ^ B_bud
    R := fun u => D4CoreCut.reattach x.G L (br u).n (br u).leafFn
    V := planVOfBr x f guard B_bud br
    w := fun u => (br u).wVal
    source := fun u =>
      let w := getReattachWit x (br u).n (br u).leafFn
      Fin.addCases
        (fun v => lookupDesc x.desc (w.old v).val.val f.natDegree x.l q)
        (br u).rightSrc
    edges := fun u => (DetDLP.d4_reattach_poly_and_spec.2 x (br u).n (br u).leafFn).2.1
    vertices := hverts
    degree := hdegree
    correct := hcorrect }

end

end DetDLP.D4SoloPlanDefs


