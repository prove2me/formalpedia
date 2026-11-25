-- Prove2me | Definitions.Def_DetDLP_D4SoloNode
-- name    : DetDLP_D4SoloNode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T15:36:44.263831+00:00
-- url     : https://prove2.me/theorems/bf9bf225-10ba-4923-a7c2-859563b91307
-- title:
--   Solo node state, pinned open tensor, and stopped descriptor for D4 unrolling
-- statement:
--   Defines the deterministic D4 partial-unrolling node invariant `SoloNode`, its per-vertex representation `SoloVert` (original and packet vertices), the pinned open tensor `openTensor`, pin synchronization `pinSyncProp`, work-item serialization `toWorkItem`, and stopped-item descriptor `toStoppedSpec` matching `D4RankWalker.WorkItem` and `D4SoloRaw`.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Theorem 4.3 and Lemma 5.3)

import Definitions.Def_DetDLP_D4SoloRaw
import Definitions.Def_DetDLP_D4CoreCut
import Definitions.Def_DetDLP_D4StoppedNode
import Theorems.Thm_DetDLP_d4_core_cut_poly_and_spec
import Theorems.Thm_DetDLP_d4_residue_lift_eq
import Theorems.Thm_DetDLP_m14a_separator_edge_budget

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace DetDLP.D4SoloNode

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4SoloRaw
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section

section LiftLemmas

theorem encodeList_eq_pack_map {α : Type} (fn : α → List Bool) (xs : List α) :
    Encoding.encodeList fn xs = pack (xs.map fn) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (true :: Encoding.frame (fn x)) ++ Encoding.encodeList fn xs =
      (true :: Encoding.frame (fn x)) ++ pack (xs.map fn)
    rw [ih]

private theorem readCoeff {R : Type*} [CommRing R] {g : R[X]} (hg : g.Monic)
    {n : ℕ} (hn : Nontrivial R → g.natDegree = n) (b : Fin n → R) (i : Fin n) :
    (AdjoinRoot.modByMonicHom hg (AdjoinRoot.mk _ (∑ j : Fin n, monomial j.val (b j)))).coeff i = b i := by
  nontriviality R
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hg).mpr]
  · simp only [finsetSum_coeff, coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [degree_eq_natDegree hg.ne_zero, hn inferInstance]
    simp_rw [← C_mul_X_pow_eq_monomial]
    exact degree_sum_fin_lt _

private theorem readBase {R : Type*} [CommRing R] {g : R[X]} (hg : g.Monic)
    {n : ℕ} (hn : Nontrivial R → g.natDegree = n) (b : R) (i : Fin n) :
    (AdjoinRoot.modByMonicHom hg (AdjoinRoot.of _ b)).coeff i = if i.val = 0 then b else 0 := by
  nontriviality R
  rw [← AdjoinRoot.mk_C, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hg).mpr, coeff_C]
  apply degree_C_le.trans_lt
  rw [degree_eq_natDegree hg.ne_zero, hn inferInstance]
  exact_mod_cast Nat.zero_lt_of_lt i.isLt

theorem word_eq_of_residue_eq {f : ℤ[X]} {l p₁ p₂ : ℕ} {hf : f.Monic}
    {x : B f l p₁} {y : B f l p₂}
    (hres : residue f l p₁ hf x = residue f l p₂ hf y)
    (j : Fin l) (i : Fin f.natDegree) :
    word f l p₁ hf x j i = word f l p₂ hf y j i := by
  have hdec := congrArg ints hres
  simp only [residue, ints_encodeNatListBin] at hdec
  let k : Fin (l * f.natDegree) := finProdFinEquiv (j, i)
  have hk := congrArg (fun xs : List ℕ => xs[k.val]?) hdec
  simp only [List.getElem?_ofFn, k.isLt, ↓reduceDIte, Option.some.injEq] at hk
  have hsymm : finProdFinEquiv.symm k = (j, i) := finProdFinEquiv.symm_apply_apply (j, i)
  rw [hsymm] at hk
  exact hk

theorem word_lift_of_le {f : ℤ[X]} {l p₁ p₂ : ℕ} (hf : f.Monic) (hp : p₁ ≤ p₂)
    (z : B f l p₁) (j : Fin l) (i : Fin f.natDegree) :
    word f l p₂ hf (lift hf p₂ z) j i = word f l p₁ hf z j i :=
  word_eq_of_residue_eq ((d4_residue_lift_eq f l p₁ p₂ hf hp).1 z) j i

theorem lift_lift_of_le {f : ℤ[X]} {l p₁ p₂ : ℕ} (hf : f.Monic) (hp : p₁ ≤ p₂)
    (q : ℕ) (z : B f l p₁) :
    lift hf q (lift hf p₂ z) = lift hf q z := by
  let y := lift hf p₂ z
  have hy : ∀ j i, word f l p₂ hf y j i = word f l p₁ hf z j i :=
    fun j i => word_lift_of_le hf hp z j i
  change lift hf q y = lift hf q z
  unfold lift
  congr 1; apply Finset.sum_congr rfl; intro j _
  congr 2; apply Finset.sum_congr rfl; intro i _
  rw [hy j i]

theorem lift_liftBase_of_le {f : ℤ[X]} {l p₁ p₂ : ℕ} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (_hp : p₁ ≤ p₂) (a : Fin l → ℕ) (ha : ∀ j, a j < 2 ^ p₁) :
    lift hf p₂ (liftBase f l p₁ a) = liftBase f l p₂ a := by
  unfold lift liftBase
  congr 1; apply Finset.sum_congr rfl; intro j _
  congr 1
  have hw (i : Fin f.natDegree) :
      word f l p₁ hf (AdjoinRoot.mk _ (∑ k : Fin l, monomial k.val (AdjoinRoot.of _ (a k : ZMod (2 ^ p₁))))) j i =
        if i.val = 0 then a j else 0 := by
    unfold word
    rw [readCoeff (monic_X_pow l) (fun _ => natDegree_X_pow l),
        readBase (hf.map _) (fun _ => hf.natDegree_map _)]
    split_ifs with hi
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ha j)]
    · simp
  simp only [hw]
  let i0 : Fin f.natDegree := ⟨0, hdeg⟩
  have hsum : (∑ i : Fin f.natDegree,
      monomial i.val (((if i.val = 0 then a j else 0 : ℕ) : ZMod (2 ^ p₂)))) =
      C (a j : ZMod (2 ^ p₂)) := by
    rw [Finset.sum_eq_single i0]
    · simp [i0]
    · intro i _ hne
      have hi0 : i.val ≠ 0 := fun h0 => hne (Fin.ext h0)
      simp [hi0]
    · intro hmem; exact False.elim (hmem (Finset.mem_univ i0))
  rw [hsum, AdjoinRoot.mk_C]

end LiftLemmas

section VertexAndNode

abbrev PktPred (f : ℤ[X]) (l : ℕ) :=
  ℕ → ∀ (pCreate origDeg : ℕ), Bits → ((Fin origDeg → Bool) → B f l pCreate) → Prop

inductive SoloVert {C c : ℕ} (x : Input C c) (G : BipartiteMultigraph) (f : ℤ[X])
    (PktOK : PktPred f x.l) (pCurr : ℕ) (dNode : ℕ) (w : Fin G.nV) where
  | orig (v₀ : Fin x.G.nV) (hv₀ : v₀ ∉ x.spec.lookupVerts)
      (pinPort : Option (Fin (x.G.deg v₀)))
      (portMap : List ℕ)
      (hlen : portMap.length = x.G.deg v₀)
      (hports : ∀ r : Fin (x.G.deg v₀), pinPort ≠ some r → portMap.getD r.val 0 < G.deg w)
  | pkt (_dCreate pCreate origDeg : ℕ)
      (rawDesc : Bits)
      (hdLt : _dCreate < dNode)
      (hpLe : pCreate ≤ pCurr)
      (entry₀ : (Fin origDeg → Bool) → B f x.l pCreate)
      (hpkt : PktOK _dCreate pCreate origDeg rawDesc entry₀)
      (permOpt : Option (List ℕ))
      (hperm : match permOpt with
        | none => origDeg = G.deg w
        | some pm => pm.length = origDeg ∧ ∀ i : Fin origDeg, pm.getD i.val 0 < G.deg w)

namespace SoloVert

variable {C c : ℕ} {x : Input C c} {G : BipartiteMultigraph} {f : ℤ[X]}
  {PktOK : PktPred f x.l} {pCurr dNode : ℕ} {w : Fin G.nV}

def pinCode {n : ℕ} (pinPort : Option (Fin n)) : ℕ :=
  pinPort.elim 0 (fun r => r.val + 1)

def specBits : SoloVert x G f PktOK pCurr dNode w → Wd
  | .orig v₀ _ pinPort portMap _ _ =>
    pack [[false], encodeNatListBin [v₀.val, x.G.deg v₀, pinCode pinPort], encodeNatListBin portMap]
  | .pkt _ _ _ rawDesc _ _ _ _ none _ =>
    pack [[true], rawDesc]
  | .pkt _ _ _ rawDesc _ _ _ _ (some pm) _ =>
    pack [[true], rawDesc, encodeNatListBin pm]

def eval (hf : f.Monic) (pinBit : Bool) (sv : SoloVert x G f PktOK pCurr dNode w)
    (β : Fin (G.deg w) → Bool) : B f x.l pCurr :=
  match sv with
  | .orig v₀ _ pinPort portMap _ hports =>
    liftBase f x.l pCurr (x.A v₀ (fun r =>
      if h : pinPort = some r then pinBit
      else β ⟨portMap.getD r.val 0, hports r h⟩))
  | .pkt _ _ _ _ _ _ entry₀ _ none hperm =>
    lift hf pCurr (entry₀ (fun i => β (i.cast hperm)))
  | .pkt _ _ _ _ _ _ entry₀ _ (some pm) hperm =>
    lift hf pCurr (entry₀ (fun i => β ⟨pm.getD i.val 0, hperm.2 i⟩))

def toVertexSpec (pinPos : ℕ) : SoloVert x G f PktOK pCurr dNode w → VertexSpec
  | .orig v₀ _ pinPort portMap _ _ =>
    let routed := (List.range (x.G.deg v₀)).map fun r =>
      if pinCode pinPort = r + 1 then (true, pinPos) else (false, portMap.getD r 0)
    .orig v₀.val routed
  | .pkt _ _ _ rawDesc _ _ _ _ none _ =>
    .pkt (pack [rawDesc, []])
  | .pkt _ _ _ rawDesc _ _ _ _ (some pm) _ =>
    .pkt (pack [rawDesc, encodeNatListBin pm])

def toPacket (pinPos : ℕ) (sv : SoloVert x G f PktOK pCurr dNode w) (d : Bits)
    (h : sv.toVertexSpec pinPos = .pkt d) : Packet f x.l pCurr (G.deg w) :=
  match sv, h with
  | .orig _ _ _ _ _ _, h => nomatch h
  | .pkt _ pCreate _ _ _ hpLe entry₀ _ none hperm, _ =>
    ⟨pCreate, hpLe, fun β => entry₀ (fun i => β (i.cast hperm))⟩
  | .pkt _ pCreate _ _ _ hpLe entry₀ _ (some pm) hperm, _ =>
    ⟨pCreate, hpLe, fun β => entry₀ (fun i => β ⟨pm.getD i.val 0, hperm.2 i⟩)⟩

def isOrigPinOk (openDeg pinPos : ℕ) : SoloVert x G f PktOK pCurr dNode w → Prop
  | .orig _ _ pinPort _ _ _ => pinPort.isSome → pinPos < openDeg
  | .pkt _ _ _ _ _ _ _ _ _ _ => True

theorem validOrig_of_pinPos {openDeg pinPos : ℕ} (sv : SoloVert x G f PktOK pCurr dNode w)
    (hpinLt : sv.isOrigPinOk openDeg pinPos)
    (v : ℕ) (perm : List (Bool × ℕ)) (hv : sv.toVertexSpec pinPos = .orig v perm) :
    ∃ hv' : v < x.G.nV, perm.length = x.G.deg ⟨v, hv'⟩ ∧
      ∀ r ∈ perm, r.2 < (if r.1 then openDeg else G.deg w) := by
  cases sv with
  | pkt _ _ _ _ _ _ _ _ permOpt _ =>
    cases permOpt <;> nomatch hv
  | orig v₀ hv₀ pinPort portMap hlen hports =>
    simp only [toVertexSpec, VertexSpec.orig.injEq] at hv
    rcases hv with ⟨rfl, rfl⟩
    refine ⟨v₀.isLt, by simp, ?_⟩
    intro rt hrt
    simp only [List.mem_map, List.mem_range] at hrt
    rcases hrt with ⟨r, hr, rfl⟩
    by_cases hmatch : pinCode pinPort = r + 1
    · simp only [hmatch, ↓reduceIte]
      exact hpinLt (by cases pinPort <;> simp [pinCode] at hmatch ⊢)
    · simp only [hmatch, ↓reduceIte]
      exact hports ⟨r, hr⟩ (by intro heq; subst heq; simp [pinCode] at hmatch)

private theorem getD_ofFn_fin {n : ℕ} (g : Fin n → ℕ) (j : ℕ) (hj : j < n) :
    (List.ofFn g).getD j 0 = g ⟨j, hj⟩ := by
  have hlen : j < (List.ofFn g).length := by simp [hj]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_ofFn, Option.getD_some]

private theorem getD_map_nat (xs : List ℕ) (fn : ℕ → ℕ) (r : ℕ) (hr : r < xs.length) :
    (xs.map fn).getD r 0 = fn (xs.getD r 0) := by
  have hlen : r < (xs.map fn).length := by simp [hr]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_map,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  rfl

def pushChild {G' : BipartiteMultigraph} {w' : Fin G'.nV} (p' : ℕ) (hp' : pCurr ≤ p')
    (pe : Fin (G.deg w) ≃ Fin (G'.deg w'))
    (sv : SoloVert x G f PktOK pCurr dNode w) : SoloVert x G' f PktOK p' (dNode + 1) w' :=
  let permList := List.ofFn (fun j : Fin (G.deg w) => (pe j).val)
  match sv with
  | .orig v₀ hv₀ pinPort portMap hlen hports =>
    .orig v₀ hv₀ pinPort (portMap.map fun j => permList.getD j 0) (by simp [hlen]) (by
      intro r hr
      have hr_lt : r.val < portMap.length := by rw [hlen]; exact r.isLt
      have hj : portMap.getD r.val 0 < G.deg w := hports r hr
      rw [getD_map_nat portMap _ r.val hr_lt, getD_ofFn_fin _ _ hj]
      exact (pe ⟨portMap.getD r.val 0, hj⟩).isLt)
  | .pkt dCreate pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt none hperm =>
    .pkt dCreate pCreate origDeg rawDesc (Nat.lt_succ_of_lt hdLt) (hpLe.trans hp') entry₀ hpkt (some permList) (by
      dsimp only
      refine ⟨by simp [permList, hperm], fun i => ?_⟩
      have hi : i.val < G.deg w := by rw [← hperm]; exact i.isLt
      rw [getD_ofFn_fin _ _ hi]
      exact (pe ⟨i.val, hi⟩).isLt)
  | .pkt dCreate pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt (some pm) hperm =>
    .pkt dCreate pCreate origDeg rawDesc (Nat.lt_succ_of_lt hdLt) (hpLe.trans hp') entry₀ hpkt
      (some (pm.map fun j => permList.getD j 0)) (by
      dsimp only at hperm ⊢
      refine ⟨by simp [hperm.1], fun i => ?_⟩
      have hi_lt : i.val < pm.length := by rw [hperm.1]; exact i.isLt
      have hj : pm.getD i.val 0 < G.deg w := hperm.2 i
      rw [getD_map_nat pm _ i.val hi_lt, getD_ofFn_fin _ _ hj]
      exact (pe ⟨pm.getD i.val 0, hj⟩).isLt)

theorem pushChild_specBits {G' : BipartiteMultigraph} {w' : Fin G'.nV} (p' : ℕ) (hp' : pCurr ≤ p')
    (pe : Fin (G.deg w) ≃ Fin (G'.deg w'))
    (sv : SoloVert x G f PktOK pCurr dNode w) :
    (sv.pushChild p' hp' pe).specBits =
      mapped sv.specBits (encodeNatListBin (List.ofFn fun j => (pe j).val)) := by
  cases sv with
  | orig v₀ hv₀ pinPort portMap hlen hports =>
    simp [pushChild, specBits, mapped, unpack_pack, ints_encodeNatListBin]
  | pkt dCreate pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt permOpt hperm =>
    cases permOpt with
    | none =>
      simp [pushChild, specBits, mapped, unpack_pack]
    | some pm =>
      simp [pushChild, specBits, mapped, unpack_pack, ints_encodeNatListBin]

theorem pushChild_eval {G' : BipartiteMultigraph} {w' : Fin G'.nV} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hp₁ : x.p ≤ pCurr) (p' : ℕ) (hp' : pCurr ≤ p')
    (pe : Fin (G.deg w) ≃ Fin (G'.deg w'))
    (pinBit : Bool) (sv : SoloVert x G f PktOK pCurr dNode w)
    (β' : Fin (G'.deg w') → Bool) :
    (sv.pushChild p' hp' pe).eval hf pinBit β' =
      lift hf p' (sv.eval hf pinBit (β' ∘ pe)) := by
  have ha_lt : ∀ v t i, x.A v t i < 2 ^ pCurr :=
    fun v t i => (x.bounded v t i).trans_le (Nat.pow_le_pow_right (by decide) hp₁)
  cases sv with
  | orig v₀ hv₀ pinPort portMap hlen hports =>
    simp only [pushChild, eval]
    rw [lift_liftBase_of_le hf hdeg hp' _ (ha_lt v₀ _)]
    congr 2
    funext r
    split_ifs with hr
    · rfl
    · simp only [Function.comp_apply]
      congr 1
      apply Fin.ext
      simp only
      have hr_lt : r.val < portMap.length := by rw [hlen]; exact r.isLt
      have hj : portMap.getD r.val 0 < G.deg w := hports r hr
      rw [getD_map_nat portMap _ r.val hr_lt, getD_ofFn_fin _ _ hj]
  | pkt dCreate pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt permOpt hperm =>
    cases permOpt with
    | none =>
      simp only [pushChild, eval]
      rw [lift_lift_of_le hf hpLe p']
      congr 2
      funext i
      simp only [Function.comp_apply]
      congr 1
      apply Fin.ext
      simp only
      have hi : i.val < G.deg w := by rw [← hperm]; exact i.isLt
      rw [getD_ofFn_fin _ _ hi]
      rfl
    | some pm =>
      dsimp only at hperm
      simp only [pushChild, eval]
      rw [lift_lift_of_le hf hpLe p']
      congr 2
      funext i
      simp only [Function.comp_apply]
      congr 1
      apply Fin.ext
      simp only
      have hi_lt : i.val < pm.length := by rw [hperm.1]; exact i.isLt
      have hj : pm.getD i.val 0 < G.deg w := hperm.2 i
      rw [getD_map_nat pm _ i.val hi_lt, getD_ofFn_fin _ _ hj]

end SoloVert

def pinSyncProp {C c : ℕ} {x : Input C c} {G : BipartiteMultigraph} {f : ℤ[X]}
    {PktOK : PktPred f x.l} {pCurr dNode : ℕ}
    (pins : List (Fin (4 * x.m * x.k) × Fin G.nV)) (w : Fin G.nV) :
    SoloVert x G f PktOK pCurr dNode w → Prop
  | .orig _ _ pinPort _ _ _ => pinPort.isSome ↔ ∃ k : Fin pins.length, (pins.get k).2 = w
  | .pkt _ _ _ _ _ _ _ _ _ _ => ∀ k : Fin pins.length, (pins.get k).2 ≠ w

structure SoloNode {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) where
  d : ℕ
  G : BipartiteMultigraph
  pCurr : ℕ
  pins : List (Fin (4 * x.m * x.k) × Fin G.nV)
  pins_sorted : pins.Pairwise (fun a b => a.1.val < b.1.val)
  host_inj : ∀ k₁ k₂ : Fin pins.length, (pins.get k₁).2 = (pins.get k₂).2 → k₁ = k₂
  pinned_deg_pos : ∀ k : Fin pins.length, 1 ≤ G.deg (pins.get k).2
  pins_len_le : pins.length ≤ (4 * x.m * x.k) / 32 ^ d + 31 * (D3Stopped.level x.S + 2)
  verts : (w : Fin G.nV) → SoloVert x G f PktOK pCurr d w
  pin_sync : ∀ w : Fin G.nV, pinSyncProp pins w (verts w)
  hp_ge : x.p ≤ pCurr
  hp_le : pCurr ≤ x.p + (if d = 0 then 0 else 80 * x.S * 2 ^ D3Stopped.shift x.S (d - 1))
  edges_le : G.nE ≤ x.S / 8 ^ d
  verts_le : G.nV ≤ x.G.nV + d * (3 * x.S)
  deg_le : G.maxDeg ≤ max (C * Nat.ceil ((x.b : ℝ) ^ ((3 : ℝ) / 4)))
    (if d = 0 then 0 else 2 * 2 ^ D3Stopped.shift x.S (d - 1))

namespace SoloNode

variable {C c : ℕ} {x : Input C c} {f : ℤ[X]} {PktOK : PktPred f x.l}

def host (nd : SoloNode x f PktOK) (k : Fin nd.pins.length) : Fin nd.G.nV :=
  (nd.pins.get k).2

def pinPosOf (nd : SoloNode x f PktOK) (w : Fin nd.G.nV) : ℕ :=
  findPinPos (nd.pins.map fun pv => encodeNatListBin [pv.1.val, pv.2.val]) w.val

def toWorkItem (nd : SoloNode x f PktOK) : WorkItem where
  depth := nd.d
  G := nd.G
  pins := nd.pins.map (fun pv => (pv.1.val, pv.2))
  pCurr := nd.pCurr
  vSpecs := fun w => (nd.verts w).specBits

theorem host_card_le_one (nd : SoloNode x f PktOK) (z : Fin nd.pins.length) :
    (Finset.univ.filter fun y : Fin nd.pins.length => nd.host z = nd.host y).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact (nd.host_inj z a ha).symm.trans (nd.host_inj z b hb)

def openTensor (hf : f.Monic) (nd : SoloNode x f PktOK) :
    OpenTensor nd.host (B f x.l nd.pCurr) :=
  fun w β pinFn =>
    let pinBit : Bool :=
      if h : ∃ k : Fin nd.pins.length, nd.host k = w then
        pinFn ⟨Classical.choose h, Classical.choose_spec h⟩
      else false
    (nd.verts w).eval hf pinBit β

theorem findPinPos_eq_unique (nd : SoloNode x f PktOK) (k : Fin nd.pins.length) :
    nd.pinPosOf (nd.host k) = k.val := by
  unfold pinPosOf findPinPos
  let ps := nd.pins.map fun pv => encodeNatListBin [pv.1.val, pv.2.val]
  have hlen : ps.length = nd.pins.length := List.length_map _
  have hpred : ∀ idx < nd.pins.length,
      decide ((ints (ps.getD idx [])).getD 1 0 = (nd.host k).val) = decide (idx = k.val) := by
    intro idx hidx
    have hidx_ps : idx < ps.length := hlen.symm ▸ hidx
    have hget : ps.getD idx [] = encodeNatListBin [(nd.pins.get ⟨idx, hidx⟩).1.val, (nd.pins.get ⟨idx, hidx⟩).2.val] := by
      simp [ps, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_ps, List.getElem_map]
    rw [hget, ints_encodeNatListBin]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    apply decide_eq_decide.mpr
    constructor
    · intro hv
      have heq := nd.host_inj ⟨idx, hidx⟩ k (Fin.ext hv)
      exact congrArg Fin.val heq
    · intro hi
      have hfin : (⟨idx, hidx⟩ : Fin nd.pins.length) = k := Fin.ext hi
      rw [hfin]; rfl
  have hfl : (List.range ps.length).filter
      (fun idx => decide ((ints (ps.getD idx [])).getD 1 0 = (nd.host k).val)) = [k.val] := by
    rw [hlen]
    have hcongr : (List.range nd.pins.length).filter
        (fun idx => decide ((ints (ps.getD idx [])).getD 1 0 = (nd.host k).val)) =
        (List.range nd.pins.length).filter (fun idx => decide (idx = k.val)) := by
      apply List.filter_congr
      intro idx hmem
      exact hpred idx (List.mem_range.mp hmem)
    rw [hcongr]
    have hsplit : List.range nd.pins.length =
        List.range k.val ++ (k.val :: ((List.range (nd.pins.length - (k.val + 1))).map (· + (k.val + 1)))) := by
      apply List.ext_getElem
      · simp; omega
      · intro m hm₁ hm₂
        rw [List.getElem_range]
        by_cases hmk : m < k.val
        · rw [List.getElem_append_left (by simpa using hmk), List.getElem_range]
        · rw [List.getElem_append_right (by simpa using hmk)]
          simp only [List.length_range]
          by_cases hmeq : m - k.val = 0
          · have : m = k.val := by omega
            subst this; simp
          · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hmeq
            simp [ht]; omega
    rw [hsplit, List.filter_append, List.filter_cons]
    have h1 : (List.range k.val).filter (fun idx => decide (idx = k.val)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha; have := List.mem_range.mp ha; simp; omega
    have h2 : (List.map (· + (k.val + 1)) (List.range (nd.pins.length - (k.val + 1)))).filter
        (fun idx => decide (idx = k.val)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      rcases List.mem_map.mp ha with ⟨t, _, rfl⟩
      simp; omega
    simp [h1, h2]
  rw [hfl]; rfl

theorem vert_origPinOk (nd : SoloNode x f PktOK) (w : Fin nd.G.nV) :
    (nd.verts w).isOrigPinOk nd.pins.length (nd.pinPosOf w) := by
  have hs := nd.pin_sync w
  revert hs
  generalize nd.verts w = sv
  intro hs
  cases sv with
  | pkt _ _ _ _ _ _ _ _ _ _ => trivial
  | orig v₀ hv₀ pinPort portMap hlen hports =>
    intro hsome
    rcases hs.mp hsome with ⟨k, hk⟩
    have hw_eq : w = nd.host k := hk.symm
    rw [hw_eq, findPinPos_eq_unique nd k]
    exact k.isLt

def toStoppedSpec (nd : SoloNode x f PktOK) :
    StoppedSpec x.G nd.G f x.l nd.pCurr nd.pins.length where
  vTable w := (nd.verts w).toVertexSpec (nd.pinPosOf w)
  validOrig w v perm hv := (nd.verts w).validOrig_of_pinPos (nd.vert_origPinOk w) v perm hv
  packet w d hv := (nd.verts w).toPacket (nd.pinPosOf w) d hv

theorem toStoppedSpec_entry_eq (hf : f.Monic) (nd : SoloNode x f PktOK)
    (α : Fin nd.pins.length → Bool) :
    nd.toStoppedSpec.entry hf x.A α = pin (nd.openTensor hf) α := by
  funext w β
  have hgen : ∀ (sv : SoloVert x nd.G f PktOK nd.pCurr nd.d w)
      (hpin : pinSyncProp nd.pins w sv)
      (hpinLt : sv.isOrigPinOk nd.pins.length (nd.pinPosOf w)),
      (match h : sv.toVertexSpec (nd.pinPosOf w) with
        | .orig v perm =>
          let hv := (sv.validOrig_of_pinPos hpinLt v perm h).choose
          let bits := routedBits perm (List.ofFn α) (List.ofFn β)
          liftBase f x.l nd.pCurr (x.A ⟨v, hv⟩ (fun j => bits[j.val]?.getD false))
        | .pkt d =>
          lift hf nd.pCurr ((sv.toPacket (nd.pinPosOf w) d h).entry β)) =
      sv.eval hf (if hex : ∃ k : Fin nd.pins.length, nd.host k = w then
        α (Classical.choose hex) else false) β := by
    intro sv hpin hpinLt
    cases sv with
    | orig v₀ hv₀ pinPort portMap hlen hports =>
      cases v₀ with
      | mk v₀val v₀lt =>
      have hv_choose : ((SoloVert.orig ⟨v₀val, v₀lt⟩ hv₀ pinPort portMap hlen hports).validOrig_of_pinPos
          hpinLt v₀val _ rfl).choose = v₀lt := Subsingleton.elim _ _
      change liftBase f x.l nd.pCurr (x.A ⟨v₀val, _⟩ (fun r => (routedBits _ (List.ofFn α) (List.ofFn β))[r.val]?.getD false)) =
        liftBase f x.l nd.pCurr (x.A ⟨v₀val, v₀lt⟩ (fun r =>
          if h : pinPort = some r then
            if hex : ∃ k : Fin nd.pins.length, nd.host k = w then α (Classical.choose hex) else false
          else β ⟨portMap.getD r.val 0, hports r h⟩))
      rw [hv_choose]
      congr 2
      funext r
      have hr_len : r.val < ((List.range (x.G.deg ⟨v₀val, v₀lt⟩)).map (fun r' =>
          if SoloVert.pinCode pinPort = r' + 1 then (true, nd.pinPosOf w)
          else (false, portMap.getD r' 0))).length := by simp [r.isLt]
      have hbit : (routedBits
          ((List.range (x.G.deg ⟨v₀val, v₀lt⟩)).map fun r' =>
            if SoloVert.pinCode pinPort = r' + 1 then (true, nd.pinPosOf w)
            else (false, portMap.getD r' 0))
          (List.ofFn α) (List.ofFn β))[r.val]?.getD false =
          (let rt := if SoloVert.pinCode pinPort = r.val + 1 then (true, nd.pinPosOf w)
            else (false, portMap.getD r.val 0)
           (if rt.1 then List.ofFn α else List.ofFn β)[rt.2]?.getD false) := by
        unfold routedBits
        rw [List.getElem?_map, List.getElem?_eq_getElem hr_len]
        simp
      rw [hbit]
      by_cases hpr : pinPort = some r
      · have hcode : SoloVert.pinCode pinPort = r.val + 1 := by rw [hpr]; rfl
        rw [dif_pos hpr, if_pos hcode]
        dsimp only
        rw [if_pos rfl]
        have hex : ∃ k : Fin nd.pins.length, nd.host k = w := hpin.mp (by rw [hpr]; rfl)
        rw [dif_pos hex]
        let k₀ := Classical.choose hex
        have hk₀ : nd.host k₀ = w := Classical.choose_spec hex
        have hpos_eq : nd.pinPosOf w = k₀.val := by rw [← hk₀, findPinPos_eq_unique nd k₀]
        rw [hpos_eq]
        have hk_lt : k₀.val < (List.ofFn α).length := by simp [k₀.isLt]
        rw [List.getElem?_eq_getElem hk_lt, List.getElem_ofFn, Option.getD_some]
      · have hneq : ¬(SoloVert.pinCode pinPort = r.val + 1) := by
          cases pinPort with
          | none => simp [SoloVert.pinCode]
          | some r₀ =>
            simp only [SoloVert.pinCode, Option.elim_some]
            intro hh; apply hpr; congr 1; apply Fin.ext; omega
        rw [dif_neg hpr, if_neg hneq]
        dsimp only
        rw [if_neg Bool.false_ne_true]
        have hj : portMap.getD r.val 0 < nd.G.deg w := hports r hpr
        have hj_lt : portMap.getD r.val 0 < (List.ofFn β).length := by rw [List.length_ofFn]; exact hj
        rw [List.getElem?_eq_getElem hj_lt, List.getElem_ofFn, Option.getD_some]
    | pkt dCreate pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt permOpt hperm =>
      cases permOpt <;> rfl
  unfold StoppedSpec.entry pin openTensor
  dsimp only [toStoppedSpec]
  exact hgen (nd.verts w) (nd.pin_sync w) (nd.vert_origPinOk w)

theorem toStoppedSpec_desc_eq (fuel : List Unit) (nd : SoloNode x f PktOK)
    (hfuel : ∀ v₀ : Fin x.G.nV, x.G.deg v₀ ≤ fuel.length) :
    stoppedItemDescRaw fuel x.desc (polynomialBits f) x.S x.l nd.toWorkItem.bits =
      stoppedDesc x.desc x.S x.l nd.pCurr nd.d f nd.G nd.toStoppedSpec.tableBits := by
  unfold stoppedItemDescRaw stoppedDesc D3Stopped.descOf StoppedSpec.tableBits toWorkItem WorkItem.bits
  simp only [fld_pack, num, List.getD_cons_zero, List.getD_cons_succ, num_countWord,
    unpack_pack, List.length_ofFn, List.map_map]
  congr 1; congr 1; congr 2; congr 2; congr 2; congr 2; congr 2; congr 2
  rw [encodeList_eq_pack_map]
  apply congrArg pack
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intro wIdx hw₁ hw₂
    have hw_lt : wIdx < nd.G.nV := by simpa only [List.length_map, List.length_range] using hw₁
    let w : Fin nd.G.nV := ⟨wIdx, hw_lt⟩
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hget : (List.ofFn fun u : Fin nd.G.nV => (nd.verts u).specBits).getD wIdx [] = (nd.verts w).specBits := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hw_lt]), List.getElem_ofFn, Option.getD_some]
    unfold convertVertexRaw
    rw [hget]
    dsimp only [toStoppedSpec, pinPosOf]
    generalize nd.verts w = sv
    cases sv with
    | orig v₀ hv₀ pinPort portMap hlen hports =>
      simp only [SoloVert.specBits, SoloVert.toVertexSpec, fld_pack, List.getD_cons_zero,
        List.getD_cons_succ, List.headD_cons, Bool.false_eq_true, ↓reduceIte,
        ints_encodeNatListBin, VertexSpec.bits, rangeFuel_eq fuel (x.G.deg v₀) (hfuel v₀),
        encodeList_eq_pack_map, List.map_map]
      congr 2; congr 1; congr 2; congr 1
      funext r
      by_cases hm : SoloVert.pinCode pinPort = r + 1
      · simp [hm]; rfl
      · simp [hm]
    | pkt _ pCreate origDeg rawDesc hdLt hpLe entry₀ hpkt permOpt hperm =>
      cases permOpt with
      | none =>
        simp only [SoloVert.specBits, SoloVert.toVertexSpec, VertexSpec.bits,
          fld_pack, unpack_pack, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, ↓reduceIte,
          List.length_cons, List.length_nil]
        have h2 : 2 < 3 := by omega
        simp [h2]
      | some pm =>
        simp only [SoloVert.specBits, SoloVert.toVertexSpec, VertexSpec.bits,
          fld_pack, unpack_pack, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, ↓reduceIte,
          List.length_cons, List.length_nil]
        simp

end SoloNode

end VertexAndNode

end

end DetDLP.D4SoloNode


