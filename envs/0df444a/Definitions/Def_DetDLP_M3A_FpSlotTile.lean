-- Prove2me | Definitions.Def_DetDLP_M3A_FpSlotTile
-- name    : DetDLP_M3A_FpSlotTile
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:12:32.232905+00:00
-- url     : https://prove2.me/theorems/d9de030b-9798-49d4-95f6-133353686299
-- title:
--   W3 prime-field physical slot and uniform incidence code
-- statement:
--   Concrete linked hash slot with pinned seed, k-bit zero-extended output, unique bus extension, incidence size bound, and polynomial-time modeled endpoint code.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_FpPhysicalAtom
import Definitions.Def_DetDLP_S8L_FpPairAddresses
import Definitions.Def_DetDLP_S8H0_AnchoredLayout

set_option autoImplicit false
namespace DetDLP.M3A.FpSlotTile
open S8J S8C S8G.FpPhysicalAtom S8L.FpPair.Stage.Links S8H.PointAddresses
attribute [-simp] Fin.natAdd_eq_addNat

private abbrev anchors := S8H0.AnchoredLayout.anchors

def body (d k : ℕ) (hd : 1 ≤ d) := join (S8G.FpPhysicalAtom.layout d hd) (anchors k)

def tap {d k : ℕ} (hd : 1 ≤ d) (i : Fin (min k (d+1))) : Fin (body d k hd).nb :=
  Fin.castAdd k (port hd 3 0 ⟨i.val,lt_of_lt_of_le i.isLt (min_le_right ..)⟩)

def pad {d k : ℕ} (hd : 1 ≤ d) (i : Fin k) : Fin (body d k hd).nb :=
  Fin.natAdd (S8G.FpPhysicalAtom.layout d hd).nb i

def slotLayout (d k : ℕ) (hd : 1 ≤ d) := links (body d k hd) (tap hd)
  (fun i => pad hd (Fin.castLE (min_le_left ..) i))

def xBits {d k : ℕ} (hd : 1 ≤ d) (i : Fin d) : Fin (slotLayout d k hd).nb :=
  Fin.castAdd k (xWire hd i)

def zBits {d k : ℕ} (hd : 1 ≤ d) (i : Fin k) : Fin (slotLayout d k hd).nb := pad hd i

theorem z_injective {d k : ℕ} (hd : 1 ≤ d) : Function.Injective (@zBits d k hd) :=
  Fin.natAdd_injective ..

private def zeroPad (d k : ℕ) : w3_factorTest (anchors k) := fun g x =>
  if g.val < d+1 then true else !(x ⟨g,rfl⟩)

noncomputable def seedTest {d : ℕ} (hd : 1 ≤ d) (p T slope intercept : ℕ) :=
  atPins (atPins (S8G.FpPhysicalAtom.test d hd p (min T p)) (aWire hd) (fun j => slope.testBit j.val))
    (bWire hd) (fun j => intercept.testBit j.val)

noncomputable def slotTest {d k : ℕ} (hd : 1 ≤ d) (p T slope intercept : ℕ) :
    w3_factorTest (slotLayout d k hd) :=
  linksTest (tap hd) (fun i => pad hd (Fin.castLE (min_le_left ..) i))
    (joinTest (seedTest hd p T slope intercept) (zeroPad d k))

theorem read_low {d k : ℕ} (hd : 1 ≤ d) {p T a b : ℕ} {x : Fin (slotLayout d k hd).nb → Bool}
    (h : Accept _ (slotTest hd p T a b) x) (j : Fin (min k (d+1))) :
    x (zBits hd (Fin.castLE (min_le_left ..) j)) = x (tap hd j) :=
  ((links_iff _ _ _ _).mp h).2 j |>.symm

theorem read_high {d k : ℕ} (hd : 1 ≤ d) {p T a b : ℕ} {x : Fin (slotLayout d k hd).nb → Bool}
    (h : Accept _ (slotTest hd p T a b) x) (j : Fin k) (hj : d+1 ≤ j.val) : x (zBits hd j) = false := by
  have hz := ((join_iff _ _ _).mp ((links_iff _ _ _ _).mp h).1).2 j
  change (if j.val < d+1 then true else !(x (zBits hd j))) = true at hz
  simpa [Nat.not_lt_of_le hj] using hz

private def copyOut {d k : ℕ} (hd : 1 ≤ d) (x : Fin (S8G.FpPhysicalAtom.layout d hd).nb → Bool) (j : Fin k) :=
  if h : j.val < d+1 then x (port hd 3 0 ⟨j.val,h⟩) else false

/-- The exported bus contributes no new choice of witnesses, even when k exceeds the row width. -/
noncomputable def forgetBus {d k : ℕ} (hd : 1 ≤ d) (p T a b : ℕ) :
    {x : Fin (slotLayout d k hd).nb → Bool // Accept _ (slotTest hd p T a b) x} ≃
    {x // Accept _ (seedTest hd p T a b) x} where
  toFun x := ⟨x.1 ∘ Fin.castAdd k, ((join_iff _ _ _).mp ((links_iff _ _ _ _).mp x.2).1).1⟩
  invFun x := ⟨Fin.append x.1 (copyOut hd x.1), by
    apply (links_iff _ _ _ _).mpr
    constructor
    · apply (HashGateLayout.joined _ _ _ _).mpr
      refine ⟨x.2,?_⟩; intro g
      change (if g.val < d+1 then true else !(copyOut hd x.1 g)) = true
      by_cases h : g.val < d+1 <;> simp [copyOut,h]
    · intro i; have h := lt_of_lt_of_le i.isLt (min_le_right k (d+1))
      change Fin.append x.val (copyOut hd x.val) (Fin.castAdd k _) = Fin.append x.val (copyOut hd x.val) (Fin.natAdd _ _)
      exact (Fin.append_left x.val (copyOut hd x.val) _).trans (((dif_pos h).symm).trans (Fin.append_right x.val (@copyOut d k hd x.val) (Fin.castLE (min_le_left ..) i)).symm)⟩
  right_inv x := Subtype.ext (HashGateLayout.appendL _ _)
  left_inv x := by
    apply Subtype.ext; funext j
    induction j using Fin.addCases with
    | left j => exact Fin.append_left ..
    | right j =>
      apply (Fin.append_right (x.val ∘ Fin.castAdd k) (@copyOut d k hd _) j).trans
      by_cases hj : j.val < d+1
      · let u : Fin (min k (d+1)) := ⟨j.val,lt_min j.isLt hj⟩
        exact (dif_pos hj).trans (read_low hd x.2 u).symm
      · exact (dif_neg hj).trans (read_high hd x.2 j (Nat.le_of_not_gt hj)).symm

theorem edges {d k : ℕ} (hd : 1 ≤ d) : (slotLayout d k hd).ne < 12000*(d+3)+3*k := by
  have h := S8G.FpPhysicalAtom.edges hd
  change (S8G.FpPhysicalAtom.layout d hd).ne+k+(min k (d+1)+min k (d+1)) < _
  omega

open S8L.FpPair.Address w4_M5PortTensor Groundwork

private def splice (a : Code) (n : ℕ) (l r : ℕ → ℕ) : Code :=
  ⟨a.ng+n,a.nb,a.ne+(n+n),fun e => if e<a.ne then a.gate e else a.ng+(if e-a.ne<n then e-a.ne else e-a.ne-n),
    fun e => if e<a.ne then a.bit e else if e-a.ne<n then l (e-a.ne) else r (e-a.ne-n)⟩

private theorem splice_spec {a : Code} {A : w3_FactorLayout} {n : ℕ} (h : Models a A)
    {l r : Fin n → Fin A.nb} {f g : ℕ → ℕ} (hf : ∀ i : Fin n, f i.val = (l i).val)
    (hg : ∀ i : Fin n, g i.val = (r i).val) : Models (splice a n f g) (links A l r) := by
  refine ⟨congrArg (·+n) h.ng,h.nb,congrArg (·+(n+n)) h.ne,?_,?_⟩
  all_goals intro e; induction e using Fin.addCases with
    | left u => simp [splice,links,splitMap,h.ne,u.isLt,h.gate,h.bit]
    | right u => induction u using Fin.addCases with
      | left u => simp [splice,links,splitMap,h.ne,h.ng,u.isLt,hf]
      | right u => simp [splice,links,splitMap,h.ne,h.ng,hg]

private def addrN (d i l : ℕ) := (mul d).nb+(mul d).nb+(4*i+l)
private def outN (d i : ℕ) := w4_M5EdgeNat.edgeBase d 9 i
private def linkedCode (d : ℕ) := splice (stageCode d) (2*d+2*d)
  (fun e => if e<2*d then addrN d e 0 else addrN d (e-2*d) 2)
  (fun e => if e<2*d then (mul d).nb+outN d e else outN d (e-2*d))

private theorem addr_val {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d)) (l : Fin 4) :
    addrN d i.val l.val = (addr hd i l).val := by
  simp only [addrN,(mul_spec hd).nb]; rfl

private theorem out_val {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d)) : outN d i.val = (ext hd (outPos i)).val := by
  unfold ext; rw [ext_outPos]; rfl
private theorem input_val {d : ℕ} (hd : 1 ≤ d) (i : Fin d) (b : Bool) :
    (ext hd (inPos b i)).val = (if b then d+i.val else i.val) := by
  unfold ext; rw [ext_inPos]; cases b <;> change _ + d*_ = _ <;> simp [tag,Nat.add_comm]

private theorem linked_models {d : ℕ} (hd : 1 ≤ d) : Models (linkedCode d) (S8L.FpPair.Stage.Links.layout hd) := by
  apply splice_spec (stage_spec hd)
  · intro i; induction i using Fin.addCases with
    | left u => simpa [left,u.isLt] using addr_val hd u 0
    | right u => simpa [left] using addr_val hd u 2
  · intro i; induction i using Fin.addCases with
    | left u => simp only [right,Fin.addCases_left,Fin.val_castAdd,if_pos u.isLt]; rw [out_val hd,(mul_spec hd).nb]; rfl
    | right u => simp [right,out_val hd]; rfl

private def rowN (d j l i : ℕ) := (stageCode d).nb + (4*(i+(d+1)*j)+l)
private def eight (d : ℕ) := sum (linkedCode d) (add (8*(d+1)))
private def edgeL (d e : ℕ) :=
  if e<3*d then rowN d (if e/d=0 then 0 else if e/d=1 then 1 else 5) (if e/d<2 then 2 else 0) (e%d)
  else let t := e-3*d; let j := t/(d+1); let i := t%(d+1)
       rowN d (if j=0 then 1 else if j=1 then 3 else if j=2 then 4 else if j=3 then 5 else 7)
        (if j=0 then 2 else if j=3 then 2 else if j=4 then 1 else 0) i
private def edgeR (d e : ℕ) :=
  if e<3*d then (if e/d=0 then e%d else if e/d=1 then d+e%d else addrN d (e%d) 1)
  else let t := e-3*d; let j := t/(d+1); let i := t%(d+1)
       rowN d (if j=0 then 2 else if j=2 then 5 else 6) (if j=3 then 2 else if j=4 then 1 else 0) i
private def physCode (d : ℕ) := splice (eight d) (3*d+5*(d+1)) (edgeL d) (edgeR d)

private theorem row_val {d : ℕ} (hd : 1 ≤ d) (j : Fin 8) (l : Fin 4) (i : Fin (d+1)) :
    rowN d j.val l.val i.val = (port hd j l i).val := by
  simp only [rowN,(stage_spec hd).nb]; rfl

private theorem phys_models {d : ℕ} (hd : 1 ≤ d) : Models (physCode d) (S8G.FpPhysicalAtom.layout d hd) := by
  apply splice_spec (sum_spec (linked_models hd) (add_spec _)) <;> intro u <;> induction u using Fin.addCases with
    | left u =>
      obtain ⟨⟨j,i⟩,rfl⟩ := finProdFinEquiv.surjective u
      have div : (finProdFinEquiv (j,i)).val/d = j.val := Fin.ext_iff.mp (congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (j,i)))
      have mod : (finProdFinEquiv (j,i)).val%d = i.val := Fin.ext_iff.mp (congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (j,i)))
      simp only [edgeL,edgeR,Fin.val_castAdd,if_pos (finProdFinEquiv (j,i)).isLt,div,mod,S8G.FpPhysicalAtom.ties,Fin.addCases_left,Equiv.symm_apply_apply]
      fin_cases j <;> simp [st,mul1,← row_val hd] <;> first | exact (input_val hd i false).symm | exact (input_val hd i true).symm | exact addr_val hd ⟨i.val,by omega⟩ 1
    | right u =>
      obtain ⟨⟨j,i⟩,rfl⟩ := finProdFinEquiv.surjective u
      have div : (finProdFinEquiv (j,i)).val/(d+1) = j.val := Fin.ext_iff.mp (congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (j,i)))
      have mod : (finProdFinEquiv (j,i)).val%(d+1) = i.val := Fin.ext_iff.mp (congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (j,i)))
      simp only [edgeL,edgeR,Fin.val_natAdd,Nat.not_lt_of_ge (Nat.le_add_right ..),if_false,Nat.add_sub_cancel_left,div,mod,S8G.FpPhysicalAtom.ties,Fin.addCases_right,Equiv.symm_apply_apply]
      fin_cases j <;> simp [← row_val hd]

def slotCode (d k : ℕ) := splice (sum (physCode d) (S8H0.AnchoredLayout.anchorCode k)) (min k (d+1))
  (rowN d 3 0) (fun i => (physCode d).nb+i)

theorem slot_models {d k : ℕ} (hd : 1 ≤ d) : Models (slotCode d k) (slotLayout d k hd) := by
  apply splice_spec (sum_spec (phys_models hd) (S8H0.AnchoredLayout.anchorModels k))
  · intro i; exact row_val hd 3 0 ⟨i.val,lt_of_lt_of_le i.isLt (min_le_right ..)⟩
  · intro i; change (physCode d).nb+i.val = (S8G.FpPhysicalAtom.layout d hd).nb+i.val; rw [(phys_models hd).nb]

attribute [local fun_prop] PolyT.mul PolyT.div PolyT.mod PolyT.const PolyT.comp PolyT.id' P2M_Groundwork_PolyT_ite__226169acf219 w4_M5Evaluator.L1_poly w4_M5Evaluator.L2_poly w4_M5Evaluator.J_poly w4_M5Evaluator.n0_poly PolyT.add PolyT.sub PolyT.fst PolyT.snd PolyT.prodMk

private abbrev P1 (f : ℕ → ℕ) := ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => f (d x)
private abbrev P2 (f : ℕ → ℕ → ℕ) := ∀ {α : Type} [Enc α] {d e : α → ℕ}, PolyT d → PolyT e → PolyT fun x => f (d x) (e x)
private theorem splice_poly {a : ℕ → Code} {n : ℕ → ℕ} {l r : ℕ → ℕ → ℕ} (ha : Uniform a) (hn : P1 n) (hl : P2 l) (hr : P2 r) : Uniform (fun d => splice (a d) (n d) (l d) (r d)) := by
  constructor
  · intros; exact PolyT.add (ha.ng ‹_›) (hn ‹_›)
  · intros; exact ha.nb ‹_›
  · intros; exact PolyT.add (ha.ne ‹_›) (PolyT.add (hn ‹_›) (hn ‹_›))
  · intro α _ d e hd he; have h := ha.ne hd; have nh := hn hd; have u := PolyT.sub he h
    apply PolyT.ite' (c := fun x => e x < (a (d x)).ne) (PolyT.decide_lt he h) (ha.gate hd he) (PolyT.add (ha.ng hd) (PolyT.ite' (c := fun x => e x-(a (d x)).ne<n (d x)) (PolyT.decide_lt u nh) u (PolyT.sub u nh)))
  · intro α _ d e hd he; have h := ha.ne hd; have nh := hn hd; have u := PolyT.sub he h
    apply PolyT.ite' (c := fun x => e x < (a (d x)).ne) (PolyT.decide_lt he h) (ha.bit hd he) (PolyT.ite' (c := fun x => e x-(a (d x)).ne<n (d x)) (PolyT.decide_lt u nh) (hl hd u) (hr hd (PolyT.sub u nh)))

private theorem linked_poly : Uniform linkedCode := by
  apply splice_poly stage_poly
  · intro α _ d hd; fun_prop
  all_goals intro α _ d e hd he; have := mul_poly.nb hd; simp only [addrN,outN,w4_M5EdgeNat.edgeBase,w4_M5GraphBounds.W]; fun_prop

private theorem physical_poly : Uniform physCode := by
  apply splice_poly (sum_poly linked_poly (add_poly _ (by intros; fun_prop)))
  · intro α _ d hd; fun_prop
  all_goals intro α _ d e hd he; have hs := stage_poly.nb hd; have hm := mul_poly.nb hd; simp only [edgeL,edgeR,rowN,addrN]; fun_prop

theorem slot_uniform (k : ℕ → ℕ) (hk : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => k (d x)) : Uniform (fun d => slotCode d (k d)) := by
  have anc : Uniform (fun d => S8H0.AnchoredLayout.anchorCode (k d)) := ⟨hk,hk,hk,fun _ he => he,fun _ he => he⟩
  apply splice_poly (sum_poly physical_poly anc)
  · intro α _ d hd; have := hk hd; simp only [Nat.min_def]; fun_prop
  · intro α _ d e hd he; have := stage_poly.nb hd; simp only [rowN]; fun_prop
  · intro α _ d e hd he; exact PolyT.add (physical_poly.nb hd) he

end DetDLP.M3A.FpSlotTile
abbrev DetDLP_M3A_FpSlotTile := DetDLP.M3A.FpSlotTile.slotLayout


