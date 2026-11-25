-- Prove2me | Definitions.Def_DetDLP_S8H_MakeCombinators
-- name    : DetDLP_S8H_MakeCombinators
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:58:51.743198+00:00
-- url     : https://prove2.me/theorems/06908466-ee89-458d-9f86-7fdf41a00be2
-- title:
--   Public reusable NC make-packet combinators for register networks
-- statement:
--   Let $c=(A,\nu)$ consist of a layout address code and a signal-name function. The relation `Fits` asserts that $A$ models the named block and that $\nu$ agrees with its name on each valid edge. Binary concatenation preserves `Fits`. For a family indexed by $0,\ldots,n$, `manyN_spec` identifies concatenation with `RangeRows.many`; `manyN_poly` gives uniform polynomial-time access when $n$ is unary and the component family is uniformly efficient. A separate fixed-bound theorem requires only slotwise efficiency.
--
--   The row, column, scan, and product specifications give elementary block constructions; `genHash_spec` assembles two products and three addition blocks into `HashRows.block`. Finally, `fullMake_spec` identifies the output word with the BTN encoding of the subdivided factor graph at parameters $(s,s,1)$. The theorem `fullMake_poly` uses an efficiently generated list whose length bounds both packet enumerations.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_BaseCode
import Definitions.Def_DetDLP_S8C3_Routes
import Definitions.Def_DetDLP_S8H_WirePacket
set_option autoImplicit false
namespace DetDLP.S8H.MakeCombinators
open S8H0 RegisterMap NamedBlocks GateSemantics PointAddresses S8C S8C3 Groundwork M89S1
abbrev NC := Code × (ℕ → ℕ)
def catN (a b : NC) : NC := (sum a.1 b.1, fun i => if i < a.1.ne then a.2 i else b.2 (i-a.1.ne))
def Fits {k : ℕ} (c : NC) (b : B k) := Models c.1 b.core.A ∧ ∀ i : Fin b.core.A.ne, c.2 i = (b.name i).val
theorem cat_spec {k : ℕ} {a b : NC} {u v : B k} (h : Fits a u) (j : Fits b v) : Fits (catN a b) (joinB u v) := by
  refine ⟨sum_spec h.1 j.1,fun i => ?_⟩; induction i using Fin.addCases with
  | left i => simp [catN,joinB,h.1.ne,i.isLt,h.2]
  | right i => simp [catN,joinB,h.1.ne,j.2]
def offset (n : ℕ) (f : ℕ → ℕ) (k : ℕ) := (((List.range n).map f).take k).sum
theorem offset_step (n k : ℕ) (f : ℕ → ℕ) : offset (n+1) f (k+1) = f 0 + offset n (fun j => f (j+1)) k := by simp [offset,List.range_succ_eq_map,List.map_map,Function.comp_def]
/-- Count completed blocks, excluding the last so that all natural indices have a local address. -/
def slot (n : ℕ) (e : ℕ → ℕ) (i : ℕ) := ((List.range n).filter fun j => decide (offset (n+1) e (j+1) ≤ i)).length
theorem slot_step (n i : ℕ) (e : ℕ → ℕ) : slot (n+1) e i = if i<e 0 then 0 else slot n (fun j => e (j+1)) (i-e 0)+1 := by
  unfold slot; rw [List.range_succ_eq_map]; simp only [List.filter_cons,List.filter_map,Function.comp_def,offset_step]; by_cases h : i<e 0
  · simp [h,offset,show ¬ e 0 ≤ i by omega]; intros; omega
  · have he (v : ℕ) : e 0 + v ≤ i ↔ v ≤ i-e 0 := by omega
    simp [h,he,offset,show e 0 ≤ i by omega]
/-- Concatenate the nonempty family of blocks numbered `0` through `n`, inclusively. -/
def manyN (n : ℕ) (f : ℕ → NC) : NC :=
  let off := fun (m : NC → ℕ) => offset (n+1) (fun j => m (f j)); let g := off (·.1.ng); let b := off (·.1.nb); let e := off (·.1.ne)
  let s := slot n (fun j => (f j).1.ne); (⟨g (n+1),b (n+1),e (n+1),fun i => g (s i)+(f (s i)).1.gate (i-e (s i)),fun i => b (s i)+(f (s i)).1.bit (i-e (s i))⟩,fun i => (f (s i)).2 (i-e (s i)))
theorem manyN_zero (f : ℕ → NC) : manyN 0 f = f 0 := by apply Prod.ext <;> simp [manyN,slot,offset,List.range_one]
theorem manyN_succ (n : ℕ) (f : ℕ → NC) : manyN (n+1) f = catN (f 0) (manyN n fun j => f (j+1)) := by
  apply Prod.ext <;> first | (simp only [manyN,catN,sum,Code.mk.injEq,offset_step]; refine ⟨True.intro,True.intro,True.intro,?_,?_⟩) | skip
  all_goals funext i; by_cases h : i<(f 0).1.ne <;> simp [manyN,catN,sum,slot_step,h,offset_step,show ∀ m f, offset m f 0 = 0 by simp [offset],Nat.add_assoc,Nat.sub_sub]
theorem manyN_spec {k : ℕ} (n : ℕ) (f : ℕ → NC) (b : Fin (n+1) → B k) (h : ∀ j : Fin (n+1), Fits (f j) (b j)) : Fits (manyN n f) (RangeRows.many n b) := by
  induction n generalizing f with | zero => rw [manyN_zero]; exact h 0 | succ n ih => rw [manyN_succ]; exact cat_spec (h 0) (ih _ _ fun j => h j.succ)
def anchorN (n : ℕ) (name : ℕ → ℕ) : NC := (AnchoredLayout.anchorCode n,name)
def rowN (n m : ℕ) (f : ℕ → ℕ → ℕ) : NC := (BaseCode.rowsCode n m, fun i => f (i/m) (i%m))
def colN (n : ℕ) (a b z c : ℕ → ℕ) : NC := (S8H.PointAddresses.add n, fun i =>
  let k := (S8H.PointAddresses.add n).bit i; let j := k/4; if k%4=0 then a j else if k%4=1 then b j else if k%4=2 then z j else c j)
theorem row_spec {s : Shape} {n m : ℕ} {f : ℕ → ℕ → ℕ} {r : Fin n → Fin m → Ref s} (t) (h : ∀ (i : Fin n) (j : Fin m), f i j = (r i j).source.val) : Fits (rowN n m f) (rows n m r t) := ⟨⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩,fun i => h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2⟩
theorem col_spec {s : Shape} {n : ℕ} {a b z c : ℕ → ℕ} {A B Z C : Fin n → Ref s} (v : Bool)
    (ha : ∀ i : Fin n, a i = (A i).source.val) (hb : ∀ i : Fin n, b i = (B i).source.val) (hz : ∀ i : Fin n, z i = (Z i).source.val) (hc : ∀ i : Fin n, c i = (C i).source.val) : Fits (colN n a b z c) (NamedBlocks.add v A B Z C) := by
  refine ⟨add_spec _,fun i => ?_⟩; simp only [colN,(add_spec n).bit i]; let k := (AddLayout.layout n).bit i
  change (if k.val%4=0 then _ else _) = (colRef A B Z C k).source.val
  generalize hk : k.val%4 = x; unfold colRef; rw [hk]; have hj : k.val/4 < n := by have := k.isLt; change k.val < n*4 at this; omega
  rcases x with _|_|_|x <;> first | exact ha ⟨_,hj⟩ | exact hb ⟨_,hj⟩ | exact hz ⟨_,hj⟩ | exact hc ⟨_,hj⟩
def scanN (n : ℕ) (x t : ℕ → ℕ) (c : ℕ) : NC := (⟨n+1,3*n+1,3*n+1,fun i => i/3,id⟩,fun i =>
  if i%3=0 then if i/3=0 then c else t (i/3-1) else if i%3=1 then x (i/3) else t (i/3))
theorem scan_spec {s : Shape} (n : ℕ) (x t : ℕ → ℕ) (c : Ref s) (X T : Fin n → Ref s) (hx : ∀ j : Fin n, x j = (X j).source.val) (ht : ∀ j : Fin n, t j = (T j).source.val) : Fits (scanN n x t c.source.val) (Routes.scan n X c T) := by
  induction n generalizing x t c with
  | zero => rw [Routes.scan]; exact ⟨⟨rfl,rfl,rfl,fun i => by change i.val/3 = i.val/1; have := i.isLt; change i.val < 1 at this; omega,fun _ => rfl⟩,fun i => by have hi : i.val=0 := Nat.lt_one_iff.mp i.isLt; change (if i.val%3=0 then _ else _) = c.source.val; simp [hi]⟩
  | succ n ih =>
    let f := fun (_ j : ℕ) => if j=0 then c.source.val else if j=1 then x 0 else t 0
    have H := cat_spec (row_spec (f:=f) (r:=fun (_ : Fin 1) => ![c,X 0,T 0]) (fun _ v => decide (v 2 = (v 0 || v 1))) (by intro _ j; fin_cases j <;> first | rfl | exact hx 0 | exact ht 0)) (ih (fun j => x (j+1)) (fun j => t (j+1)) (T 0) (X ∘ Fin.succ) (T ∘ Fin.succ) (fun j => hx j.succ) (fun j => ht j.succ))
    rw [Routes.scan]; convert H using 1; apply Prod.ext
    · simp only [scanN,catN,rowN,BaseCode.rowsCode,sum,Code.mk.injEq]; refine ⟨by omega,by omega,by omega,?_,?_⟩ <;> funext i <;> simp [id] <;> omega
    · funext i; simp [scanN,catN,rowN,BaseCode.rowsCode,f,← ht 0]; split_ifs <;> (first | rfl | omega | (congr 1; omega))
def prodN (d e off : ℕ) (a b z : ℕ → ℕ) : NC := catN (S8H.PointAddresses.mul d,fun i => off + if i<e then i else i-e) (rowN (4*d) 2 fun j k => if k=0 then off+(if j<2*d then j else e-2*d+(j-2*d)) else if j<d then a j else if j<2*d then b (j-d) else z (j-2*d))
theorem ext_spec {d : ℕ} (h : 1 ≤ d) (j : Fin (4*d)) : (if j.val<2*d then j.val else (w4_M5GraphBounds.graph d h).nE-2*d+(j.val-2*d)) = (w4_M5PortTensor.ext h j).val := by
  unfold w4_M5PortTensor.ext w4_M5PortTensor.extEdge; by_cases h₁ : j.val<d <;> by_cases h₂ : j.val<2*d <;> simp only [h₁,h₂,if_true,if_false,dif_pos,reduceDIte] <;> try omega
  · change j.val = j.val + d*0; omega
  · change j.val = (j.val-d) + d*1; omega
  · let n := w4_MulParams.n0 d; let t := w4_M5GraphBounds.W d; let u := w4_MulParams.L2 d * (w4_MulParams.L1 d*t); let v := (2*n-1)*t
    change w4_M5GraphBounds.edgeCount d t-2*d+(j.val-2*d) = 2*d+(2*(n*t)+(2*u+(2*u+(u+(u+(2*n*t+(v+(v+(j.val-2*d)))))))))
    unfold w4_M5GraphBounds.edgeCount; dsimp [v,u,n,t]; omega
theorem prod_spec {s : Shape} {d o : ℕ} (h : 1 ≤ d) {a b z : ℕ → ℕ} {A B Z : HashRows.Word s} {R : Fin (w4_M5GraphBounds.graph d h).nE → Ref s} (hw : ∀ i : Fin _, o+i.val = (R i).source.val) (ha : ∀ j, a j = (A j).source.val) (hb : ∀ j, b j = (B j).source.val) (hz : ∀ j, z j = (Z j).source.val) : Fits (prodN d (w4_M5GraphBounds.graph d h).nE o a b z) (HashRows.product h A B Z R) := by
  apply cat_spec
  · refine ⟨mul_spec h,fun i => ?_⟩; have hh := (mul_spec h).bit i; simp only [S8H.PointAddresses.mul,wires_eq h] at hh; exact (congrArg (o+·) hh).trans (hw _)
  · apply row_spec; intro i j; fin_cases j
    · exact (congrArg (o+·) (ext_spec h i)).trans (hw _)
    · change (if i.val<d then _ else _) = (HashRows.busRef d A B Z i).source.val; unfold HashRows.busRef; split_ifs <;> first | apply ha | apply hb | apply hz
def genHashN (d e o₁ o₂ pin : ℕ) (a x b z rem q p₁ p₂ s cp c₁ c₂ c₃ : ℕ → ℕ) : NC :=
  catN (catN (prodN d e o₁ a x p₁) (prodN d e o₂ q (fun _ => pin) p₂)) (catN (colN (2*d) p₂ rem p₁ c₁) (catN (colN (d+1) rem b s c₂) (colN (d+1) z cp s c₃)))
abbrev Names {s : Shape} (a : ℕ → ℕ) (w : HashRows.Word s) := ∀ j, a j = (w j).source.val
theorem genHash_spec {s : Shape} {d o₁ o₂ : ℕ} {hd : 1 ≤ d} (p : ℕ) (w : HashRows.Wires d hd s) {a x b z r q p₁ p₂ t cp c₁ c₂ c₃ : ℕ → ℕ}
    (ha : Names a w.a) (hx : Names x w.x) (hb : Names b w.b) (hz : Names z w.z) (hr : Names r w.rem) (hq : Names q w.quot) (h₁ : Names p₁ w.prod1) (h₂ : Names p₂ w.prod2) (ht : Names t w.sum) (hp : Names cp w.cp)
    (ho : ∀ j, o₁+j.val=(w.mul1 j).source.val) (ho' : ∀ j, o₂+j.val=(w.mul2 j).source.val) (hc : ∀ j : Fin (2*d), c₁ j=(w.carry1 j).source.val) (hc' : ∀ j : Fin (d+1), c₂ j=(w.carry2 j).source.val) (hc'' : ∀ j : Fin (d+1), c₃ j=(w.carry3 j).source.val) :
    Fits (genHashN d (w4_M5GraphBounds.graph d hd).nE o₁ o₂ s.size a x b z r q p₁ p₂ t cp c₁ c₂ c₃) (HashRows.block p w) :=
  cat_spec (cat_spec (prod_spec hd ho ha hx h₁) (prod_spec hd ho' hq (fun _ => rfl) h₂)) (cat_spec (col_spec false (fun j => h₂ j) (fun j => hr j) (fun j => h₁ j) hc) (cat_spec (col_spec false (fun j => hr j) (fun j => hb j) (fun j => ht j) hc') (col_spec false (fun j => hz j) (fun j => hp j) (fun j => ht j) hc'')))
def Eff {α : Type} [Enc α] (F : α → NC) := (PolyT fun x => (F x).1.ng) ∧ (PolyT fun x => (F x).1.ne) ∧ ∀ {I : α → ℕ}, PolyT I → (PolyT fun x => (F x).1.gate (I x)) ∧ (PolyT fun x => (F x).2 (I x))
theorem catP {α : Type} [Enc α] {A B : α → NC} (a : Eff A) (b : Eff B) : Eff (fun x => catN (A x) (B x)) := by
  refine ⟨PolyT.add a.1 b.1,PolyT.add a.2.1 b.2.1,fun h => ?_⟩; have j := b.2.2 (PolyT.sub h a.2.1); have i := a.2.2 h; have k := PolyT.decide_lt h a.2.1
  exact ⟨P2M_Groundwork_PolyT_ite__226169acf219 k i.1 (PolyT.add a.1 j.1),P2M_Groundwork_PolyT_ite__226169acf219 k i.2 j.2⟩
/-- A fixed number of slots only requires a separate efficiency proof for each slot. -/
theorem manyN_const_poly {α : Type} [Enc α] (n : ℕ) (f : α → ℕ → NC) (h : ∀ j, Eff fun x => f x j) : Eff fun x => manyN n (f x) := by
  induction n generalizing f with | zero => simpa only [manyN_zero] using h 0 | succ n ih => simp only [manyN_succ]; exact catP (h 0) (ih _ fun j => h (j+1))
theorem rangeNextP {α : Type} [Enc α] {n : α → ℕ} (hn : Unary n) : PolyT fun x => List.range (n x+1) := by
  apply PolyT.range; exact (PolyT.append (PolyT.const [()]) hn).congr fun x => by simp [List.replicate_succ]
theorem offsetP {α : Type} [Enc α] {n k : α → ℕ} {f : α → ℕ → ℕ} (hn : PolyT fun x => List.range (n x)) (hf : PolyT fun z : α × ℕ => f z.1 z.2) (hk : PolyT k) : PolyT fun x => offset (n x) (f x) (k x) := PolyT.sum (PolyT.take hk (PolyT.map hf hn))
set_option maxHeartbeats 1000000 in
/-- An input-dependent last slot requires unary size and uniform access to the family. -/
theorem manyN_poly {α : Type} [Enc α] {n : α → ℕ} {f : α → ℕ → NC} (hn : Unary n) (hf : Eff fun z : α × ℕ => f z.1 z.2) : Eff fun x => manyN (n x) (f x) := by
  have R := rangeNextP hn; have N : PolyT (fun x => n x+1) := (PolyT.length R).congr fun x => List.length_range
  refine ⟨offsetP R hf.1 N,offsetP R hf.2.1 N,fun {i} hi => ?_⟩
  let S x := slot (n x) (fun j => (f x j).1.ne) (i x)
  have J : PolyT (fun z : α × ℕ => z.2+1) := PolyT.add (PolyT.snd PolyT.id') (PolyT.const 1)
  have R' := PolyT.comp (f:=fun x => List.range (n x+1)) (g:=Prod.fst (β:=ℕ)) R (PolyT.fst PolyT.id')
  have e' := PolyT.comp (f:=fun z : α × ℕ => (f z.1 z.2).1.ne) (g:=fun z : (α × ℕ) × ℕ => (z.1.1,z.2)) hf.2.1 (PolyT.prodMk (PolyT.fst (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id'))
  have O := offsetP (f:=fun z : α × ℕ => fun j => (f z.1 j).1.ne) R' e' J
  have H : PolyT S := PolyT.length (PolyT.filter (PolyT.decide_le O (PolyT.comp hi (PolyT.fst PolyT.id'))) (PolyT.range hn))
  let I x := i x - offset (n x+1) (fun j => (f x j).1.ne) (S x); have D : PolyT I := PolyT.sub hi (offsetP R hf.2.1 H)
  have E := hf.2.2 (PolyT.comp (f:=I) (g:=Prod.fst (β:=ℕ)) D (PolyT.fst (PolyT.id' (α:=α × ℕ)))); have P := PolyT.prodMk PolyT.id' H
  exact ⟨PolyT.add (offsetP R hf.1 H) (PolyT.comp (f:=fun z : α × ℕ => (f z.1 z.2).1.gate (I z.1)) (g:=fun x => (x,S x)) E.1 P),PolyT.comp (f:=fun z : α × ℕ => (f z.1 z.2).2 (I z.1)) (g:=fun x => (x,S x)) E.2 P⟩
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem packet_model {c : Code} {A : w3_FactorLayout} (M : Models c A) : S8H.WirePacket.packet (c.ng+c.nb) c.ne c.gate (fun j => c.ng+c.bit j) = (w3_factorGraph A).subdivision.encode := by
  let G := w3_factorGraph A; have hv : c.ng+c.nb=G.nV := by rw [M.ng,M.nb]; rfl
  have he : c.ne=G.nE := M.ne; rw [hv,he]; exact S8H.WirePacket.packet_eq G _ _ (fun j => M.gate j) (fun j => by rw [M.ng,M.bit j]; rfl)
abbrev cycle (a : NC) := CycleCode.code a.1 a.2
def fullMake (F : PacketWord → NC) (s : PacketWord → ℕ) (w : PacketWord) := let c := cycle (F w); outerPacket w (WirePacket.packet (c.ng+c.nb) c.ne c.gate (fun i => c.ng+c.bit i)) (s w)
theorem fullMake_spec {F s w k} {u : B k} (h : Fits (F w) u) : fullMake F s w = encodeBTNInstance w (w3_factorGraph (CopyCycle.layout u.core.A.gate (NamedWires.next u.name))).subdivision (s w) (s w) 1 := by
  have M := CycleCode.models h.1 (F w).2; rw [AnchoredLayout.next_congr _ u.name (fun i j => by rw [h.2 i,h.2 j]; exact Fin.val_inj)] at M
  dsimp only [fullMake,cycle]; rw [packet_model M,outerPacket_eq]
/-- The length of `big` bounds both packet enumerations; no unary encoding of edge addresses is assumed. -/
theorem fullMake_poly {F : PacketWord → NC} {s : PacketWord → ℕ} {big : PacketWord → List Unit} (h : Eff F) (hi : Eff fun z : PacketWord × ℕ => F z.1) (hs : PolyT s) (hb : PolyT big)
    (bound : ∀ w, let c := cycle (F w); c.ng+c.nb+c.ne ≤ (big w).length ∧ c.ne+c.ne ≤ (big w).length) : PolyT (fullMake F s) := by
  have U {q : PacketWord → ℕ} (hq : PolyT q) (hl : ∀ w, q w ≤ (big w).length) : Unary q := (PolyT.unary_min_length hq hb).congr fun w => by simp only [min_eq_left (hl w)]
  have g := PolyT.add h.1 h.2.1; have v := PolyT.add g h.2.1; have e := PolyT.add h.2.1 (PolyT.add h.2.1 h.2.1); have i := hi.2.2 (PolyT.snd PolyT.id')
  have H := CycleCode.endpoints_poly (c:=fun w => (F w).1) (name:=fun w => (F w).2) h.1 h.2.1 (U h.2.1 fun w => by have := (bound w).2; dsimp [cycle,CycleCode.code] at this; omega) i.1 i.2
  exact outerPacket_poly PolyT.id' (WirePacket.packet_poly (src:=fun w => (cycle (F w)).gate) (dst:=fun w j => (cycle (F w)).ng+(cycle (F w)).bit j) v e (U (PolyT.add v e) fun w => (bound w).1) (U (PolyT.add e e) fun w => (bound w).2) H.1 (PolyT.add (PolyT.comp (f:=fun w => (cycle (F w)).ng) (g:=Prod.fst (β:=ℕ)) g (PolyT.fst PolyT.id')) H.2)) hs
end DetDLP.S8H.MakeCombinators


