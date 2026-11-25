-- Prove2me | Definitions.Def_DetDLP_S8M_Semantics
-- name    : DetDLP_S8M_Semantics
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T13:08:35.783443+00:00
-- url     : https://prove2.me/theorems/b3104e9f-9414-414a-a589-6ff00fe92327
-- title:
--   Tag 6 EC pair-collision anchored layout and bijection
-- statement:
--   Let $E/\mathbf F_p$ be elliptic with $p>3$, let $m\ge1$, and suppose that $T\le p$. For public seed $S$, target $X$, and prefix $\eta$, `validWitnessEquiv` is a bijection from accepted assignments of the anchored factor layout to ordered pairs of factor-block tuples with the prescribed prefix and sum $X$. Every counted pair determines the atom, conversion, and addition registers uniquely. Thus `AcceptedEquiv` identifies the assignment count with the Tag 6 query value. At $X=0$, `rowsAt_zero` identifies the network with the fold pinned to $(\mathrm{true},0,0)$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_Routes
import Definitions.Def_DetDLP_S8M_ECFoldEquiv
import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8M_ECPairPoints

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace DetDLP.S8M.Semantics
open S8H0 RegisterMap NamedBlocks ResidueWires HashRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic S8J.CircuitRealizes M89S1
open ECMapRows (At)
open ECFoldEquiv (Reads)
open Routes (idx first next)
open private ECFoldEquiv.transcript from Definitions.Def_DetDLP_S8M_ECFoldEquiv
noncomputable section
variable {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (hp : 3 < p) (hm : 1 ≤ m) (S : ECSeed p m) (hT : T ≤ p) (X : E.toAffine.Point) (η : List Bool)
abbrev shape (p m : ℕ) := Routes.bank m (width p) (GateSemantics.e p)
abbrev seed (S : ECSeed p m) : Routes.SeedData m := fun i b => ((S i b).1.val+1,(S i b).2.val)
abbrev sw := ECPair.Witness.sw E hp
abbrev target := let c := coords (sw E hp X); (c.1,c.2.1.val,c.2.2.val)
abbrev rowsAt (T : ℕ) := Routes.networkAt (GateSemantics.hd p) hm p T (GateSemantics.coeff E) (seed S) E.b₂.val (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val η (target E hp X)
abbrev net (T : ℕ) := joinB (PointGraph.zeroLast (shape p m).size) (rowsAt E hp hm S X η T)
abbrev core (T : ℕ) := AnchoredLayout.block (net E hp hm S X η T).core ((shape p m).size+1)
abbrev wires (T : ℕ) := AnchoredLayout.wiring (net E hp hm S X η T).core (net E hp hm S X η T).name
def layout (T : ℕ) : w3_FactorLayout := circuit (core E hp hm S X η T) (wires E hp hm S X η T)
def tests (T : ℕ) : w3_factorTest (layout E hp hm S X η T) := test _ (wires E hp hm S X η T)
abbrev Accepted (a : w3_FactorLayout) (t : w3_factorTest a) := {b : Fin a.nb → Bool // ∀ g, t g (fun e => b (a.bit e.1)) = true}
abbrev Physical (T : ℕ) := Accepted (layout E hp hm S X η T) (tests E hp hm S X η T)
private abbrev U (p m : ℕ) := Bits ((shape p m).size+1)
private abbrev raw (u : U p m) := (shape p m).decode (u ∘ Fin.castSucc)
private abbrev extend (v : (shape p m).Data) := (PointGraph.dropLast.symm ((shape p m).decode.symm v)).val
private def physical : Physical E hp hm S X η T ≃ {v : (shape p m).Data // (rowsAt E hp hm S X η T).OK (extend v)} := by
  let D := PointGraph.dropLast.trans (shape p m).decode
  refine ((w3_factorEquiv _ _).symm.trans ((S8J.CircuitRealizes.decode _ _).trans (AnchoredLayout.assignments _ _))).trans ?_
  let Z := fun u : U p m => u (Fin.last _) = false
  let B := rowsAt E hp hm S X η T
  refine (Equiv.subtypeEquivRight (q:=fun u => Z u ∧ B.OK u) (fun u => (joinB_iff ..).trans (and_congr_left fun _ => PointGraph.zeroLast_iff _))).trans ?_
  refine (Equiv.subtypeSubtypeEquivSubtypeInter Z (fun u => B.OK u)).symm.trans (Equiv.subtypeEquiv D ?_)
  intro u; change B.OK u.val ↔ B.OK (D.symm (D u)).val; rw [Equiv.symm_apply_apply]

private theorem index_address (t : Shape) (j : Fin t.size) : (ECAtomSlot.address t j).index = j := by
  induction t with
  | bit => exact Fin.ext (by have := j.isLt; change j.val < 1 at this; change 0 = j.val; omega)
  | word => rfl
  | pair l r il ir =>
    simp only [ECAtomSlot.address]; split <;> simp only [Addr.index,il,ir] <;> apply Fin.ext
    · rfl
    · change l.size + (j.val-l.size) = j.val; omega
  | vec n t ih => simp only [ECAtomSlot.address,Addr.index,ih,Prod.mk.eta]; exact finProdFinEquiv.apply_symm_apply j
private abbrev atomData (p : ℕ) := (ECAtomSlot.slotShape (width p) (GateSemantics.e p)).Data
private abbrev Atom (i : Fin m) := {v : atomData p // ECAtomSlot.sliceOK S i E T v}
private abbrev Factors := ∀ j : Fin (2*m), {P : E.toAffine.Point // P ∈ ecFactorBlock E T S (idx j)}
private abbrev atoms (f : Factors E S (T:=T)) (j : Fin (2*m)) := (ECAtomSlot.slotEquiv S (idx j) hT).symm (f j)
omit [E.IsElliptic] in
private theorem atomIff (u : U p m) (j : Fin (2*m)) :
    (Routes.atomRows (GateSemantics.hd p) p T (GateSemantics.coeff E) (seed S) j).OK u ↔ ECAtomSlot.sliceOK S (idx j) E T ((raw u).1 j) := by
  apply (ECAtomSlot.slotBlock_slice_iff (T:=T) (E:=E) _ _ _ _ S (idx j) (Routes.A j) u (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).trans
  apply iff_of_eq; congr 1
  apply congrArg (ECAtomSlot.slotShape (width p) (GateSemantics.e p)).decode; funext k
  simp [ECAtomSlot.route,Function.comp_def,Addr.index,index_address]; rfl
private theorem atomRead (u : U p m) (j : Fin (2*m)) (w : Atom E S (T:=T) (idx j)) (h : (raw u).1 j = w.val) :
    Reads (Routes.atomW j) u (coords (ECAtomSlot.slotEquiv S (idx j) hT w).val) := by
  obtain ⟨hf,hx,hy⟩ := ECAtomSlot.slotEquiv_coords S (idx j) hT w
  refine ⟨?_,?_,?_⟩
  · rw [hf,←h]; rfl
  · rw [hx,←h]; exact word_eval (fun k => Routes.A j (.fst (RangeRows.xa (.fst k)))) u _ (fun _ => rfl)
  · rw [hy,←h]; exact word_eval (fun k => Routes.A j (.fst (RangeRows.ya (.fst k)))) u _ (fun _ => rfl)

private def conv (P : E.toAffine.Point) := (ECMapRows.mapBlock_unique E hp w3_m5_modmul_r2 P).exists.choose
private theorem convOut (P : E.toAffine.Point) : ECMapRows.output (conv E hp P) = coords (sw E hp P) :=
  ecToSW_sound E hp w3_m5_modmul_r2 P _ _ ((S8O.ECAddLayout.ecToSW_lift E _ _ _).1 _ (ECMapRows.mapBlock_unique E hp w3_m5_modmul_r2 P).exists.choose_spec)
private theorem mapIff (u : U p m) (j : Fin (2*m)) (P : E.toAffine.Point) (H : Reads (Routes.atomW j) u (coords P)) :
    (Routes.mapRows (m:=m) (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val j).OK u ↔ (raw u).2.1 j = ECMapRows.sliceData (conv E hp P) := by
  let f := Routes.M (d:=width p) (e:=GateSemantics.e p) j
  let a := Routes.atomW (d:=width p) (e:=GateSemantics.e p) j
  have h : At f u ((raw u).2.1 j) := fun k => (Addr.correct (f k) (u ∘ Fin.castSucc)).symm
  have c := (ECMapRows.mapBlock_unique E hp w3_m5_modmul_r2 P).exists.choose_spec
  let t := conv E hp P
  have ok (g : At f u (ECMapRows.sliceData t)) := (ECMapRows.mapBlock_iff E _ t f u _ _ _ g H.1 H.2.1 H.2.2).mpr c
  constructor
  · intro yes
    let U := ECMapRows.acceptedSlice_unique E hp w3_m5_modmul_r2 P
    apply U.unique ⟨_,f,u,a.1,a.2.1,a.2.2,h,H.1,H.2.1,H.2.2,yes⟩
    let B := ECMapRows.mapShape (width p) (GateSemantics.e p)
    let z : Bits (B.size+1) := Fin.lastCases false (B.decode.symm (ECMapRows.sliceData t))
    have g : At id z (ECMapRows.sliceData t) := by intro k; change z k.index.castSucc = _; simp [z,←Addr.correct k (B.decode.symm (ECMapRows.sliceData t))]
    exact ⟨B,id,z,.pin (coords P).1,pub _,pub _,g,rfl,fun _ => rfl,fun _ => rfl,(ECMapRows.mapBlock_iff E _ t id z _ _ _ g rfl (fun _ => rfl) (fun _ => rfl)).mpr c⟩
  · intro eq; rw [eq] at h; exact ok h
private theorem mapRead (u : U p m) (j : Fin (2*m)) (P : E.toAffine.Point) (eq : (raw u).2.1 j = ECMapRows.sliceData (conv E hp P)) : Reads (Routes.mapW j) u (coords (sw E hp P)) := by
  let t := conv E hp P
  rw [←convOut]; have H : At (Routes.M j) u (ECMapRows.sliceData t) := eq ▸ (fun k => (Addr.correct (Routes.M j k) (u ∘ Fin.castSucc)).symm)
  refine ⟨H (.fst (.fst .bit)),?_,?_⟩
  · change evalWord _ _ ((zmodEquiv (fits p).le) t.1.2.1).val; rw [GateSemantics.resVal]; exact word_eval (fun k => Routes.M j (.fst (.snd (.fst (.fst k))))) u _ (fun k => ((Ref.reg _).correct u).trans (H (.fst (.snd (.fst (.fst (.word k)))))))
  · change evalWord _ _ ((zmodEquiv (fits p).le) t.1.2.2).val; rw [GateSemantics.resVal]; exact word_eval (fun k => Routes.M j (.fst (.snd (.snd (.fst k))))) u _ (fun k => ((Ref.reg _).correct u).trans (H (.fst (.snd (.snd (.fst (.word k)))))))

private abbrev family (f : Factors E S (T:=T)) := (fun i => (f (Routes.L i)).val,fun i => (f (Routes.R i)).val)
private abbrev condition (f : Factors E S (T:=T)) := (tupleWord (ecWord (bitLen p)) (family E S f)).take η.length = η ∧
  ∑ i, ((family E S f).1 i + (family E S f).2 i) = X
private def pack (f : Factors E S (T:=T)) : (shape p m).Data :=
  (fun j => (atoms E S hT f j).val,fun j => ECMapRows.sliceData (conv E hp (f j).val),
    ECFoldEquiv.transcript (sw E hp (f (first hm)).val) (fun j => sw E hp (f (next j)).val))
omit [E.IsElliptic] in
private theorem digitRead {b : ℕ} (u : U p m) (j : Fin (2*m)) (P : E.toAffine.Point) (h : Reads (Routes.atomW j) u (coords P)) :
    (Routes.digits b j).map (fun r => r.eval u) = ecWord b P := by
  rw [←S8H.ECPointSlots.word_coords]; simp only [Routes.digits,List.map_cons,List.map_append,List.map_ofFn,S8H.ECPointSlots.word,digitWord]
  exact congrArg₂ List.cons h.1 (congrArg₂ List.append (congrArg List.ofFn (funext fun i => h.2.1 _)) (congrArg List.ofFn (funext fun i => h.2.2 _)))
private theorem sumOrder {G : Type} [AddCommMonoid G] (f : Fin (2*m) → G) :
    f (first hm) + ∑ i, f (next i) = ∑ i, (f (Routes.L i) + f (Routes.R i)) := by
  let g (i : ℕ) := if h : i < 2*m then f ⟨i,h⟩ else 0
  have H (k : ℕ) (hk : k < 2*m) : g k = f ⟨k,hk⟩ := dif_pos hk
  calc _ = ∑ j : Fin ((2*m-1)+1), g j := by
              rw [Fin.sum_univ_succ]; simp only [Fin.val_zero,Fin.val_succ,H 0 (by omega)]; congr 1; apply Finset.sum_congr rfl; intro i _; exact (H _ (by have := i.isLt; omega)).symm
       _ = ∑ j : Fin (m+m), g j := by rw [show 2*m-1+1=m+m by omega]
       _ = _ := by rw [Fin.sum_univ_add,Finset.sum_add_distrib]; congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> apply H
private theorem rowsSpec (u : U p m) : (rowsAt E hp hm S X η T).OK u ↔
    ∃ f : Factors E S (T:=T), raw u = pack E hp hm S hT f ∧ condition E S X η f := by
  rw [Routes.networkAt_iff]; simp only [atomIff]
  have rest (f : Factors E S (T:=T)) (ha : ∀ j, (raw u).1 j = (atoms E S hT f j).val) := by
    have ar (j) := atomRead E S hT u j (atoms E S hT f j) (ha j)
    simp only [atoms,Equiv.apply_symm_apply] at ar
    have mi (j) := mapIff E hp u j (f j).val (ar j)
    have prefixEq : (Routes.refs (bitLen p)).map (fun r => r.eval u) = tupleWord (ecWord (bitLen p)) (family E S f) := by
      simp only [Routes.refs,List.map_flatMap,List.map_append,tupleWord,digitRead E u _ _ (ar _)]
    have fold (hs : ∀ j, (raw u).2.1 j = ECMapRows.sliceData (conv E hp (f j).val)) :=
      ECFoldEquiv.foldRows E (sw E hp (f (first hm)).val) (fun j => sw E hp (f (next j)).val) (sw E hp X)
        (Routes.mapW (first hm)) (fun j => Routes.mapW (next j)) (Routes.pins (target E hp X)) Routes.F u (raw u).2.2
        (fun j => (Addr.correct (Routes.F j) (u ∘ Fin.castSucc)).symm) (mapRead E hp u _ _ (hs _))
        (fun j => mapRead E hp u _ _ (hs _)) ⟨rfl,fun _ => rfl,fun _ => rfl⟩
    have eqSum : sw E hp (f (first hm)).val + ∑ i, sw E hp (f (next i)).val = sw E hp X ↔ ∑ i, ((family E S f).1 i+(family E S f).2 i) = X := by
      rw [←map_sum,←map_add,(sw E hp).injective.eq_iff,sumOrder hm (fun j => (f j).val)]
    exact And.intro mi (And.intro prefixEq (And.intro fold eqSum))
  constructor
  · rintro ⟨a,b,c,d⟩
    let f : Factors E S (T:=T) := fun j => ECAtomSlot.slotEquiv S (idx j) hT ⟨_,a j⟩
    have ha (j) : (raw u).1 j = (atoms E S hT f j).val := by simp [atoms,f]
    obtain ⟨mi,pre,fold,eqSum⟩ := rest f ha
    have hs := fun j => (mi j).mp (b j)
    obtain ⟨tr,sm⟩ := (fold hs).mp c
    exact ⟨f,Prod.ext (funext ha) (Prod.ext (funext hs) tr),pre ▸ d,eqSum.mp sm⟩
  · rintro ⟨f,e,d,sm⟩
    have ha (j) : (raw u).1 j = (atoms E S hT f j).val := congrArg (fun x : (shape p m).Data => x.1 j) e
    have hs (j) := congrArg (fun x : (shape p m).Data => x.2.1 j) e
    obtain ⟨mi,pre,fold,eqSum⟩ := rest f ha
    exact ⟨fun j => ha j ▸ (atoms E S hT f j).property,fun j => (mi j).mpr (hs j),
      (fold hs).mpr ⟨congrArg (fun x : (shape p m).Data => x.2.2) e,eqSum.mpr sm⟩,pre ▸ d⟩

private def bankEquiv : Physical E hp hm S X η T ≃ {f : Factors E S (T:=T) // condition E S X η f} := by
  apply (physical E hp hm S X η).trans
  apply Equiv.symm; let B := rowsAt E hp hm S X η T
  have rawExt (v : (shape p m).Data) : raw (extend v) = v :=
    (congrArg (shape p m).decode (PointGraph.dropLast.apply_symm_apply ((shape p m).decode.symm v))).trans ((shape p m).decode.apply_symm_apply v)
  have char (v : (shape p m).Data) : B.OK (extend v) ↔ ∃ f, v = pack E hp hm S hT f ∧ condition E S X η f := by
    simpa only [rawExt] using rowsSpec E hp hm S hT X η (extend v)
  apply Equiv.ofBijective (fun f => ⟨pack E hp hm S hT f.val,(char _).mpr ⟨f.val,rfl,f.property⟩⟩)
  constructor
  · intro f g eq; apply Subtype.ext; funext j; apply (ECAtomSlot.slotEquiv S (idx j) hT).symm.injective; apply Subtype.ext
    exact congrArg (fun v : {v : (shape p m).Data // B.OK (extend v)} => v.val.1 j) eq
  · rintro ⟨v,ok⟩; obtain ⟨f,rfl,cf⟩ := (char _).mp ok; exact ⟨⟨f,cf⟩,rfl⟩
private abbrev PairSet := S8I.ECQueryCount.PairSet p m E T η (bitLen p) S X
private theorem idxL (i : Fin m) : idx (Routes.L i) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
private theorem idxR (i : Fin m) : idx (Routes.R i) = i := Fin.ext (by simp [idx,Nat.mod_eq_of_lt i.isLt])
/-- An accepted assignment determines an ordered pair, and each counted pair determines all its registers. -/
def validWitnessEquiv : Physical E hp hm S X η T ≃ S8I.ECQueryCount.PairSet p m E T η (bitLen p) S X := by
  classical
  letI := ecPointFintype E
  refine (bankEquiv E hp hm S hT X η).trans ?_
  let split (f : {f : Factors E S (T:=T) // condition E S X η f}) : PairSet E S X η (T:=T) :=
    ⟨family E S f.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i => ⟨by simpa only [idxL] using (f.val (Routes.L i)).property, by simpa only [idxR] using (f.val (Routes.R i)).property⟩,f.property⟩⟩
  apply Equiv.ofBijective split; constructor
  · intro f g eq; apply Subtype.ext; funext j; apply Subtype.ext
    have H := congrArg Subtype.val eq
    by_cases hj : j.val < m
    · exact congrArg (fun ab => ab.1 ⟨j,hj⟩) H
    · let k : Fin m := ⟨j-m,by have := j.isLt; omega⟩
      have e : j = Routes.R k := Fin.ext (by dsimp [Routes.R,k]; omega)
      rw [e]; exact congrArg (fun ab => ab.2 k) H
  · rintro ⟨ab,h⟩; obtain ⟨_,mem,pre,sm⟩ := Finset.mem_filter.mp h
    let f : Factors E S (T:=T) := fun j => if hj : j.val < m then
      ⟨ab.1 ⟨j,hj⟩, (idxL ⟨j,hj⟩).symm ▸ (mem ⟨j,hj⟩).1⟩ else
      let k : Fin m := ⟨j-m,by have := j.isLt; omega⟩
      have eq : Routes.R k = j := Fin.ext (by dsimp [Routes.R,k]; omega)
      ⟨ab.2 k,eq ▸ (idxR k).symm ▸ (mem k).2⟩
    have e : family E S f = ab := by
      apply Prod.ext <;> funext i <;> simp [f,Routes.L,Routes.R,i.isLt]
    exact ⟨⟨f,show condition E S X η f by unfold condition; rw [e]; exact ⟨pre,sm⟩⟩,Subtype.ext e⟩
abbrev ECPairCount (T : ℕ) := ECPair.value E T S X η
/-- The accepted-assignment count for the anchored layout is the Tag 6 query value. -/
theorem AcceptedEquiv (hT : T ≤ p) : Fintype.card (Physical E hp hm S X η T) = ECPairCount E S X η T :=
  (Fintype.card_congr (validWitnessEquiv E hp hm S hT X η)).trans (S8I.ECQueryCount.pair_card ..)
/-- The neutral target is exactly the infinity flag with two zero coordinate words. -/
theorem target_zero : target E hp 0 = (true,0,0) := by simp [target,map_zero,coords]
theorem rowsAt_zero : rowsAt E hp hm S 0 η T = Routes.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E) (seed S)
    E.b₂.val (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val η := by unfold rowsAt; rw [target_zero]
end
end DetDLP.S8M.Semantics


