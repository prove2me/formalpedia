-- Prove2me | Definitions.Def_DetDLP_S8N_MomentOwner
-- name    : DetDLP_S8N_MomentOwner
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T12:25:10.028661+00:00
-- url     : https://prove2.me/theorems/81be9015-e2b0-51aa-8db4-5e2baa4c7a00
-- title:
--   Source addresses for the elliptic-curve moment circuit
-- statement:
--   Constructs the source endpoint from the decoded moment word and edge index and proves that it agrees with the actual physical layout on every edge.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_BaseCode
import Definitions.Def_DetDLP_S8L_FpPairAddresses
import Definitions.Def_DetDLP_S8N_MomentDimensions

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentOwner

open Groundwork S8H.PointAddresses S8H0 RegisterMap NamedBlocks
open S8L.FpPair.Address (repeatCode)

private theorem tileIndex {e : ℕ} (he : 0 < e) (g i : ℕ) (f : ℕ → ℕ) :
    f (i%e) + g*(i/e) =
      if i < e then f i else g + (f ((i-e)%e) + g*((i-e)/e)) := by
  split_ifs with hi
  · simp [Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
    simp [Nat.add_div_left _ he, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

theorem repeat_many {k : ℕ} (n : ℕ) (f : Fin (n+1) → B k) (a : Code)
    (h : ∀ i, Models a (f i).core.A) :
    Models (repeatCode (n+1) a) (RangeRows.many n f).core.A := by
  induction n with
  | zero =>
    have H := h 0
    refine ⟨(Nat.one_mul _).trans H.ng, (Nat.one_mul _).trans H.nb,
      (Nat.one_mul _).trans H.ne, ?_, ?_⟩
    all_goals
      intro i
      have hi : i.val < a.ne := lt_of_lt_of_eq i.isLt H.ne.symm
      simp only [repeatCode, Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, Nat.mul_zero, Nat.add_zero]
    · exact H.gate i
    · exact H.bit i
  | succ n ih =>
    rw [RangeRows.many]
    have H := sum_spec (h 0) (ih (fun i => f i.succ) (fun i => h i.succ))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (show (n+1+1)*a.ng = a.ng+(n+1)*a.ng by ring).trans H.ng
    · exact (show (n+1+1)*a.nb = a.nb+(n+1)*a.nb by ring).trans H.nb
    · exact (show (n+1+1)*a.ne = a.ne+(n+1)*a.ne by ring).trans H.ne
    all_goals
      intro i
      have hi : i.val < a.ne+(n+1)*a.ne := lt_of_lt_of_eq i.isLt H.ne.symm
      have hp : 0 < a.ne := by
        by_contra! z
        simp [Nat.eq_zero_of_le_zero z] at hi
    · exact (tileIndex hp _ _ _).trans (H.gate i)
    · exact (tileIndex hp _ _ _).trans (H.bit i)

theorem repeat_all {s : Shape} (n : ℕ) (f : Fin n → B (s.size+1)) (a : Code)
    (h : ∀ i, Models a (f i).core.A) :
    Models (repeatCode n a) (S8G.SeedAndAtomBank.allRows n f).core.A := by
  cases n with
  | zero =>
    exact ⟨Nat.zero_mul _, Nat.zero_mul _, Nat.zero_mul _, fun i => i.elim0, fun i => i.elim0⟩
  | succ n => exact repeat_many n f a h

/-- Polynomial-time access to a code's dimensions and gate owner under arbitrary input encodings. -/
structure Efficient {α : Type} [Enc α] (C : α → Code) : Prop where
  ng : PolyT fun x => (C x).ng
  ne : PolyT fun x => (C x).ne
  gate : ∀ {i : α → ℕ}, PolyT i → PolyT fun x => (C x).gate (i x)

variable {α : Type} [Enc α]

theorem ofUniform {F : ℕ → Code} {d : α → ℕ} (h : Uniform F) (hd : PolyT d) :
    Efficient fun x => F (d x) := ⟨h.ng hd, h.ne hd, h.gate hd⟩

theorem sumP {A B : α → Code} (ha : Efficient A) (hb : Efficient B) :
    Efficient (fun x => sum (A x) (B x)) := by
  refine ⟨PolyT.add ha.ng hb.ng, PolyT.add ha.ne hb.ne, fun hi => ?_⟩
  exact PolyT.ite' (PolyT.decide_lt hi ha.ne) (ha.gate hi)
    (PolyT.add ha.ng (hb.gate (PolyT.sub hi ha.ne)))

theorem repeatP {n : α → ℕ} {A : α → Code} (hn : PolyT n) (ha : Efficient A) :
    Efficient (fun x => repeatCode (n x) (A x)) := by
  refine ⟨PolyT.mul hn ha.ng, PolyT.mul hn ha.ne, fun hi => ?_⟩
  exact PolyT.add (ha.gate (PolyT.mod hi ha.ne)) (PolyT.mul ha.ng (PolyT.div hi ha.ne))

theorem rowP {n : α → ℕ} (k : ℕ) (hn : PolyT n) :
    Efficient (fun x => BaseCode.rowsCode (n x) k) :=
  ⟨hn, PolyT.mul hn (PolyT.const k), fun hi => PolyT.div hi (PolyT.const k)⟩

theorem anchorP {n : α → ℕ} (hn : PolyT n) :
    Efficient (fun x => AnchoredLayout.anchorCode (n x)) := ⟨hn, hn, fun hi => hi⟩

end DetDLP.S8N.MomentOwner

namespace DetDLP.S8N.MomentOwner

open Groundwork S8H.PointAddresses S8H0 RegisterMap NamedBlocks GateRoutes RangeRows HashRows
open BaseCode (rowsCode)
open S8L.FpPair.Address (repeatCode)
open S8G.SeedAndAtomBank S8M
open private rangeCode hashCode range_spec hash_spec' many_spec rows_spec
  from Definitions.Def_DetDLP_S8H0_BaseCode
open private fixed from Definitions.Def_DetDLP_S8M_ECAtomSlot
open private ranges maskEq from Definitions.Def_DetDLP_S8M_ECMapRows
open private invRows selectRows from Definitions.Def_DetDLP_S8N_ECAddRoutes
open private foldStep from Definitions.Def_DetDLP_S8M_ECFoldRoutes

def seedSlotCode (d : ℕ) :=
  let a := S8H.PointAddresses.add (d+1)
  sum a (sum a a)

def seedCode (m d k : ℕ) :=
  sum (repeatCode m (sum (seedSlotCode d) (seedSlotCode d))) (rowsCode k 1)

def atomCode (d : ℕ) :=
  let h := hashCode d
  let base := sum (rangeCode d) (sum (copiesCode h 5) (rowsCode d 5))
  sum (sum base (sum h (sum (rowsCode 1 1) (S8H.PointAddresses.add (d+1))))) (rowsCode d 7)

def mapCode (d : ℕ) :=
  let a := S8H.PointAddresses.add (d+1)
  sum (sum (sum a a) (copiesCode (sum a a) 3))
    (sum (copiesCode (hashCode d) 3) (sum (rowsCode 1 2) (sum (rowsCode d 3) (rowsCode d 3))))

def stepCode (d : ℕ) :=
  let a := S8H.PointAddresses.add (d+1)
  sum (copiesCode a 3) <| sum (copiesCode (sum a a) 14) <| sum (copiesCode (hashCode d) 14) <|
    sum (rowsCode d 4) <| sum (rowsCode d 4) <| sum (rowsCode d 7) <|
    sum (rowsCode 1 5) (sum (rowsCode d 8) (rowsCode d 8))

def foldCode (n d : ℕ) :=
  sum (rowsCode 1 2) (sum (rowsCode d 2) (sum (rowsCode d 2) (repeatCode n (stepCode d))))

def targetCode (d : ℕ) :=
  let a := S8H.PointAddresses.add (d+1)
  sum a (sum a (rowsCode d 3))

theorem seedSlot_models {s : Shape} {d : ℕ} (p : ℕ) (q : Path (seedSlot d) s) :
    Models (seedSlotCode d) (ECSeedBank.ecSeedSlotBlock p q).core.A :=
  sum_spec (add_spec _) (sum_spec (add_spec _) (add_spec _))

theorem seed_models {s : Shape} {m d : ℕ} (p : ℕ) (η : List Bool)
    (q : Path (ECSeedBank.ecSeedShape m d) s) :
    Models (seedCode m d η.length) (RoutesV2.ecSeedBlockV2 p m η q).core.A :=
  sum_spec (repeat_all m _ _ fun _ => sum_spec (seedSlot_models ..) (seedSlot_models ..))
    (rows_spec ..)

theorem atom_models {s : Shape} {d : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (a b x y : Word s) (q : Path (ECAtomSlot.slotShape d (w4_M5GraphBounds.graph d hd).nE) s) :
    Models (atomCode d) (ECAtomSlot.slotBlock hd p T c a b x y q).core.A := by
  unfold atomCode ECAtomSlot.slotBlock fixed
  exact sum_spec (sum_spec (sum_spec (range_spec ..)
    (sum_spec (many_spec _ _ _ (fun _ => hash_spec' ..)) (rows_spec ..)))
    (sum_spec (hash_spec' ..) (sum_spec (rows_spec ..) (add_spec _)))) (rows_spec ..)

theorem map_models {s : Shape} {d e : ℕ} (hd : 1 ≤ d) (p b a c : ℕ) (f : Ref s)
    (x y : Word s) (q : Path (ECMapRows.mapShape d e) s) :
    Models (mapCode d) (ECMapRows.mapBlock hd p b a c f x y q).core.A := by
  unfold mapCode ECMapRows.mapBlock ranges maskEq
  exact sum_spec
    (sum_spec (sum_spec (add_spec _) (add_spec _))
      (many_spec _ _ _ (fun _ => sum_spec (add_spec _) (add_spec _))))
    (sum_spec (many_spec _ _ _ (fun _ => hash_spec' ..))
      (sum_spec (rows_spec ..) (sum_spec (rows_spec ..) (rows_spec ..))))

theorem step_models {s : Shape} {d e : ℕ} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (f : Ref s) (x y : Word s) (g : Ref s) (X Y : Word s) (q : Path (ECAddRoutes.addShape d e) s) :
    Models (stepCode d) (ECAddRoutes.addBlock hd p neg1 three c4 f x y g X Y q).core.A := by
  unfold stepCode ECAddRoutes.addBlock invRows selectRows
  exact sum_spec (many_spec _ _ _ (fun _ => add_spec _))
    (sum_spec (many_spec _ _ _ (fun _ => sum_spec (add_spec _) (add_spec _)))
      (sum_spec (many_spec _ _ _ (fun _ => hash_spec' ..))
        (sum_spec (rows_spec ..) (sum_spec (rows_spec ..) (sum_spec (rows_spec ..)
          (sum_spec (rows_spec ..) (sum_spec (rows_spec ..) (rows_spec ..))))))))

theorem fold_models {s : Shape} {n d e : ℕ} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (f : Ref s) (x y : Word s) (flags : Fin n → Ref s) (xs ys : Fin n → Word s)
    (z : Ref s) (X Y : Word s) (q : Path (ECFoldRoutes.foldShape n d e) s) :
    Models (foldCode n d) (ECFoldRoutes.foldBlock hd p neg1 three c4 f x y flags xs ys z X Y q).core.A := by
  unfold foldCode ECFoldRoutes.foldBlock
  exact sum_spec (rows_spec ..) (sum_spec (rows_spec ..) (sum_spec (rows_spec ..)
    (repeat_all n (foldStep hd p neg1 three c4 f x y flags xs ys q) _ (fun _ => step_models ..))))

theorem target_models {s : Shape} {d : ℕ} (p : ℕ) (q : Path (RoutesV2.targetShape d) s) :
    Models (targetCode d) (RoutesV2.targetBlock p q).core.A :=
  sum_spec (add_spec _) (sum_spec (add_spec _) (rows_spec ..))

end DetDLP.S8N.MomentOwner

namespace DetDLP.S8N.MomentOwner

open Groundwork S8H.PointAddresses S8H0 RegisterMap NamedBlocks GateRoutes
open BaseCode (rowsCode)
open S8L.FpPair.Address (repeatCode)
open S8G.SeedAndAtomBank
open private rangeCode hashCode from Definitions.Def_DetDLP_S8H0_BaseCode

def tree (c o m d e k : ℕ) :=
  let product := sum (targetCode d)
    (sum (repeatCode (2*m) (mapCode d)) (repeatCode 2 (foldCode (m-1) d)))
  sum (AnchoredLayout.anchorCode (PortPoly.anchorCount c o m d e)) <|
    sum (AnchoredLayout.anchorCode 1) <| sum (seedCode m d k) <|
    sum (repeatCode c (repeatCode m (atomCode d))) (repeatCode o product)

theorem tree_models {m d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ) (c : Coeff)
    (b2 neg1 three c4 : ℕ) (j : Fin 4) (η : List Bool) :
    let e := (w4_M5GraphBounds.graph d hd).nE
    let s := RoutesV2.bank j m d e
    let N := joinB (PointGraph.zeroLast s.size) (RoutesV2.network hd hm p T c b2 neg1 three c4 j η id)
    Models (tree (RoutesV2.copies j) (RoutesV2.outputs j) m d e η.length)
      (AnchoredLayout.block N.core (s.size+1)).A := by
  dsimp only
  unfold tree
  rw [MomentGeometry.anchor_eq]
  refine sum_spec (AnchoredLayout.anchorModels _) (sum_spec (AnchoredLayout.anchorModels 1) ?_)
  unfold RoutesV2.network
  refine sum_spec (seed_models ..) (sum_spec
    (repeat_all _ _ _ (fun _ => repeat_all _ _ _ (fun _ => atom_models ..))) ?_)
  exact repeat_all _ _ _ fun _ => sum_spec (target_models ..)
    (sum_spec (repeat_all _ _ _ (fun _ => map_models ..))
      (repeat_all _ _ _ (fun _ => fold_models ..)))

variable {α : Type} [Enc α] {C O M D E K : α → ℕ}

private theorem fixedP {A : α → Code} (n : ℕ) (ha : Efficient A) :
    Efficient (fun x => copiesCode (A x) n) := by
  induction n with
  | zero => exact ha
  | succ n ih => exact sumP ha ih

private theorem addP {n : α → ℕ} (hn : PolyT n) :
    Efficient fun x => S8H.PointAddresses.add (n x) :=
  ofUniform (add_poly id (fun h => h)) hn

private theorem hashP (hd : PolyT D) : Efficient fun x => hashCode (D x) := by
  have hr := rowP 2 (PolyT.mul (PolyT.const 4) hd)
  have hm := sumP (ofUniform mul_poly hd) hr
  have a := addP (PolyT.add hd (PolyT.const 1))
  exact sumP (sumP hm hm) (sumP (addP (PolyT.mul (PolyT.const 2) hd)) (sumP a a))

private theorem rangeP (hd : PolyT D) : Efficient fun x => rangeCode (D x) := by
  have a := addP (PolyT.add hd (PolyT.const 1))
  exact sumP (sumP a a) (fixedP 6 (sumP a a))

theorem seedP (hm : PolyT M) (hd : PolyT D) (hk : PolyT K) :
    Efficient fun x => seedCode (M x) (D x) (K x) := by
  have a := addP (PolyT.add hd (PolyT.const 1))
  have slot := sumP a (sumP a a)
  exact sumP (repeatP hm (sumP slot slot)) (rowP 1 hk)

theorem atomP (hd : PolyT D) : Efficient fun x => atomCode (D x) := by
  have h := hashP hd
  exact sumP (sumP (sumP (rangeP hd) (sumP (fixedP 5 h) (rowP 5 hd)))
    (sumP h (sumP (rowP 1 (PolyT.const 1)) (addP (PolyT.add hd (PolyT.const 1)))))) (rowP 7 hd)

theorem mapP (hd : PolyT D) : Efficient fun x => mapCode (D x) := by
  have a := addP (PolyT.add hd (PolyT.const 1))
  exact sumP (sumP (sumP a a) (fixedP 3 (sumP a a)))
    (sumP (fixedP 3 (hashP hd)) (sumP (rowP 2 (PolyT.const 1)) (sumP (rowP 3 hd) (rowP 3 hd))))

theorem stepP (hd : PolyT D) : Efficient fun x => stepCode (D x) := by
  have a := addP (PolyT.add hd (PolyT.const 1))
  exact sumP (fixedP 3 a) <| sumP (fixedP 14 (sumP a a)) <| sumP (fixedP 14 (hashP hd)) <|
    sumP (rowP 4 hd) <| sumP (rowP 4 hd) <| sumP (rowP 7 hd) <|
    sumP (rowP 5 (PolyT.const 1)) (sumP (rowP 8 hd) (rowP 8 hd))

theorem foldP (hn : PolyT M) (hd : PolyT D) : Efficient fun x => foldCode (M x) (D x) :=
  sumP (rowP 2 (PolyT.const 1)) (sumP (rowP 2 hd) (sumP (rowP 2 hd) (repeatP hn (stepP hd))))

theorem targetP (hd : PolyT D) : Efficient fun x => targetCode (D x) := by
  have a := addP (PolyT.add hd (PolyT.const 1))
  exact sumP a (sumP a (rowP 3 hd))

attribute [local fun_prop] PolyT.add PolyT.sub PolyT.mul PolyT.const

theorem treeP (hc : PolyT C) (ho : PolyT O) (hm : PolyT M) (hd : PolyT D)
    (he : PolyT E) (hk : PolyT K) :
    Efficient fun x => tree (C x) (O x) (M x) (D x) (E x) (K x) := by
  have an : PolyT (fun x => PortPoly.anchorCount (C x) (O x) (M x) (D x) (E x)) := by
    unfold PortPoly.anchorCount
    fun_prop (disch := assumption)
  have product := sumP (targetP hd) (sumP (repeatP (PolyT.mul (PolyT.const 2) hm) (mapP hd))
    (repeatP (PolyT.const 2) (foldP (PolyT.sub hm (PolyT.const 1)) hd)))
  exact sumP (anchorP an) <| sumP (anchorP (PolyT.const 1)) <| sumP (seedP hm hd hk) <|
    sumP (repeatP hc (repeatP hm (atomP hd))) (repeatP ho product)

end DetDLP.S8N.MomentOwner

namespace DetDLP.S8N.MomentOwner

open Groundwork S8H.PointAddresses S8H0

def code (w : List Bool) : Code :=
  let b := S8G.FpMoment.Code.width (S8M.PortPoly.prime w)
  let d := b+1
  let j := PortPoly.idx w
  tree (min j 2) (if j = 3 then 1 else 0) (S8G.FpMoment.Code.slots b) d
    (S8H.PointAddresses.wires d) (PortPoly.prefixBits w).length

def owner (w : List Bool) (i : ℕ) := (code w).gate i

def sourceAt (e g o i : ℕ) :=
  if i < e then o else g + (if i-e < e then i-e else i-e-e)

def src (w : List Bool) (i : ℕ) :=
  sourceAt (MomentDimensions.incidences w) (PortPoly.decoded w).1 (owner w i) i

private theorem cycle_source {k : ℕ} {B : S8J.CircuitRealizes.Block} {c : Code}
    (H : Models c B.A) (W : S8J.CircuitRealizes.Wiring B.A.ne k)
    (i : Fin (S8J.CircuitRealizes.G B W).nE) :
    sourceAt c.ne c.ng (c.gate i.val) i.val = ((S8J.CircuitRealizes.G B W).endpoints i).1.val :=
  (CycleCode.models H (fun _ => 0)).gate i

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

theorem code_models (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool) :
    Models (code (MomentGeometry.word E j T η)) (MomentGeometry.core E hm j T η).A := by
  have h : PortPoly.idx (MomentGeometry.word E j T η) = j.val ∧
      PortPoly.prefixBits (MomentGeometry.word E j T η) = η := by
    simp [PortPoly.idx, PortPoly.prefixBits, MomentGeometry.word, M89S1.queryWord,
      DetDLP_W1_Queries.third, DetDLP_W1_Queries.second]
  simp only [code, MomentGeometry.prime_word, S8G.FpMoment.Code.width_eq, S8G.FpMoment.Code.slots_eq,
    h.1, h.2, S8H.PointAddresses.wires_eq (GateSemantics.hd p)]
  exact tree_models (GateSemantics.hd p) hm p T (GateSemantics.coeff E) E.b₂.val
    (-1 : ZMod p).val (3 : ZMod p).val (-27 * E.c₄).val j η

theorem owner_word (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool)
    (i : Fin (MomentGeometry.core E hm j T η).A.ne) :
    owner (MomentGeometry.word E j T η) i.val = ((MomentGeometry.core E hm j T η).A.gate i).val :=
  (code_models E hm j T η).gate i

theorem src_of_gateCount (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool)
    (hgate : (PortPoly.decoded (MomentGeometry.word E j T η)).1 = (MomentGeometry.core E hm j T η).A.ng)
    (i : Fin (S8J.CircuitRealizes.G (MomentGeometry.core E hm j T η) (MomentGeometry.wires E hm j T η)).nE) :
    src (MomentGeometry.word E j T η) i.val =
      ((S8J.CircuitRealizes.G (MomentGeometry.core E hm j T η) (MomentGeometry.wires E hm j T η)).endpoints i).1.val := by
  let w := MomentGeometry.word E j T η
  have H := code_models E hm j T η
  have he : MomentDimensions.incidences w = (code w).ne :=
    (MomentDimensions.incidences_word E hm j T η).trans H.ne.symm
  have hg : (PortPoly.decoded w).1 = (code w).ng :=
    hgate.trans H.ng.symm
  change src w i.val = _
  simp only [src, owner, he, hg]
  exact cycle_source H (MomentGeometry.wires E hm j T η) i

theorem code_poly {α : Type} [Enc α] {w : α → List Bool} (hw : PolyT w) :
    Efficient fun x => code (w x) := by
  have hb := S8G.FpMoment.Code.width_poly (PolyT.comp DetDLP.S8N.PortPoly.prime_poly hw)
  have hd := PolyT.add hb (PolyT.const 1)
  have hi := PolyT.comp PortPoly.idx_poly hw
  have hc : PolyT (fun x => min (PortPoly.idx (w x)) 2) := by
    simp only [min_def]
    exact PolyT.ite' (PolyT.decide_le hi (PolyT.const 2)) hi (PolyT.const 2)
  have ho : PolyT (fun x => if PortPoly.idx (w x) = 3 then 1 else 0) :=
    PolyT.ite' (PolyT.decide_eq hi (PolyT.const 3)) (PolyT.const 1) (PolyT.const 0)
  exact treeP hc ho (S8G.FpMoment.Code.slots_poly hb) hd (S8H.PointAddresses.mul_poly.nb hd)
    (PolyT.length (PolyT.comp PortPoly.prefix_poly hw))

theorem owner_poly : PolyT (fun z : List Bool × ℕ => owner z.1 z.2) :=
  (code_poly (PolyT.fst PolyT.id')).gate (PolyT.snd PolyT.id')

private theorem sourceAt_poly {α : Type} [Enc α] {n g o i : α → ℕ}
    (hn : PolyT n) (hg : PolyT g) (ho : PolyT o) (hi : PolyT i) :
    PolyT (fun x => sourceAt (n x) (g x) (o x) (i x)) := by
  exact PolyT.ite' (PolyT.decide_lt hi hn) ho (PolyT.add hg
    (PolyT.ite' (PolyT.decide_lt (PolyT.sub hi hn) hn) (PolyT.sub hi hn) (PolyT.sub (PolyT.sub hi hn) hn)))

theorem src_poly : PolyT (fun z : List Bool × ℕ => src z.1 z.2) := by
  have w := PolyT.fst (PolyT.id' (α := List Bool × ℕ))
  have i := PolyT.snd (PolyT.id' (α := List Bool × ℕ))
  have e := PolyT.comp MomentDimensions.incidences_poly w
  have g := PolyT.comp (f := fun w => (PortPoly.decoded w).1) PortPoly.decoded_poly.1 w
  exact sourceAt_poly e g owner_poly i

end DetDLP.S8N.MomentOwner
end


