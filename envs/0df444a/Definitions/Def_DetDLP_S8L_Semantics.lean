-- Prove2me | Definitions.Def_DetDLP_S8L_Semantics
-- name    : DetDLP_S8L_Semantics
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:58:11.875992+00:00
-- url     : https://prove2.me/theorems/d4788504-9c48-45d2-b8bb-28d920c3db41
-- title:
--   Tag 5 anchored factor layout and pairSet witness bijection
-- statement:
--   For a prime $p$ and $m\ge 1$, the satisfying assignments of the anchored Tag 5 layout are in bijection with the pairs in the prescribed hash blocks whose tuple word begins with $\eta$ and whose product is $X$. The bijection also identifies accepted network assignments with shortened M5 transcripts. Consequently the layout witness count equals the Tag 5 query value whenever $|\eta|\le 2m\,\mathrm{bitLen}(p)$ and the public coefficients agree with the seed.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_PairOrder
import Definitions.Def_DetDLP_S8L_FpPairGraph
import Definitions.Def_DetDLP_S8H0_PointGraph

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace DetDLP.S8L.Semantics
open S8H0 S8H0.NamedBlocks S8H0.RegisterMap S8H0.ResidueWires
open S8J.CircuitRealizes

abbrev width (p : ℕ) := bitLen p + 1
abbrev width_pos (p : ℕ) : 1 ≤ width p := Nat.succ_pos _
abbrev shape (p m : ℕ) := Routes.bank m (width p) (Routes.G (width_pos p))

def net (p m T X : ℕ) (seedCoeffs : Fin m → ℕ × ℕ) (η : List Bool) :=
  joinB (PointGraph.zeroLast (shape p m).size)
    (Routes.network (width_pos p) p m T X seedCoeffs η)

abbrev core (p m T X : ℕ) (seedCoeffs : Fin m → ℕ × ℕ) (η : List Bool) :=
  AnchoredLayout.block (net p m T X seedCoeffs η).core ((shape p m).size + 1)

abbrev wiring (p m T X : ℕ) (seedCoeffs : Fin m → ℕ × ℕ) (η : List Bool) :=
  AnchoredLayout.wiring (net p m T X seedCoeffs η).core (net p m T X seedCoeffs η).name

def layout (p m T X : ℕ) (seedCoeffs : Fin m → ℕ × ℕ) (η : List Bool) : w3_FactorLayout :=
  circuit (core p m T X seedCoeffs η) (wiring p m T X seedCoeffs η)

def tests (p m T X : ℕ) (seedCoeffs : Fin m → ℕ × ℕ) (η : List Bool) :
    w3_factorTest (layout p m T X seedCoeffs η) :=
  test (core p m T X seedCoeffs η) (wiring p m T X seedCoeffs η)

variable (p m T X : ℕ) (cs : Fin m → ℕ × ℕ) (η : List Bool)

abbrev Witness := {b : Fin (layout p m T X cs η).nb → Bool //
  ∀ g, tests p m T X cs η g (fun e => b ((layout p m T X cs η).bit e.1)) = true}

/-- Copy-cycle consistency and the anchors identify physical assignments with named signals. -/
noncomputable def namedEquiv : Witness p m T X cs η ≃ {u // (net p m T X cs η).OK u} :=
  ((w3_factorEquiv _ (tests p m T X cs η)).symm.trans
    (S8J.CircuitRealizes.decode (core p m T X cs η) (wiring p m T X cs η))).trans
    (AnchoredLayout.assignments _ _)

abbrev extend {n : ℕ} (v : Bits n) : Bits (n+1) := (PointGraph.dropLast.symm v).val

/-- The last signal is fixed, so it contributes no multiplicity to the count. -/
noncomputable def physicalEquiv : Witness p m T X cs η ≃
    {v : Bits (shape p m).size // (Routes.network (width_pos p) p m T X cs η).OK (extend v)} := by
  let R := Routes.network (width_pos p) p m T X cs η
  let Z := fun u : Bits ((shape p m).size + 1) => u (Fin.last _) = false
  refine (namedEquiv p m T X cs η).trans ?_
  refine (Equiv.subtypeEquivRight (q := fun u => Z u ∧ R.OK u) ?_).trans ?_
  · intro u; exact (joinB_iff ..).trans (and_congr_left fun _ => PointGraph.zeroLast_iff _)
  refine (Equiv.subtypeSubtypeEquivSubtypeInter Z (fun u => R.OK u)).symm.trans ?_
  apply Equiv.subtypeEquiv PointGraph.dropLast
  intro u
  change R.OK u.val ↔ R.OK (PointGraph.dropLast.symm (PointGraph.dropLast u)).val
  rw [Equiv.symm_apply_apply]

section Count
open S8C M89S1 RowSound PairOrder
variable {p m T : ℕ} [Fact p.Prime] (S : FpSeed p m) (Y : (ZMod p)ˣ)
abbrev Atoms := ∀ j : Fin (2*m), AtomLift.Accepted S (idx j) T
noncomputable abbrev fac (a : Atoms (T:=T) S) : Factors p m := fun j => (unitEquiv S (idx j) T (a j)).val
abbrev Prefix (a : Atoms (T:=T) S) (η : List Bool) := (tupleWord elemWord (pair (fac S a))).take η.length = η
abbrev rest (a : Atoms (T:=T) S) (v : ChainLift.Bank p (2*m)) (η : List Bool) :=
  Prefix S a η ∧ ChainLift.OK (seq (fac S a)) (Y : ZMod p) v
abbrev Valid (v : (shape p m).Data) := ∀ j, constraint (primeFitsAtom p).le T (AtomLift.coeff S (idx j)) (v.1 j)
abbrev packed (v : (shape p m).Data) (h : Valid (T:=T) S v) : Atoms (T:=T) S := fun j => ⟨v.1 j,h j⟩

private theorem rows (hm : 1 ≤ m) (hη : η.length ≤ 2*m*bitLen p) (u : Input m (width p) (width_pos p)) :
    (Routes.network (width_pos p) p m T (Y : ZMod p).val (AtomLift.coeff S) η).OK u ↔
    ∃ h : Valid (T:=T) S (raw u), rest S Y (packed S _ h) (raw u).2 η := by
  rw [Routes.network_iff]; simp only [atom_iff (primeFitsAtom p).le,stage_iff]
  let v := raw u
  have R (j : Fin (2*m-2)) := RangeRows.checker_iff p (Routes.intermediate j) u (v.2.2 j) (fun _ => (Addr.correct _ (u ∘ Fin.castSucc)).symm)
  simp only [R,hη,(Y : ZMod p).val_lt,(Y : ZMod p).val_lt.trans (primeFitsAtom p),show m ≠ 0 by omega,false_implies,true_and]
  have N (h : Valid (T:=T) S v) (hr : ∀ j, below p (v.2.2 j)) :
      rest S Y (packed S v h) v.2 η ↔ (∀ i : Fin (2*m-1), step p (inputX v i) (num (v.1 ⟨i+1,by have := i.isLt; omega⟩).1.1) (outputZ (Y : ZMod p).val v i) (v.2.1 i)) ∧ ∀ j : Fin η.length, (Routes.digit p j).eval u = η[j] := by
    let a := packed S v h
    let f := fac S a
    have F (j : Fin (2*m)) : (f j : ZMod p).val = num (v.1 j).1.1 := unit_val ..
    have E (i : Fin (2*m)) := S8H0.GateRoutes.word_eval (fun j => Routes.A i (.fst (.fst j))) u (v.1 i).1.1 (fun _ => rfl)
    have P : Prefix S a η ↔ ∀ j : Fin η.length, (Routes.digit p j).eval u = η[j] := by
      have hdig (k : ℕ) : (Routes.digit (m:=m) (d:=width p) (e:=Routes.G (width_pos p)) p k).eval u = atDigit f (bitLen p) k := by
        unfold Routes.digit atDigit; dsimp only; split <;> first | rfl | exact (E _ _).trans (congrArg (fun n : ℕ => n.testBit _) (F _).symm)
      simp only [hdig]; unfold Prefix; rw [tuple_eq]
      have len : η.length ≤ m*2*bitLen p := by rwa [Nat.mul_comm m 2]
      constructor
      · intro eq j; have z := congrArg (fun L : List Bool => L[j.val]?) eq
        simpa [List.getElem?_take,j.isLt,show j.val < m*2*bitLen p from j.isLt.trans_le len] using z
      · intro he; apply List.ext_getElem (by simp [len]); intro j _ hj; simpa using he ⟨j,hj⟩
  
    have B (j : Fin (2*m-2)) : (num (v.2.2 j).1 : ℕ) < p := (finEquiv (primeFitsAtom p).le ⟨v.2.2 j,hr j⟩).isLt
    have Q (k : ℕ) (hk : k < 2*m) : (seq f k).val = num (v.1 ⟨k,hk⟩).1.1 := by simpa [seq,hk] using F ⟨k,hk⟩
    have I (i : Fin (2*m-1)) : (ChainLift.acc (seq f) (Y : ZMod p) v.2 i).val = inputX v i := by
      unfold ChainLift.acc inputX; split_ifs <;> first | exact Q _ _ | exact ZMod.val_natCast_of_lt (B _) | omega
    have O (i : Fin (2*m-1)) : (ChainLift.acc (seq f) (Y : ZMod p) v.2 (i+1)).val = outputZ (Y : ZMod p).val v i := by
      unfold ChainLift.acc outputZ
      rw [dif_neg (Nat.succ_ne_zero i.val)]
      by_cases hi : i.val < 2*m-2
      · rw [dif_pos hi,dif_pos (show i.val+1<2*m-1 by omega)]; exact ZMod.val_natCast_of_lt (B ⟨i,hi⟩)
      · rw [dif_neg hi,dif_neg (show ¬i.val+1<2*m-1 by omega)]
    change (Prefix S a η ∧ (∀ j, below p (v.2.2 j)) ∧ ∀ i : Fin (2*m-1), step p (ChainLift.acc (seq f) (Y : ZMod p) v.2 i).val (seq f (i+1)).val (ChainLift.acc (seq f) (Y : ZMod p) v.2 (i+1)).val (v.2.1 i)) ↔ _
    simp only [P]; constructor
    · rintro ⟨pre,_,st⟩; refine ⟨fun i => ?_,pre⟩; simpa only [I,O,Q (i.val+1) (by have := i.isLt; omega)] using st i
    · rintro ⟨st,pre⟩; refine ⟨pre,hr,fun i => ?_⟩; simpa only [I,O,Q (i.val+1) (by have := i.isLt; omega)] using st i
  constructor
  · rintro ⟨h,st,hr,pre⟩; exact ⟨h,(N h hr).mpr ⟨st,pre⟩⟩
  · rintro ⟨h,ok⟩; obtain ⟨st,pre⟩ := (N h ok.2.1).mp ok; exact ⟨h,st,ok.2.1,pre⟩

private noncomputable def bankWitness (hm : 1 ≤ m) (hη : η.length ≤ 2*m*bitLen p) :
    Witness p m T (Y : ZMod p).val (AtomLift.coeff S) η ≃ {w : Atoms (T:=T) S × ChainLift.Bank p (2*m) // rest S Y w.1 w.2 η} := by
  refine (physicalEquiv ..).trans ((Equiv.subtypeEquiv (shape p m).decode (q := fun v => ∃ h : Valid (T:=T) S v, rest S Y (packed S v h) v.2 η) ?_).trans ?_)
  · intro v; rw [rows η S Y hm hη]; have e : raw (extend v) = (shape p m).decode v := congrArg (shape p m).decode (PointGraph.dropLast.apply_symm_apply v)
    rw [e]
  exact { toFun := fun v => ⟨(packed S v.val v.2.choose,v.val.2),v.2.choose_spec⟩
          invFun := fun w => ⟨(fun j => (w.val.1 j).val,w.val.2),(fun j => (w.val.1 j).property),w.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

private noncomputable def factorsEquiv : Atoms (T:=T) S ≃ {ab : UnitPair p m // ∀ i, ab.1 i ∈ fpFactorBlock T S i ∧ ab.2 i ∈ fpFactorBlock T S i} := by
  refine (Equiv.piCongrRight (fun j => unitEquiv S (idx j) T)).trans (Equiv.subtypePiEquivPi.symm.trans (Equiv.subtypeEquiv pair ?_))
  intro f; change (∀ j, f j ∈ fpFactorBlock T S (idx j)) ↔ ∀ i, f (l i) ∈ fpFactorBlock T S i ∧ f (r i) ∈ fpFactorBlock T S i
  have L (i : Fin m) : idx (l i) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have R (i : Fin m) : idx (r i) = i := Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])
  constructor
  · intro h i; exact ⟨by simpa only [L] using h (l i),by simpa only [R] using h (r i)⟩
  · intro h j; by_cases hj : j.val < m
    · let k : Fin m := ⟨j,hj⟩; have eq : j = l k := rfl; rw [eq,L]; exact (h k).1
    · let k : Fin m := ⟨j-m,by have := j.isLt; omega⟩; have eq : j = r k := Fin.ext (by dsimp [r,k]; omega); rw [eq,R]; exact (h k).2

/-- Erasing the physical registers gives one assignment for each admissible pair. -/
noncomputable def pairSetEquiv (hm : 1 ≤ m) (hη : η.length ≤ 2*m*bitLen p) (cs : Fin m → ℕ × ℕ)
    (hs : ∀ i, cs i = AtomLift.coeff S i) : Witness p m T (Y : ZMod p).val cs η ≃ ↥(pairSet S T Y η) := by
  obtain rfl : cs = AtomLift.coeff S := funext hs; refine (bankWitness η S Y hm hη).trans ?_
  let E := factorsEquiv (T:=T) S
  have L (a : Atoms (T:=T) S) := ChainLift.chainLift (seq (fac S a)) (Y : ZMod p) (n:=2*m) (by omega)
  have eq (a : Atoms (T:=T) S) : (Y : ZMod p) = ChainLift.partialProd (seq (fac S a)) (2*m-1) ↔ (∏ i, (E a).val.1 i * (E a).val.2 i) = Y := by
    rw [prod_eq _ hm]; exact ⟨fun h => Units.ext h.symm,fun h => (congrArg Units.val h).symm⟩
  apply Equiv.ofBijective (fun w => ⟨(E w.val.1).val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(E w.val.1).property,w.2.1,(eq _).mp ((L _).1 _ w.2.2)⟩⟩)
  constructor
  · rintro ⟨⟨a,b⟩,ha⟩ ⟨⟨c,d⟩,hc⟩ h; obtain rfl : a = c := E.injective (Subtype.ext (congrArg (fun t : ↥(pairSet S T Y η) => t.val) h)); exact Subtype.ext (Prod.ext rfl (((L a).2 ((L a).1 b ha.2)).unique ha.2 hc.2))
  · rintro ⟨ab,h⟩; obtain ⟨_,hm',hp,hx⟩ := Finset.mem_filter.mp h
    obtain ⟨a,ea⟩ := E.surjective ⟨ab,hm'⟩; have e : (E a).val = ab := congrArg Subtype.val ea
    obtain ⟨b,hb,_⟩ := (L a).2 ((eq a).mpr (e ▸ hx)); exact ⟨⟨(a,b),show (tupleWord elemWord (E a).val).take η.length = η by rw [e]; exact hp,hb⟩,Subtype.ext e⟩

/-- The same bijection before erasing the two atom transcripts and shortened product run. -/
noncomputable def networkShortEquiv (hm : 1 ≤ m) (hη : η.length ≤ 2*m*bitLen p) (cs : Fin m → ℕ × ℕ)
    (hs : ∀ i, cs i = AtomLift.coeff S i) :
    {v : Bits (shape p m).size // (Routes.network (width_pos p) p m T (Y : ZMod p).val cs η).OK (extend v)} ≃
    {v : UnitPair p m × PairRun p m // FpPair.shortOK S T Y η v.1 v.2} :=
  (physicalEquiv p m T (Y : ZMod p).val cs η).symm.trans ((pairSetEquiv η S Y hm hη cs hs).trans
    (FpPair.shortEquiv w3_m5_modmul_r2 S T Y η).symm)

theorem witness_card (hm : 1 ≤ m) (hη : η.length ≤ 2*m*bitLen p) (cs : Fin m → ℕ × ℕ) (hs : ∀ i, cs i = AtomLift.coeff S i) :
    Fintype.card (Witness p m T (Y : ZMod p).val cs η) = FpPair.value T S Y η :=
  (Fintype.card_congr (pairSetEquiv η S Y hm hη cs hs)).trans (pairSet_card ..)

end Count
end DetDLP.S8L.Semantics


