-- Prove2me | Definitions.Def_DetDLP_M3B_ECSliceLift
-- name    : DetDLP_M3B_ECSliceLift
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:38:30.973801+00:00
-- url     : https://prove2.me/theorems/94784a55-7bac-4de3-8b5e-d74d5128374c
-- title:
--   Canonical elliptic-curve map and addition register slices
-- statement:
--   Each accepting map or addition cell reads exactly the canonical checked slice for its point inputs, including the slope selection and every range and hash auxiliary register. The point-copy rows enforce equality of the entire point cell.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECChainBlocks

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace DetDLP.M3B.ECSliceLift
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows GateRoutes RangeRows
open ECMapRows ECChainBlocks S8H.ECPointArithmetic S8K.ECAddArithmetic
variable {s : Shape} {d p : ℕ}

/-- Read every register under a path, including the proof words. -/
def readPath : {q : Shape} → Path q s → Bits (s.size+1) → q.Data
  | .bit, f, v => (Ref.reg (f .bit)).eval v
  | .word _, f, v => fun j => (Ref.reg (f (.word j))).eval v
  | .pair _ _, f, v => (readPath (fstP f) v, readPath (sndP f) v)
  | .vec _ _, f, v => fun i => readPath (fun j => f (.vec i j)) v

theorem at_read {q : Shape} (f : Path q s) (v : Bits (s.size+1)) : At f v (readPath f v) := by
  intro a; induction a with
  | bit => rfl
  | word => rfl
  | fst a ih => exact ih (fstP f)
  | snd a ih => exact ih (sndP f)
  | vec i a ih => exact ih (fun n => f (.vec i n))

theorem read_of_at {q : Shape} {f : Path q s} {v : Bits (s.size+1)} {u : q.Data} (h : At f v u) : readPath f v = u := by
  induction q with
  | bit => exact h .bit
  | word n => exact funext fun j => h (.word j)
  | pair a b ia ib => exact Prod.ext (ia (f:=fstP f) (fun j => h (.fst j))) (ib (f:=sndP f) (fun j => h (.snd j)))
  | vec n a ih => exact funext fun i => ih (f:=fun j => f (.vec i j)) (fun j => h (.vec i j))

theorem tripleEq_iff (f g : Path (triple d) s) (v : Bits (s.size+1)) :
    (tripleEq f g).OK v ↔ readPath f v = readPath g v := by
  simp only [tripleEq, wordEqB, joinB_iff, eqs_iff, triple, readPath, refw]
  constructor
  · intro h; exact Prod.ext (funext h.1) (Prod.ext (funext h.2.1) (funext h.2.2))
  · intro h; exact ⟨congrFun (congrArg Prod.fst h), congrFun (congrArg (fun u => u.2.1) h), congrFun (congrArg (fun u => u.2.2) h)⟩

theorem pointEq_iff (f g : Path (PointCell d) s) (v : Bits (s.size+1)) :
    (pointEq f g).OK v ↔ readPath f v = readPath g v := by
  simp only [pointEq, joinB_iff, tripleEq_iff, eqs_iff, Fin.forall_fin_one]
  change (_ ∧ _ ∧ _) ↔ (_, (_, _)) = (_, (_, _))
  simp only [Prod.mk.injEq]; rfl

def boundedAt (f : Path (triple d) s) (v : Bits (s.size+1)) (h : (checker p f).OK v) : Bounded (d:=d) p :=
  ⟨readPath f v, (checker_iff p f v _ (at_read f v)).mp h⟩

def gateAtPath (f : Path (slot (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1))
    (h : (checker p (result f)).OK v ∧ (checker p (remain f)).OK v) : CheckedRun (width p) p (GateSemantics.hd p) × AuxBank (width p) :=
  let u := readPath f v
  ((boundedAt _ v h.1, (boundedAt _ v h.2, u.1.2.1.2), u.1.2.2), u.2)

def pointAtPath (f : Path (PointCell (width p)) s) (v : Bits (s.size+1))
    (h : (checker p (fstP (sndP f))).OK v ∧ (checker p (sndP (sndP f))).OK v) : Bool × ECAddRows.Bd p × ECAddRows.Bd p :=
  ((readPath f v).1, boundedAt _ v h.1, boundedAt _ v h.2)

noncomputable def mapSlice (f : Path (mapShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1))
    {b a c : ℕ} {i : Ref s} {x y : Word s} (h : (mapBlock (GateSemantics.hd p) p b a c i x y f).OK v) : ECMapRows.Slice p := by
  let r := (joinB_iff ..).mp h |>.1
  have z := (joinB_iff ..).mp r
  exact (pointAtPath (fstP f) v ((joinB_iff ..).mp z.1), fun j =>
    gateAtPath (fun n => f (.snd (.vec j n))) v ((joinB_iff ..).mp (((many_iff ..).mp z.2) j)))

theorem at_mapSlice (f : Path (mapShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1))
    {b a c : ℕ} {i : Ref s} {x y : Word s} (h : (mapBlock (GateSemantics.hd p) p b a c i x y f).OK v) :
    At f v (sliceData (mapSlice f v h)) := at_read f v

abbrev addGate (f : Path (ECAddRows.addShape (width p) (GateSemantics.e p)) s) (k : Fin 15) :
    Path (slot (width p) (GateSemantics.e p)) s := fun n => f (.snd (.snd (.snd (.vec k n))))
abbrev control (f : Path (ECAddRows.addShape (width p) (GateSemantics.e p)) s) (k : Fin 2) :
    Path (.pair .bit (triple (width p))) s := fun n => f (.snd (.fst (.vec k n)))

section Add
variable (f : Path (ECAddRows.addShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1))
variable {m o t c : ℕ} {i j : Ref s} {x y z w : Word s}
variable (h : (ECAddRows.addBlock (GateSemantics.hd p) p m o t c i j x y z w f).OK v)

noncomputable def addSlice : ECAddRows.Slice p := by
  let r := (joinB_iff ..).mp h |>.1
  have a := (joinB_iff ..).mp r
  have b := (joinB_iff ..).mp a.2
  exact ⟨pointAtPath (fstP f) v ((joinB_iff ..).mp a.1),
    fun k => ((readPath (control f k) v).1, boundedAt _ v (((many_iff ..).mp b.1) k)),
    fun k => gateAtPath (addGate f k) v ((joinB_iff ..).mp (((many_iff ..).mp b.2) k))⟩

variable [Fact p.Prime]
theorem at_addSlice : At f v (ECAddRows.sliceData (i.eval v) (j.eval v) (addSlice f v h)) := by
  let u := addSlice f v h
  let b := fun k : Fin 2 => (u.zi k).1
  let Rv := fun k : Fin 15 => (R (u.gates k).1).1
  let A := readPath f v
  have branch := (joinB_iff ..).mp ((joinB_iff ..).mp ((joinB_iff ..).mp ((joinB_iff ..).mp ((joinB_iff ..).mp h).2).2).2).2 |>.1
  have gr (g : Fin 15) : evalWord (rwrd (result (addGate f g))) v (Rv g).val := by
    change evalWord _ _ (Z (u.gates g).1.1).val
    rw [GateSemantics.resVal]; exact wordAt (at_read (fstP (result (addGate f g))) v)
  let l := word (fstP (sndP (sndP f)))
  have hs (k : Fin (width p)) := (rows_iff ..).mp branch k
  have hslope (k : Fin (width p)) : A.2.2.1 k =
      (if !(i.eval v) && !(j.eval v) && !(b 0) then Rv 5 else if !(i.eval v) && !(j.eval v) && b 0 && !(b 1) then Rv 8 else 0).val.testBit k := by
    have hh := (beq_iff_eq ..).mp (hs k)
    change (l k.val).eval v = (if !(i.eval v) && !(j.eval v) && !(b 0) then (rwrd (result (addGate f 5)) k.val).eval v else if !(i.eval v) && !(j.eval v) && b 0 && !(b 1) then (rwrd (result (addGate f 8)) k.val).eval v else (pub 0 k.val).eval v) at hh
    rw [gr 5 k, gr 8 k] at hh
    change (padded _ k.val).eval v = _ at hh
    simp only [padded, dif_pos k.isLt] at hh
    split <;> rename_i hb <;> simp only [hb, if_true] at hh
    · exact hh
    · split <;> rename_i hc <;> simp only [hc, if_true] at hh
      · exact hh
      · change A.2.2.1 k = (0 : ZMod p).val.testBit k
        rw [ZMod.val_zero]; exact hh
  have H : A = ECAddRows.sliceData (i.eval v) (j.eval v) u :=
    Prod.ext rfl (Prod.ext rfl (Prod.ext (funext hslope) rfl))
  rw [← H]; exact at_read f v
end Add

section Build
variable [Fact p.Prime]
noncomputable abbrev PointEqv := (Equiv.refl Bool).prodCongr ((Z (p:=p)).prodCongr (Z (p:=p)))
abbrev GateCell (p : ℕ) := CheckedRun (width p) p (GateSemantics.hd p) × AuxBank (width p)
noncomputable def buildGate (r : Run p) (a : GateAux p) : GateCell p := (R.symm r, (auxEquiv _).symm a.1)
noncomputable def cellAux (g : GateCell p) : GateAux p :=
  (auxEquiv _ g.2, value g.1.1.val.2.1, g.1.1.val.2.2)
@[simp] theorem gate_run (r : Run p) (a : GateAux p) : R (buildGate r a).1 = r := R.apply_symm_apply _
@[simp] theorem gate_round (g : GateCell p) : buildGate (R g.1) (cellAux g) = g :=
  Prod.ext (R.symm_apply_apply _) ((auxEquiv _).symm_apply_apply _)
theorem gate_aux (r : Run p) (a : GateAux p) (h : w3_slotLt (width p) r.1.val p a.2) : cellAux (buildGate r a) = a := by
  let g := buildGate r a
  apply Prod.ext ((auxEquiv _).apply_symm_apply _)
  apply ((w3_slotLt_spec (d:=width p) (r.1.val_lt.trans (fits p)) (fits p).le).2 r.1.val_lt).unique _ h
  have he := congrArg (fun z : Run p => z.1.val) (gate_run r a)
  change (Z g.1.1).val = r.1.val at he
  rw [← he, GateSemantics.resVal]; exact (below_iff _ _).mp g.1.1.property
abbrev mapAux (p : ℕ) := ((GateAux p × GateAux p × GateAux p × GateAux p × Unit) × Unit)
noncomputable def mapBuild (o : Coords p) (c : MapCert p) (a : mapAux p) : ECMapRows.Slice p :=
  ⟨PointEqv.symm o,
   ![buildGate c.1 a.1.1,
     buildGate c.2.1 a.1.2.1,
     buildGate c.2.2.1 a.1.2.2.1,
     buildGate c.2.2.2.1 a.1.2.2.2.1]⟩

theorem mapBuild_output (o : Coords p) (c : MapCert p) (a : mapAux p) : ECMapRows.output (mapBuild o c a) = o := PointEqv.apply_symm_apply _
theorem mapBuild_cert (o : Coords p) (c : MapCert p) (a : mapAux p) : ECMapRows.cert (mapBuild o c a) = c := by
  change (R (buildGate c.1 a.1.1).1, R (buildGate c.2.1 a.1.2.1).1, R (buildGate c.2.2.1 a.1.2.2.1).1, R (buildGate c.2.2.2.1 a.1.2.2.2.1).1, ()) = c
  simp only [gate_run]

theorem mapBuild_aux (E : WeierstrassCurve (ZMod p)) (q o : Coords p) (c : MapCert p) (a : mapAux p) (h : (ECMapRows.mapChecks' E q o c).bits a) :
    ECMapRows.auxBits (mapBuild o c a) = a := by
  change ((cellAux (buildGate c.1 a.1.1), cellAux (buildGate c.2.1 a.1.2.1), cellAux (buildGate c.2.2.1 a.1.2.2.1), cellAux (buildGate c.2.2.2.1 a.1.2.2.2.1), ()), ()) = a
  rw [gate_aux _ _ h.1.1.2,
      gate_aux _ _ h.1.2.1.2,
      gate_aux _ _ h.1.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.1.2]

theorem mapBuild_round (u : ECMapRows.Slice p) : mapBuild (ECMapRows.output u) (ECMapRows.cert u) (ECMapRows.auxBits u) = u := by
  apply Prod.ext
  · exact PointEqv.symm_apply_apply _
  · funext k; fin_cases k <;> exact gate_round _

abbrev addAux (p : ℕ) := ((GateAux p × (GateAux p × Unit) × GateAux p × (GateAux p × Unit) × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × Unit) × Unit)
noncomputable def addBuild (o : Coords p) (c : AddCert p) (a : addAux p) : ECAddRows.Slice p :=
  ⟨PointEqv.symm o, ![(c.2.1.1, Z.symm c.2.1.2.1), (c.2.2.2.1.1, Z.symm c.2.2.2.1.2.1)],
   ![buildGate c.1 a.1.1,
     buildGate c.2.1.2.2 a.1.2.1.1,
     buildGate c.2.2.1 a.1.2.2.1,
     buildGate c.2.2.2.1.2.2 a.1.2.2.2.1.1,
     buildGate c.2.2.2.2.1 a.1.2.2.2.2.1,
     buildGate c.2.2.2.2.2.1 a.1.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]⟩

theorem addBuild_output (o : Coords p) (c : AddCert p) (a : addAux p) : ECAddRows.output (addBuild o c a) = o := PointEqv.apply_symm_apply _
theorem addBuild_cert (o : Coords p) (c : AddCert p) (a : addAux p) : ECAddRows.cert (addBuild o c a) = c := by
  change (R (buildGate c.1 a.1.1).1, (c.2.1.1, Z (Z.symm c.2.1.2.1), R (buildGate c.2.1.2.2 a.1.2.1.1).1), R (buildGate c.2.2.1 a.1.2.2.1).1, (c.2.2.2.1.1, Z (Z.symm c.2.2.2.1.2.1), R (buildGate c.2.2.2.1.2.2 a.1.2.2.2.1.1).1), R (buildGate c.2.2.2.2.1 a.1.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.1 a.1.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1, R (buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1, ()) = c
  simp only [gate_run, Equiv.apply_symm_apply]

theorem addBuild_aux (E : WeierstrassCurve (ZMod p)) (q q₂ o : Coords p) (c : AddCert p) (a : addAux p) (h : (ECAddRows.addChecks' E q q₂ o c).bits a) :
    ECAddRows.auxBits (addBuild o c a) = a := by
  change ((cellAux (buildGate c.1 a.1.1), (cellAux (buildGate c.2.1.2.2 a.1.2.1.1), ()), cellAux (buildGate c.2.2.1 a.1.2.2.1), (cellAux (buildGate c.2.2.2.1.2.2 a.1.2.2.2.1.1), ()), cellAux (buildGate c.2.2.2.2.1 a.1.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.1 a.1.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1), cellAux (buildGate c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), ()), ()) = a
  rw [gate_aux _ _ h.1.1.2,
      gate_aux _ _ h.1.2.1.1.2,
      gate_aux _ _ h.1.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.1.1.2,
      gate_aux _ _ h.1.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.2.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2,
      gate_aux _ _ h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2]

theorem addBuild_round (u : ECAddRows.Slice p) : addBuild (ECAddRows.output u) (ECAddRows.cert u) (ECAddRows.auxBits u) = u := by
  rcases u with ⟨pt, z, g⟩; apply ECAddRows.Slice.mk.injEq _ _ _ _ _ _ |>.mpr
  constructor
  · exact PointEqv.symm_apply_apply _
  · constructor
    · funext k; fin_cases k <;> exact Prod.ext rfl (Z.symm_apply_apply _)
    · funext k; fin_cases k <;> exact gate_round _

theorem mapUnique (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p) (P : E.toAffine.Point) :
    ∃! u : ECMapRows.Slice p, (ECMapRows.mapChecks' E (coords P) (ECMapRows.output u) (ECMapRows.cert u)).bits (ECMapRows.auxBits u) := by
  let o := (coords (S8K.SWEquiv.equiv E (S8K.SWEquiv.six_ne_zero hp) P))
  obtain ⟨c,hc,uc⟩ := ecToSW_unique E hp w3_m5_modmul_r2 P
  obtain ⟨a,ha,ua⟩ := (ECMapRows.mapChecks_lift E (coords P) o c).2 hc
  let u := mapBuild o c a
  have ho : ECMapRows.output u = o := mapBuild_output ..
  have hh : ECMapRows.cert u = c := mapBuild_cert ..
  have haux : ECMapRows.auxBits u = a := mapBuild_aux E (coords P) o c a ha
  refine ⟨u, by simpa only [ho,hh,haux] using ha, ?_⟩
  intro t ht
  have ok := (ECMapRows.mapChecks_lift E (coords P) _ _).1 _ ht
  have ot : ECMapRows.output t = o := ecToSW_sound E hp w3_m5_modmul_r2 P _ _ ok
  rw [ot] at ok ht
  have tc := uc _ ok
  rw [tc] at ht
  rw [← mapBuild_round t, ot, tc, ua _ ht]

theorem addUnique (E : WeierstrassCurve (ZMod p)) (P Q : (S8K.SWEquiv.short E).toAffine.Point) :
    ∃! u : ECAddRows.Slice p, (ECAddRows.addChecks' E (coords P) (coords Q) (ECAddRows.output u) (ECAddRows.cert u)).bits (ECAddRows.auxBits u) := by
  let o := (coords (P+Q))
  obtain ⟨c,hc,uc⟩ := swAdd_unique E w3_m5_modmul_r2 P Q
  obtain ⟨a,ha,ua⟩ := (ECAddRows.addChecks_lift E (coords P) (coords Q) o c).2 hc
  let u := addBuild o c a
  have ho : ECAddRows.output u = o := addBuild_output ..
  have hh : ECAddRows.cert u = c := addBuild_cert ..
  have haux : ECAddRows.auxBits u = a := addBuild_aux E (coords P) (coords Q) o c a ha
  refine ⟨u, by simpa only [ho,hh,haux] using ha, ?_⟩
  intro t ht
  have ok := (ECAddRows.addChecks_lift E (coords P) (coords Q) _ _).1 _ ht
  have ot : ECAddRows.output t = o := swAdd_sound E w3_m5_modmul_r2 P Q _ _ ok
  rw [ot] at ok ht
  have tc := uc _ ok
  rw [tc] at ht
  rw [← addBuild_round t, ot, tc, ua _ ht]

noncomputable def mapCell (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p) (P : E.toAffine.Point) := (mapUnique E hp P).exists.choose

theorem mapCell_output (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p) (P : E.toAffine.Point) : ECMapRows.output (mapCell E hp P) = coords (S8K.SWEquiv.equiv E (S8K.SWEquiv.six_ne_zero hp) P) :=
  ecToSW_sound E hp w3_m5_modmul_r2 P _ _ ((ECMapRows.mapChecks_lift ..).1 _ (mapUnique E hp P).exists.choose_spec)

theorem mapBlock_at (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p) (P : E.toAffine.Point)
    (f : Path (ECMapRows.mapShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1)) (i : Ref s) (x y : Word s)
    (I : i.eval v = (coords P).1) 
    (X : evalWord x v (coords P).2.1.val) (Y : evalWord y v (coords P).2.2.val)  :
    (mapBlock (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val i x y f).OK v ↔ At f v (ECMapRows.sliceData (mapCell E hp P)) := by
  constructor
  · intro h
    let u := mapSlice f v h
    have hu := at_mapSlice f v h
    
    have hh := (ECMapRows.mapBlock_iff E (coords P) u f v i x y hu I X Y).mp h
    have eq : u = mapCell E hp P := (mapUnique E hp P).unique hh (mapUnique E hp P).exists.choose_spec
    rw [← eq]; exact hu
  · intro h
    exact (ECMapRows.mapBlock_iff E (coords P) _ f v i x y h I X Y).mpr (mapUnique E hp P).exists.choose_spec

noncomputable def addCell (E : WeierstrassCurve (ZMod p)) (P Q : (S8K.SWEquiv.short E).toAffine.Point) := (addUnique E P Q).exists.choose

theorem addCell_output (E : WeierstrassCurve (ZMod p)) (P Q : (S8K.SWEquiv.short E).toAffine.Point) : ECAddRows.output (addCell E P Q) = coords (P+Q) :=
  swAdd_sound E w3_m5_modmul_r2 P Q _ _ ((ECAddRows.addChecks_lift ..).1 _ (addUnique E P Q).exists.choose_spec)

theorem addBlock_at (E : WeierstrassCurve (ZMod p)) (P Q : (S8K.SWEquiv.short E).toAffine.Point)
    (f : Path (ECAddRows.addShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1)) (i j : Ref s) (x y z w : Word s)
    (I : i.eval v = (coords P).1) (J : j.eval v = (coords Q).1)
    (X : evalWord x v (coords P).2.1.val) (Y : evalWord y v (coords P).2.2.val) (D : evalWord z v (coords Q).2.1.val) (W : evalWord w v (coords Q).2.2.val) :
    (ECAddRows.addBlock (GateSemantics.hd p) p (-1 : ZMod p).val (1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val i j x y z w f).OK v ↔ At f v (ECAddRows.sliceData (coords P).1 (coords Q).1 (addCell E P Q)) := by
  constructor
  · intro h
    let u := addSlice f v h
    have hu := at_addSlice f v h
    rw [I,J] at hu
    have hh := (ECAddRows.addBlock_iff E (coords P) (coords Q) u f v i j x y z w hu I J X Y D W).mp h
    have eq : u = addCell E P Q := (addUnique E P Q).unique hh (addUnique E P Q).exists.choose_spec
    rw [← eq]; exact hu
  · intro h
    exact (ECAddRows.addBlock_iff E (coords P) (coords Q) _ f v i j x y z w h I J X Y D W).mpr (addUnique E P Q).exists.choose_spec

end Build

end DetDLP.M3B.ECSliceLift


