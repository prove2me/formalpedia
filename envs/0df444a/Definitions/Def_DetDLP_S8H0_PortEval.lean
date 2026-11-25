-- Prove2me | Definitions.Def_DetDLP_S8H0_PortEval
-- name    : DetDLP_S8H0_PortEval
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:46:44.221152+00:00
-- url     : https://prove2.me/theorems/947a283b-2fd5-4bd8-99b6-5406e6496309
-- title:
--   Tag 0 polynomial-time port tensor evaluator
-- statement:
--   The Boolean function `PortEval.check` on a framed query word, a numeric vertex, and a local assignment is polynomial-time; so is its packet adapter. The checker agrees with the subdivision tensor on copy-cycle equality gates, original bit vertices, and subdivision edge vertices. For the remaining anchored gate vertices, `check_eq_of_gate` reduces the tensor identity to agreement of the numeric gate implementation with the typed gate. The multiplication lemma identifies the W4 evaluator on the pullback along the local incidence map. This module does not establish the numeric gate agreement hypothesis for every anchored gate.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_CoreCheck
import Theorems.Thm_Groundwork_PolyT_all

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.S8H0.PortEval
open Groundwork w4_M5Network GateRoutes
abbrev Input := List Bool × ℕ × List Bool

def fields (w : List Bool) := w5_M6Sort.decode (DetDLP_W1_Queries.second w)
def prime (w : List Bool) := (fields w).getD 0 0
def coeff (w : List Bool) : Coeff :=
  let ns := fields w
  ⟨ns.getD 1 0,ns.getD 2 0,ns.getD 3 0,ns.getD 4 0,ns.getD 5 0⟩

@[simp] theorem fields_word {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    fields (OrderPacket.word E) = [p,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val] := by
  simp [fields,OrderPacket.word,M89S1.queryWord,DetDLP_W1_Queries.second,encodeCurveInput]

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.const PolyT.prodMk PolyT.id'
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f DetDLP_W1_Queries.first_poly DetDLP_W1_Queries.more_poly
  w5_M6Sort.decode_poly PolyT.getD PolyT.mul

theorem fields_poly : PolyT fields := by unfold fields DetDLP_W1_Queries.second; fun_prop
theorem prime_poly : PolyT prime := PolyT.getD fields_poly (PolyT.const _) (PolyT.const _)

/-- Equality of the bits is independent of any permutation of the incident ports. -/
def agree (a : List Bool) := a.all (· == true) || a.all (· == false)

theorem agree_poly : PolyT agree := by
  have ht : PolyT fun a : List Bool => a.all (· == true) := PolyT.all (f := fun _ b => b == true) (by fun_prop) PolyT.id'
  have hf : PolyT fun a : List Bool => a.all (· == false) := PolyT.all (f := fun _ b => b == false) (by fun_prop) PolyT.id'
  unfold agree; fun_prop

private theorem agree_iff {n : ℕ} (a : Fin n → Bool) (k : Fin n) :
    agree (List.ofFn a) = true ↔ ∀ i, a i = a k := by
  simp only [agree,Bool.or_eq_true,List.all_eq_true,List.mem_ofFn,beq_iff_eq,forall_exists_index,forall_apply_eq_imp_iff]
  constructor
  · rintro (h|h) i <;> rw [h i,h k]
  · intro h; cases h' : a k <;> simp [h,h']

/-- A subdivision edge reads both, and only, the two halves of its wire. -/
theorem edge_eq (G : WireGraph) (T) (e : Fin G.nE) (a) : agree (List.ofFn a) =
    G.subdivisionTensor T (G.equalityVertex e) a := by
  apply Bool.eq_iff_iff.mpr
  rw [agree_iff a (G.equalityRightPort e),WireGraph.subdivisionTensor_equalityVertex,decide_eq_true_eq]
  constructor
  · exact fun h => h _
  · intro h i
    have H := (G.mem_equalityPorts_iff e _).mp (List.get_mem _ i)
    have inj : Function.Injective (G.subdivision.ports (G.equalityVertex e)).get := fun _ _ => (G.subdivision_ports_nodup _).get_inj_iff.mp
    rcases H with hl|hr
    · exact (congrArg a (inj (hl.trans (G.get_equalityLeftPort e).symm))).trans h
    · exact congrArg a (inj (hr.trans (G.get_equalityRightPort e).symm))

/-- At a bit vertex the designated representative and the full port fibre give the same equality check. -/
theorem bit_eq (A : w3_FactorLayout) (T : w3_factorTest A) (b : Fin A.nb) (a) :
    let G := w3_factorGraph A; let v := Fin.natAdd A.ng b
    agree (List.ofFn a) = G.subdivisionTensor (w3_factorChecks A T) (G.oldVertex v) a := by
  let G := w3_factorGraph A; let v := Fin.natAdd A.ng b
  let idx (e : {i : Fin A.ne // A.bit i = b}) := G.portIndex v e.val (w3_bitInc A b e.val e.property)
  let r := idx ⟨A.rep b,A.rep_bit b⟩
  apply Bool.eq_iff_iff.mpr
  rw [agree_iff a (G.oldPort v r),G.subdivisionTensor_oldVertex (w3_factorChecks A T) v a]
  simp only [v,w3_factorChecks,Fin.addCases_right,decide_eq_true_eq]
  constructor
  · exact fun h e => h _
  · intro h i
    obtain ⟨j,rfl⟩ := (G.oldPort_bijective v).surjective i
    let e := (G.ports v).get j
    have he := (G.mem_ports v e).mp (List.get_mem _ j)
    have hb : A.bit e = b := by
      rcases he with he|he <;> have hh := congrArg Fin.val he
      · change (A.gate e).val = A.ng + b.val at hh; have := (A.gate e).isLt; omega
      · apply Fin.ext; change A.ng + (A.bit e).val = A.ng + b.val at hh; omega
    have hj : idx ⟨e,hb⟩ = j := (G.ports_nodup v).get_inj_iff.mp (G.get_portIndex v e _)
    exact hj ▸ h ⟨e,hb⟩

private theorem read_ofFn {n : ℕ} (a : Fin n → Bool) : (fun i : Fin n => (List.ofFn a).getD i.val false) = a := by
  funext i; simp [List.getD_eq_getElem?_getD,i.isLt]

/-- Reference evaluation uses the graph's own port indices at original gates. -/
noncomputable def atVertex (p : ℕ) (c : Coeff) (v : ℕ) (a : List Bool) : Bool :=
  let A := PointGraph.layout p c
  let G := w3_factorGraph A
  if h : v < G.subdivision.nV then
    G.subdivisionTensor (w3_factorChecks A (PointGraph.tests p c)) ⟨v,h⟩ (fun i => a.getD i.val false)
  else false

open S8H.CopyCycle in
theorem cycle_eq {n g : ℕ} (own : Fin n → Fin g) (next : Equiv.Perm (Fin n)) (T) (b : Fin n) (a) :
    let A := layout own next; let G := w3_factorGraph A; let v := Fin.castAdd A.nb (Fin.natAdd g b)
    agree (List.ofFn a) = G.subdivisionTensor (w3_factorChecks A (checks own next T)) (G.oldVertex v) a := by
  let A := layout own next; let G := w3_factorGraph A; let u := Fin.natAdd g b; let v := Fin.castAdd n u
  let left := Fin.natAdd n (Fin.castAdd n b); let right := Fin.natAdd n (Fin.natAdd n b)
  have hl : A.gate left = u := by simp [A,left,u,layout, -Fin.natAdd_eq_addNat]
  have hr : A.gate right = u := by simp [A,right,u,layout, -Fin.natAdd_eq_addNat]
  let idx (e : Fin A.ne) (h : A.gate e = u) := G.oldPort v (G.portIndex v e (w3_gateInc A u e h))
  apply Bool.eq_iff_iff.mpr; rw [agree_iff a (idx right hr),G.subdivisionTensor_oldVertex _ v a]
  change (∀ i, a i = a (idx right hr)) ↔ w3_factorChecks A _ v _ = true
  simp only [A,layout,v,u,w3_factorChecks,Fin.addCases_left,S8H.CopyCycle.checks,Fin.addCases_right,decide_eq_true_eq]
  change (∀ i, a i = a (idx right hr)) ↔ a (idx left hl) = a (idx right hr)
  constructor
  · exact fun h => h _
  · intro h i; obtain ⟨j,rfl⟩ := (G.oldPort_bijective v).surjective i
    let e := (G.ports v).get j
    have he := (G.mem_ports v e).mp (List.get_mem _ j)
    have hu : A.gate e = u := by
      rcases he with he|he
      · exact Fin.castAdd_inj.mp he
      · have hh := congrArg Fin.val he; change A.ng+(A.bit e).val = u.val at hh; have := u.isLt; change g+n+_ = _ at hh; omega
    have eqs : ∀ f : Fin (n+(n+n)), A.gate f = u → f = left ∨ f = right := by
      intro f; induction f using Fin.addCases with
      | left k => intro h; have hh := congrArg Fin.val h; simp only [A,layout,Fin.addCases_left,Function.comp_apply,Fin.val_castAdd,u,Fin.val_natAdd] at hh; have := (own k).isLt; omega
      | right k => induction k using Fin.addCases with
        | left k =>
          intro h; left; have hh : k = b := by simpa [A,layout,u,-Fin.natAdd_eq_addNat] using h
          rw [hh]
        | right k =>
          intro h; right; have hh : k = b := by simpa [A,layout,u,-Fin.natAdd_eq_addNat] using h
          rw [hh]
    have hj : G.portIndex v e (w3_gateInc A u e hu) = j := (G.ports_nodup v).get_inj_iff.mp (G.get_portIndex v e _)
    rw [←hj]; change a (idx e hu) = _; rcases eqs e hu with H|H <;> simp only [H]; exact h

def gateCount (p : ℕ) :=
  let d := S8G.FpMoment.Code.width p + 1
  let anchors := RegisterMap.regs d + 1
  anchors + GraphBudget.sizeG d (w4_M5GraphBounds.vertexCount d)

theorem gateCount_eq (p : ℕ) (c : Coeff) : gateCount p = (PointGraph.C p c).A.ng := by
  unfold gateCount; rw [S8G.FpMoment.Code.width_eq]
  change _ = (S (GateSemantics.d p) (GateSemantics.e p)).size+1+(PointGraph.net p c).core.A.ng
  rw [GraphBudget.netG,GraphBudget.anchorSize]; rfl

@[local fun_prop] theorem gateCount_poly {α : Type} [Enc α] {p : α → ℕ} (hp : PolyT p) : PolyT (fun x => gateCount (p x)) := by
  have hd : PolyT fun x => S8G.FpMoment.Code.width (p x) + 1 := PolyT.add (S8G.FpMoment.Code.width_poly hp) (PolyT.const _)
  have hv := w4_M5Evaluator.vertexCount_poly hd
  have hr := RegisterMap.regs_poly hd
  simp only [gateCount,GraphBudget.sizeG]; fun_prop (disch := assumption)

noncomputable def original (z : Input) := atVertex (prime z.1) (coeff z.1) z.2.1 z.2.2
def dispatch (gate : Input → Bool) (z : Input) := if z.2.1 < gateCount (prime z.1) then gate z else agree z.2.2
noncomputable def reference := dispatch original

def numericGate (z : Input) := CoreCheck.gate (fields z.1) z.2.1 z.2.2
def check := dispatch numericGate

theorem dispatch_poly {gate : Input → Bool} (hg : PolyT gate) : PolyT (dispatch gate) := by
  have hc := gateCount_poly (PolyT.comp prime_poly (PolyT.fst (PolyT.id' (α := Input))))
  exact PolyT.ite' (c := fun z : Input => z.2.1 < gateCount (prime z.1)) (by fun_prop) hg (PolyT.comp agree_poly (by fun_prop))

theorem check_poly : PolyT check := dispatch_poly (CoreCheck.gate_poly (PolyT.comp fields_poly (by fun_prop)) (by fun_prop) (by fun_prop))

theorem port_poly : PolyT (S8C.portPacket check) := S8C.portPacket_poly check_poly

open S8J.CircuitRealizes in
private theorem nongate_eq {k : ℕ} (B : Block) (W : Wiring B.A.ne k) (v : Fin (G B W).subdivision.nV) (a)
    (hv : ¬ v.val < B.A.ng) : agree (List.ofFn a) = (G B W).subdivisionTensor (T B W) v a := by
  induction v using Fin.addCases with
  | right e => exact edge_eq _ _ e a
  | left v => induction v using Fin.addCases with
    | left g => induction g using Fin.addCases with
      | left g => exact False.elim (hv g.isLt)
      | right b => exact cycle_eq B.A.gate W.next B.t b a
    | right b => exact bit_eq _ _ b a

theorem reference_eq {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (v : Fin (w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivision.nV) (a) :
    reference (OrderPacket.word E,v.val,List.ofFn a) =
      (w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivisionTensor
        (w3_factorChecks _ (PointGraph.tests p (GateSemantics.coeff E))) v a := by
  have hp : prime (OrderPacket.word E) = p := by simp [prime,List.getD]
  have hc : coeff (OrderPacket.word E) = GateSemantics.coeff E := by simp [coeff,GateSemantics.coeff,List.getD]
  unfold reference dispatch; dsimp only; rw [hp,gateCount_eq p (GateSemantics.coeff E)]; split
  · change atVertex (prime (OrderPacket.word E)) (coeff (OrderPacket.word E)) v.val (List.ofFn a) = _
    rw [hp,hc]; unfold atVertex; rw [dif_pos v.isLt]
    exact congrArg ((w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivisionTensor
      (w3_factorChecks _ (PointGraph.tests p (GateSemantics.coeff E))) v) (read_ofFn a)
  · exact nongate_eq (PointGraph.C p (GateSemantics.coeff E)) (PointGraph.W p (GateSemantics.coeff E)) v a (by assumption)

theorem reference_packet_eq {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (v : Fin (w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivision.nV) (a) :
    S8C.portPacket reference (encodePortQuery (OrderPacket.word E) v.val (List.ofFn a)) =
      encodeNatListBin [if (w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivisionTensor
        (w3_factorChecks _ (PointGraph.tests p (GateSemantics.coeff E))) v a then 1 else 0] := by
  rw [S8C.portPacket_eq,reference_eq]

theorem check_eq_of_gate {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (v : Fin (w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivision.nV) (a)
    (h : v.val < (PointGraph.C p (GateSemantics.coeff E)).A.ng →
      numericGate (OrderPacket.word E,v.val,List.ofFn a) = original (OrderPacket.word E,v.val,List.ofFn a)) :
    check (OrderPacket.word E,v.val,List.ofFn a) =
      (w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivisionTensor
        (w3_factorChecks _ (PointGraph.tests p (GateSemantics.coeff E))) v a := by
  have hp : prime (OrderPacket.word E) = p := by simp [prime,List.getD]
  rw [←reference_eq]; unfold check reference dispatch; dsimp only
  rw [hp,gateCount_eq p (GateSemantics.coeff E)]; split
  · exact h (by assumption)
  · rfl

theorem check_eq_nongate {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (v : Fin (w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivision.nV) (a)
    (hv : (PointGraph.C p (GateSemantics.coeff E)).A.ng ≤ v.val) :
    check (OrderPacket.word E,v.val,List.ofFn a) =
      (w3_factorGraph (PointGraph.layout p (GateSemantics.coeff E))).subdivisionTensor
        (w3_factorChecks _ (PointGraph.tests p (GateSemantics.coeff E))) v a :=
  check_eq_of_gate E v a (fun h => False.elim (Nat.not_lt_of_ge hv h))

open w4_M5GraphBounds w4_M5PortTensor w4_M5Dispatch in
private theorem mul_tensor (q : List Unit) (hd : 1 ≤ q.length) (v : Fin (vertexCount q.length)) (a) :
    evalNat q v.val (List.ofFn a) = tensor hd v a := by
  let u := (vertexIndex q.length).symm v
  have hi : vertexIndex q.length u = v := (vertexIndex q.length).apply_symm_apply v
  have h := evalNat_at q hd u (List.ofFn a)
  rw [hi] at h
  exact h.trans ((w4_M5GateEq.gate_eq q hd v (List.ofFn a) u).trans (by
    unfold tensor; congr 2; funext i; simp [i.isLt]))

/-- The multiplication evaluator consumes the original W4 port order.  In particular
    a raw incidence assignment is pulled back along `w3_m5LocalInc` before dispatch. -/
theorem mul_eq {d : ℕ} (hd : 1 ≤ d) (v : Fin (w3_fpMulLayout d hd).ng) (a) :
    S8J.HashGatePoly.mulLayoutCheck d v.val
      (List.ofFn fun j => a (w3_m5LocalInc (w3_forgetSides (w4_M5GraphBounds.graph d hd)) v j)) =
      w3_fpMulTests d hd v a := by
  generalize hq : List.replicate d () = q
  have hw : q.length = d := by simp [←hq]
  subst d
  unfold S8J.HashGatePoly.mulLayoutCheck
  rw [hq]; exact mul_tensor q hd v _

end DetDLP.S8H0.PortEval


