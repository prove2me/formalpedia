-- Prove2me | Definitions.Def_DetDLP_D4SoloRoot
-- name    : DetDLP_D4SoloRoot
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T16:25:41.402031+00:00
-- url     : https://prove2.me/theorems/d1e3806e-2cc3-4e85-b61f-0e0eeb04a5b6
-- title:
--   Solo Root Cut-Core Node and Exact Contraction Bridge
-- statement:
--   Defines the machine-level helpers and root SoloNode built from D4CoreCut.cutCore, proves exact work-item bit-encoding equality with rootRaw (cutCoreRaw (input x)) x.p, and proves equality between the base-lifted contraction of x.G and the boundary-summed contraction of rootSoloNode.
-- source:
--   prove2me_m14_solo/Definitions/Def_DetDLP_D4SoloRoot.lean

import Definitions.Def_DetDLP_D4SoloNode

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace DetDLP.D4SoloRoot

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker
open DetDLP.D4SoloRaw DetDLP.D4SoloNode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

section MachineUtils

theorem trace_det_halt {α : Type} {step : α → Option α} {n₁ n₂ : ℕ} {a b₁ b₂ : α}
    (h₁ : Trace step n₁ a b₁) (s₁ : step b₁ = none)
    (h₂ : Trace step n₂ a b₂) (s₂ : step b₂ = none) : n₁ = n₂ ∧ b₁ = b₂ := by
  induction h₁ generalizing n₂ with
  | refl =>
    cases h₂ with
    | refl => exact ⟨rfl, rfl⟩
    | cons hs _ => rw [s₁] at hs; cases hs
  | cons hs₁ _ ih =>
    cases h₂ with
    | refl => rw [s₂] at hs₁; cases hs₁
    | cons hs₂ ht₂ =>
      cases Option.some.inj (hs₁.symm.trans hs₂)
      obtain ⟨hn, hb⟩ := ih s₁ ht₂
      exact ⟨congrArg Nat.succ hn, hb⟩

theorem mk1_map_some_inj {xs ys : List Bool}
    (h : Turing.Tape.mk₁ (xs.map some) = Turing.Tape.mk₁ (ys.map some)) : xs = ys := by
  apply List.ext_getElem?
  intro k
  have hk := congrArg (fun t : Turing.Tape (Option Bool) => t.nth (k : ℤ)) h
  simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat,
    Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD, List.getElem?_map] at hk
  have hdef : (default : Option Bool) = none := rfl
  cases hx : xs[k]? <;> cases hy : ys[k]? <;> simp_all

theorem runsWithin_unique {A : PrimitiveMachine} {o : Fin A.tapeCount}
    {inp out₁ out₂ : List Bool} {τ₁ σ₁ τ₂ σ₂ : ℝ}
    (h₁ : RunsWithin A o inp out₁ τ₁ σ₁) (h₂ : RunsWithin A o inp out₂ τ₂ σ₂) :
    out₁ = out₂ := by
  obtain ⟨_, f₁, tr₁, ⟨b₁, hb₁⟩, ho₁, _, _⟩ := h₁
  obtain ⟨_, f₂, tr₂, ⟨b₂, hb₂⟩, ho₂, _, _⟩ := h₂
  have sf₁ : locatedStep A f₁ = none := by simp [locatedStep, PrimitiveMachine.step, hb₁]
  have sf₂ : locatedStep A f₂ = none := by simp [locatedStep, PrimitiveMachine.step, hb₂]
  obtain ⟨_, rfl⟩ := trace_det_halt tr₁ sf₁ tr₂ sf₂
  exact mk1_map_some_inj (ho₁.symm.trans ho₂)

theorem runsWithin_input_len_le {A : PrimitiveMachine} {o : Fin A.tapeCount}
    {inp out : List Bool} {τ σ : ℝ}
    (h : RunsWithin A o inp out τ σ) : (inp.length : ℝ) ≤ σ := by
  obtain ⟨t, _, _, _, _, _, hs⟩ := h
  have h0 := hs 0 (locatedInit A inp) (Nat.zero_le t) (.refl _)
  have hterm : inp.length ≤ visitedSpace (locatedInit A inp) := by
    have hsingle : (((locatedInit A inp).upper A.inputTape -
        (locatedInit A inp).lower A.inputTape + 1).toNat) ≤
        ∑ i : Fin A.tapeCount, (((locatedInit A inp).upper i -
          (locatedInit A inp).lower i + 1).toNat) :=
      Finset.single_le_sum (f := fun i : Fin A.tapeCount =>
        ((locatedInit A inp).upper i - (locatedInit A inp).lower i + 1).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ A.inputTape)
    have hval : inp.length ≤ ((locatedInit A inp).upper A.inputTape -
        (locatedInit A inp).lower A.inputTape + 1).toNat := by
      simp only [locatedInit, ↓reduceIte, sub_zero]
      cases inp <;> simp
    exact hval.trans hsingle
  exact (by exact_mod_cast hterm : (inp.length : ℝ) ≤ visitedSpace (locatedInit A inp)).trans h0

end MachineUtils

section AlgebraAndPredicates

noncomputable section

theorem self_lift {f : ℤ[X]} {l p : ℕ} (hf : f.Monic) (z : B f l p) :
    lift hf p z = z := by
  have cell (x : U f p) :
      AdjoinRoot.mk _ (∑ i : Fin f.natDegree,
        monomial i.val (((AdjoinRoot.modByMonicHom (hf.map _) x).coeff i.val).val : ZMod (2 ^ p))) = x := by
    simp only [ZMod.natCast_zmod_val]
    have he := sum_modByMonic_coeff (hf.map (Int.castRingHom (ZMod (2 ^ p))))
      (p := AdjoinRoot.modByMonicHom (hf.map _) x) (degree_map_le.trans (degree_le_natDegree (p := f)))
    rw [← AdjoinRoot.modByMonicHom_mk (hf.map _), AdjoinRoot.mk_leftInverse (hf.map _) x] at he
    rw [he, AdjoinRoot.mk_leftInverse]
  unfold lift word
  simp only [cell]
  have he := sum_modByMonic_coeff (monic_X_pow l : ((X : (U f p)[X]) ^ l).Monic)
    (p := AdjoinRoot.modByMonicHom (monic_X_pow l) z) (degree_X_pow_le _)
  rw [← AdjoinRoot.modByMonicHom_mk (monic_X_pow l), AdjoinRoot.mk_leftInverse (monic_X_pow l) z] at he
  rw [he, AdjoinRoot.mk_leftInverse]

theorem shift_mono_solo (S : ℕ) : Monotone (D3Stopped.shift S) := by
  refine monotone_nat_of_le_succ fun t => ?_
  simp only [D3Stopped.shift, Finset.sum_range_succ, Nat.mul_add]
  omega

def pktOKOf (E_pkt : PrimitiveMachine) (oe : Fin E_pkt.tapeCount) (K_loc : ℕ)
    {C c : ℕ} (x : Input C c) (f : ℤ[X]) (hf : f.Monic) : PktPred f x.l :=
  fun dCreate pCreate origDeg rawDesc entry₀ =>
    let n₀ := pCreate + 4 * D3Stopped.level x.S + x.l + 2
    1 ≤ pCreate ∧
    pCreate ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S dCreate ∧
    origDeg ≤ 2 * 2 ^ D3Stopped.shift x.S dCreate ∧
    (rawDesc.length : ℝ) ≤ polyBound K_loc n₀ ∧
    ∀ α : Fin origDeg → Bool,
      RunsWithin E_pkt oe (Encoding.encodeList id [rawDesc, List.ofFn α])
        (residue f x.l pCreate hf (entry₀ α))
        (Real.exp ((K_loc : ℝ) * (2 ^ D3Stopped.shift x.S dCreate : ℕ) * Real.log n₀))
        (polyBound K_loc n₀)

theorem soloNode_toWorkItem_bits {C c : ℕ} {x : Input C c} {f : ℤ[X]} {PktOK : PktPred f x.l}
    (nd : SoloNode x f PktOK) (d : ℕ) (G : BipartiteMultigraph) (pCurr : ℕ)
    (pins : List (Fin (4 * x.m * x.k) × Fin G.nV))
    (verts : ∀ w : Fin G.nV, SoloVert x G f PktOK pCurr d w)
    (hd : nd.d = d) (hG : nd.G = G) (hp : nd.pCurr = pCurr)
    (hpins : HEq nd.pins pins) (hverts : HEq nd.verts verts) :
    nd.toWorkItem.bits =
      pack [countWord d, G.encode, countWord pCurr,
        pack (pins.map (fun pv => encodeNatListBin [pv.1.val, pv.2.val])),
        pack (List.ofFn fun w => (verts w).specBits)] := by
  cases nd; subst hd hG hp; cases hpins; cases hverts
  simp only [SoloNode.toWorkItem, WorkItem.bits, List.map_map, Function.comp_def]

end

end AlgebraAndPredicates

section RootNode

noncomputable section

theorem getD_ofFn_unit {n : ℕ} (fn : Fin n → ℕ) (k : Fin n) :
    (List.ofFn fn).getD k.val 0 = fn k := by
  have hlen : k.val < (List.ofFn fn).length := by simp [k.isLt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_ofFn, Option.getD_some]

noncomputable abbrev rootCut {C c : ℕ} (x : Input C c) :
    D4CoreCut.Cut x.G x.spec.lookupVerts :=
  D4CoreCut.cutCore x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec)

private theorem rootCut_host_inj {C c : ℕ} (x : Input C c) :
    Function.Injective (rootCut x).host := by
  intro a b hab
  have hSpec := (d4_core_cut_poly_and_spec.2 x).2.2.2.2.2.1
  have hEq : (D4CoreCut.cutCore x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec)).host a =
      (D4CoreCut.cutCore x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec)).host b := hab
  exact Finset.card_le_one.mp (hSpec a) a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEq⟩)

private theorem root_cut_deg_pos {C c : ℕ} (x : Input C c)
    (j : Fin (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length) :
    let t := rootCut x
    1 ≤ t.H₀.deg (t.host j) := by
  intro t
  let L := x.spec.lookupVerts
  let e_b := D4CoreCut.origB x.G L j
  have hbd := D4CoreCut.boundary_ok x.G L j
  have hv_sub : t.orig (t.host j) ∈ x.spec.termSubdivVerts := by
    change D4CoreCut.origV x.G L (D4CoreCut.host₀ x.G L (D4CoreCut.independent_of_spec x.G x.spec) j) ∈ x.spec.termSubdivVerts
    dsimp only [D4CoreCut.host₀]
    split_ifs with ha
    · rw [D4CoreCut.orig_vidx]; exact (x.spec.lookup_edges_to_subdiv e_b).1 ha
    · rw [D4CoreCut.orig_vidx]; exact (x.spec.lookup_edges_to_subdiv e_b).2 (hbd.resolve_left ha)
  let v₀ := t.orig (t.host j)
  have hdeg2 : (x.G.ports v₀).length = 2 := x.spec.subdiv_deg v₀ hv_sub
  have he_b_mem : e_b ∈ x.G.ports v₀ := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange _, decide_eq_true ?_⟩
    change (x.G.endpoints e_b).1 = D4CoreCut.origV x.G L (D4CoreCut.host₀ x.G L (D4CoreCut.independent_of_spec x.G x.spec) j) ∨
      (x.G.endpoints e_b).2 = D4CoreCut.origV x.G L (D4CoreCut.host₀ x.G L (D4CoreCut.independent_of_spec x.G x.spec) j)
    dsimp only [D4CoreCut.host₀]
    split_ifs with ha
    · rw [D4CoreCut.orig_vidx]; right; rfl
    · rw [D4CoreCut.orig_vidx]; left; rfl
  have hnodup : (x.G.ports v₀).Nodup := (List.nodup_finRange _).filter _
  obtain ⟨e₁, he₁_mem, he₁_ne⟩ : ∃ e₁ ∈ x.G.ports v₀, e₁ ≠ e_b := by
    cases hp : x.G.ports v₀ with
    | nil => simp [hp] at hdeg2
    | cons a as =>
      cases as with
      | nil => simp [hp] at hdeg2
      | cons b bs =>
        by_cases ha : a = e_b
        · refine ⟨b, ?_, ?_⟩
          · simp
          · intro hba
            rw [hp] at hnodup
            exact (List.nodup_cons.mp hnodup).1 (by simp [ha, hba])
        · exact ⟨a, by simp, ha⟩
  have hv₀_not_L : v₀ ∉ L := Finset.disjoint_right.mp x.spec.disjoint_verts hv_sub
  have he₁_inc : (x.G.endpoints e₁).1 = v₀ ∨ (x.G.endpoints e₁).2 = v₀ :=
    of_decide_eq_true (List.mem_filter.mp he₁_mem).2
  have he_b_cross : ((x.G.endpoints e_b).1 = v₀ ∧ (x.G.endpoints e_b).2 ∈ L) ∨
      ((x.G.endpoints e_b).2 = v₀ ∧ (x.G.endpoints e_b).1 ∈ L) := by
    change ((x.G.endpoints e_b).1 = D4CoreCut.origV x.G L (D4CoreCut.host₀ x.G L (D4CoreCut.independent_of_spec x.G x.spec) j) ∧ _) ∨
      ((x.G.endpoints e_b).2 = D4CoreCut.origV x.G L (D4CoreCut.host₀ x.G L (D4CoreCut.independent_of_spec x.G x.spec) j) ∧ _)
    dsimp only [D4CoreCut.host₀]
    split_ifs with ha
    · rw [D4CoreCut.orig_vidx]; right; exact ⟨rfl, ha⟩
    · rw [D4CoreCut.orig_vidx]; left; exact ⟨rfl, hbd.resolve_left ha⟩
  have he₁_core : (x.G.endpoints e₁).1 ∉ L ∧ (x.G.endpoints e₁).2 ∉ L := by
    obtain ⟨eu, _, heu⟩ := Finset.card_eq_one_iff_existsUnique.mp (x.spec.subdiv_one_lookup_edge v₀ hv_sub)
    have heb_u : e_b = eu := heu e_b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_b_cross⟩)
    rcases he₁_inc with h1 | h2
    · refine ⟨h1.symm ▸ hv₀_not_L, fun hL => ?_⟩
      have h1u : e₁ = eu := heu e₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨h1, hL⟩⟩)
      exact he₁_ne (h1u.trans heb_u.symm)
    · refine ⟨fun hL => ?_, h2.symm ▸ hv₀_not_L⟩
      have h1u : e₁ = eu := heu e₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨h2, hL⟩⟩)
      exact he₁_ne (h1u.trans heb_u.symm)
  let e_core : Fin t.H₀.nE := D4CoreCut.idx (D4CoreCut.coreEdges x.G L) e₁
    (List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true he₁_core⟩)
  have he_core_mem : e_core ∈ t.H₀.ports (t.host j) := by
    dsimp only [BipartiteMultigraph.ports]
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange _, decide_eq_true ?_⟩
    have inj : Function.Injective (D4CoreCut.origV x.G L) :=
      ((List.nodup_finRange _).filter _).injective_get
    change (D4CoreCut.coreGraph x.G L |>.endpoints e_core).1 = t.host j ∨
      (D4CoreCut.coreGraph x.G L |>.endpoints e_core).2 = t.host j
    rcases he₁_inc with h1 | h2
    · left; apply inj
      simp only [D4CoreCut.coreGraph, D4CoreCut.orig_vidx]
      change (x.G.endpoints (D4CoreCut.origE x.G L e_core)).1 = v₀
      rw [show D4CoreCut.origE x.G L e_core = e₁ from D4CoreCut.get_idx ..]
      exact h1
    · right; apply inj
      simp only [D4CoreCut.coreGraph, D4CoreCut.orig_vidx]
      change (x.G.endpoints (D4CoreCut.origE x.G L e_core)).2 = v₀
      rw [show D4CoreCut.origE x.G L e_core = e₁ from D4CoreCut.get_idx ..]
      exact h2
  exact List.length_pos_of_mem he_core_mem

private theorem cut_incl_inj {C c : ℕ} (x : Input C c) (w : Fin (D4CoreCut.coreVerts x.G x.spec.lookupVerts).length) :
    Function.Injective ((rootCut x).incl w) := by
  let L := x.spec.lookupVerts
  intro i j hij
  have eq' := congrArg (x.G.ports (D4CoreCut.origV x.G L w)).get hij
  have hpi : ∀ k : Fin ((rootCut x).H₀.deg w),
      (x.G.ports (D4CoreCut.origV x.G L w)).get ((rootCut x).incl w k) =
        D4CoreCut.origE x.G L (((rootCut x).H₀.ports w).get k) := fun k => by
    dsimp only [D4CoreCut.Cut.incl, D4CoreCut.Cut.H₀, rootCut, D4CoreCut.cutCore, D4CoreCut.portIncl, L]
    exact List.getElem_idxOf _
  rw [hpi i, hpi j] at eq'
  have h1 : ((rootCut x).H₀.ports w).get i = ((rootCut x).H₀.ports w).get j :=
    ((List.nodup_finRange _).filter _).injective_get eq'
  exact ((List.nodup_finRange _).filter _).injective_get h1

private theorem cut_incl_mem_iff {C c : ℕ} (x : Input C c)
    (w : Fin (D4CoreCut.coreVerts x.G x.spec.lookupVerts).length)
    (r : Fin (x.G.deg (D4CoreCut.origV x.G x.spec.lookupVerts w))) :
    let L := x.spec.lookupVerts
    let t := rootCut x
    ((x.G.ports (D4CoreCut.origV x.G L w)).get r ∉ t.boundary) ↔ ∃ j : Fin (t.H₀.deg w), t.incl w j = r := by
  intro L t
  let v₀ := D4CoreCut.origV x.G L w
  let e := (x.G.ports v₀).get r
  have hv₀ : v₀ ∉ L := of_decide_eq_true (List.mem_filter.mp ((D4CoreCut.coreVerts x.G L).get_mem w)).2
  have he_inc : (x.G.endpoints e).1 = v₀ ∨ (x.G.endpoints e).2 = v₀ :=
    D4CoreCut.port_inc x.G v₀ r
  constructor
  · intro hnot
    have he_core : (x.G.endpoints e).1 ∉ L ∧ (x.G.endpoints e).2 ∉ L := by
      have hnb : ¬ ((x.G.endpoints e).1 ∈ L ∨ (x.G.endpoints e).2 ∈ L) := by
        intro hor
        exact hnot (List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true hor⟩)
      exact not_or.mp hnb
    let ec : Fin (D4CoreCut.coreGraph x.G L).nE := D4CoreCut.idx (D4CoreCut.coreEdges x.G L) e
      (List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true he_core⟩)
    have hec_mem : ec ∈ (D4CoreCut.coreGraph x.G L).ports w := by
      simp only [BipartiteMultigraph.ports, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq]
      have inj : Function.Injective (D4CoreCut.origV x.G L) :=
        ((List.nodup_finRange _).filter _).injective_get
      rcases he_inc with h1 | h2
      · left; apply inj; simp only [D4CoreCut.coreGraph, D4CoreCut.orig_vidx]
        change (x.G.endpoints (D4CoreCut.origE x.G L ec)).1 = v₀
        rw [show D4CoreCut.origE x.G L ec = e from D4CoreCut.get_idx ..]; exact h1
      · right; apply inj; simp only [D4CoreCut.coreGraph, D4CoreCut.orig_vidx]
        change (x.G.endpoints (D4CoreCut.origE x.G L ec)).2 = v₀
        rw [show D4CoreCut.origE x.G L ec = e from D4CoreCut.get_idx ..]; exact h2
    let j : Fin ((D4CoreCut.coreGraph x.G L).deg w) := D4CoreCut.idx ((D4CoreCut.coreGraph x.G L).ports w) ec hec_mem
    refine ⟨j, ?_⟩
    apply ((List.nodup_finRange _).filter _).injective_get (l := x.G.ports v₀)
    have hgi : (x.G.ports v₀).get (t.incl w j) =
        D4CoreCut.origE x.G L (((D4CoreCut.coreGraph x.G L).ports w).get j) := by
      dsimp only [t, D4CoreCut.Cut.incl, rootCut, D4CoreCut.cutCore, D4CoreCut.portIncl, L]
      exact List.getElem_idxOf _
    rw [hgi, show ((D4CoreCut.coreGraph x.G L).ports w).get j = ec from D4CoreCut.get_idx ..]
    exact D4CoreCut.get_idx ..
  · rintro ⟨j, rfl⟩ hmem
    have hec_bd : (x.G.endpoints ((x.G.ports v₀).get (t.incl w j))).1 ∈ L ∨
        (x.G.endpoints ((x.G.ports v₀).get (t.incl w j))).2 ∈ L :=
      of_decide_eq_true (List.mem_filter.mp hmem).2
    have hec_core : (x.G.ports v₀).get (t.incl w j) =
        D4CoreCut.origE x.G L (((D4CoreCut.coreGraph x.G L).ports w).get j) := by
      dsimp only [t, D4CoreCut.Cut.incl, rootCut, D4CoreCut.cutCore, D4CoreCut.portIncl, L]
      exact List.getElem_idxOf _
    rw [hec_core] at hec_bd
    have hno := D4CoreCut.internal_ok x.G L (((D4CoreCut.coreGraph x.G L).ports w).get j)
    rcases hec_bd with h1 | h2
    · exact hno.1 h1
    · exact hno.2 h2

private theorem cut_host_of_bd {C c : ℕ} (x : Input C c)
    (w : Fin (D4CoreCut.coreVerts x.G x.spec.lookupVerts).length)
    (j : Fin (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length)
    (r : Fin (x.G.deg (D4CoreCut.origV x.G x.spec.lookupVerts w)))
    (heq : (x.G.ports (D4CoreCut.origV x.G x.spec.lookupVerts w)).get r =
      D4CoreCut.origB x.G x.spec.lookupVerts j) :
    (rootCut x).host j = w := by
  let L := x.spec.lookupVerts
  let hInd := D4CoreCut.independent_of_spec x.G x.spec
  have hv₀ : D4CoreCut.origV x.G L w ∉ L :=
    of_decide_eq_true (List.mem_filter.mp ((D4CoreCut.coreVerts x.G L).get_mem w)).2
  have hinc := D4CoreCut.port_inc x.G (D4CoreCut.origV x.G L w) r
  rw [heq] at hinc
  have hbd := D4CoreCut.boundary_ok x.G L j
  change D4CoreCut.host₀ x.G L hInd j = w
  dsimp only [D4CoreCut.host₀]
  split_ifs with ha
  · rcases hinc with h1 | h2
    · exact False.elim (hv₀ (h1 ▸ ha))
    · apply ((List.nodup_finRange _).filter _).injective_get (l := D4CoreCut.coreVerts x.G L)
      change D4CoreCut.origV x.G L (D4CoreCut.vidx x.G L _ _) = D4CoreCut.origV x.G L w
      rw [D4CoreCut.orig_vidx]
      exact h2
  · rcases hinc with h1 | h2
    · apply ((List.nodup_finRange _).filter _).injective_get (l := D4CoreCut.coreVerts x.G L)
      change D4CoreCut.origV x.G L (D4CoreCut.vidx x.G L _ _) = D4CoreCut.origV x.G L w
      rw [D4CoreCut.orig_vidx]
      exact h1
    · exact False.elim (ha (hbd.resolve_right (fun h2L => hv₀ (h2 ▸ h2L))))

private theorem cut_pin_iff {C c : ℕ} (x : Input C c)
    (w : Fin (D4CoreCut.coreVerts x.G x.spec.lookupVerts).length)
    (j : Fin (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length) :
    (rootCut x).pin w = some j ↔ (rootCut x).host j = w := by
  let L := x.spec.lookupVerts
  let hInd := D4CoreCut.independent_of_spec x.G x.spec
  have hinj : Function.Injective (rootCut x).host := rootCut_host_inj x
  change D4CoreCut.pinEdge x.G L hInd w = some j ↔ D4CoreCut.host₀ x.G L hInd j = w
  unfold D4CoreCut.pinEdge
  rw [List.find?_eq_some_iff_append]
  constructor
  · rintro ⟨hpred, _⟩
    exact of_decide_eq_true (by simpa [beq_iff_eq] using hpred)
  · intro hw
    have hmem : j ∈ List.finRange (D4CoreCut.boundaryEdges x.G L).length := List.mem_finRange j
    obtain ⟨as, bs, hsplit⟩ := List.append_of_mem hmem
    refine ⟨by simpa [beq_iff_eq] using hw, as, bs, hsplit, ?_⟩
    intro a ha
    have hne : a ≠ j := by
      have hnod := List.nodup_finRange (D4CoreCut.boundaryEdges x.G L).length
      rw [hsplit] at hnod
      have hmid := List.nodup_middle.mp hnod
      intro heq
      exact (List.nodup_cons.mp hmid).1 (List.mem_append_left bs (heq ▸ ha))
    have hne_host : D4CoreCut.host₀ x.G L hInd a ≠ w := fun h => hne (hinj (h.trans hw.symm))
    simp [hne_host]

private noncomputable def rootPinPort {C c : ℕ} (x : Input C c)
    (w : Fin (D4CoreCut.coreVerts x.G x.spec.lookupVerts).length) :
    Option (Fin (x.G.deg (D4CoreCut.origV x.G x.spec.lookupVerts w))) :=
  let L := x.spec.lookupVerts
  match h : D4CoreCut.pinEdge x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec) w with
  | none => none
  | some bi =>
    let e_b := D4CoreCut.origB x.G L bi
    let he_inc : (x.G.endpoints e_b).1 = D4CoreCut.origV x.G L w ∨
        (x.G.endpoints e_b).2 = D4CoreCut.origV x.G L w := by
      have hhost := (cut_pin_iff x w bi).mp h
      change D4CoreCut.host₀ x.G L (D4CoreCut.independent_of_spec x.G x.spec) bi = w at hhost
      dsimp only [D4CoreCut.host₀] at hhost
      split_ifs at hhost with ha
      · right; rw [← hhost, D4CoreCut.orig_vidx]
      · left; rw [← hhost, D4CoreCut.orig_vidx]
    some (D4CoreCut.idx (x.G.ports (D4CoreCut.origV x.G L w)) e_b
      (List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true he_inc⟩))

private theorem rootPinPort_mem {C c : ℕ} (x : Input C c)
    (w : Fin (D4CoreCut.coreVerts x.G x.spec.lookupVerts).length)
    (r : Fin (x.G.deg (D4CoreCut.origV x.G x.spec.lookupVerts w))) :
    let L := x.spec.lookupVerts
    rootPinPort x w = some r ↔
      (x.G.ports (D4CoreCut.origV x.G L w)).get r ∈ (rootCut x).boundary := by
  intro L
  constructor
  · intro hr
    dsimp only [rootPinPort, L] at hr ⊢
    split at hr
    · cases hr
    · rename_i bi _
      injection hr with hr'
      rw [← hr']
      erw [D4CoreCut.get_idx]
      exact List.get_mem _ _
  · intro hbd
    let e := (x.G.ports (D4CoreCut.origV x.G L w)).get r
    let bi : Fin (D4CoreCut.boundaryEdges x.G L).length :=
      D4CoreCut.idx (D4CoreCut.boundaryEdges x.G L) e hbd
    have hhost : (rootCut x).host bi = w :=
      cut_host_of_bd x w bi r (D4CoreCut.get_idx (D4CoreCut.boundaryEdges x.G L) e hbd).symm
    have hpin : D4CoreCut.pinEdge x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec) w = some bi :=
      (cut_pin_iff x w bi).mpr hhost
    dsimp only [rootPinPort]
    split
    · rename_i hnone
      rw [hpin] at hnone
      cases hnone
    · rename_i bi' hsome
      have hbi : bi' = bi := Option.some.inj (hsome.symm.trans hpin)
      subst hbi
      congr 1
      apply ((List.nodup_finRange _).filter _).injective_get (l := x.G.ports (D4CoreCut.origV x.G L w))
      dsimp only [L]
      erw [D4CoreCut.get_idx]
      exact D4CoreCut.get_idx (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts) e hbd

private noncomputable def rootPins {C c : ℕ} (x : Input C c) :
    List (Fin (4 * x.m * x.k) × Fin (rootCut x).H₀.nV) :=
  let hbLen : (rootCut x).boundary.length = 4 * x.m * x.k :=
    (d4_core_cut_poly_and_spec.2 x).2.2.2.2.1
  List.ofFn (fun i : Fin (4 * x.m * x.k) => (i, (rootCut x).host (i.cast hbLen.symm)))

private theorem rootPins_get {C c : ℕ} (x : Input C c) (k : Fin (rootPins x).length) :
    have hk : k.val < 4 * x.m * x.k := by dsimp only [rootPins] at k; simpa using k.isLt
    ((rootPins x).get k).1 = ⟨k.val, hk⟩ ∧
    ((rootPins x).get k).2 = (rootCut x).host ((⟨k.val, hk⟩ : Fin (4 * x.m * x.k)).cast
      (d4_core_cut_poly_and_spec.2 x).2.2.2.2.1.symm) := by
  dsimp only [rootPins] at k ⊢
  simp [List.get_eq_getElem]

private noncomputable def rootVert {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l)
    (w : Fin (rootCut x).H₀.nV) :
    SoloVert x (rootCut x).H₀ f PktOK x.p 0 w :=
  let L := x.spec.lookupVerts
  let t := rootCut x
  let inclList := List.ofFn (fun j : Fin (t.H₀.deg w) => (t.incl w j).val)
  let portMap := (List.range (x.G.deg (t.orig w))).map (fun r => inclList.idxOf r)
  .orig (t.orig w)
    (of_decide_eq_true (List.mem_filter.mp ((D4CoreCut.coreVerts x.G L).get_mem w)).2)
    (rootPinPort x w)
    portMap
    (by simp [portMap])
    (by
      intro r hr
      have hr_not_bd : (x.G.ports (t.orig w)).get r ∉ t.boundary :=
        mt (rootPinPort_mem x w r).mpr hr
      obtain ⟨j, hj⟩ := (cut_incl_mem_iff x w r).mp hr_not_bd
      have hget : portMap.getD r.val 0 = inclList.idxOf r.val := by
        have hr_lt : r.val < portMap.length := by simp [portMap, r.isLt]
        simp only [portMap, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_lt,
          List.getElem_map, List.getElem_range, Option.getD_some]
      rw [hget]
      have hmem : r.val ∈ inclList := by
        simp only [inclList, List.mem_ofFn]
        exact ⟨j, congrArg Fin.val hj⟩
      simpa [inclList] using List.idxOf_lt_length_iff.mpr hmem)

def rootSoloNode {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    SoloNode x f PktOK :=
  let L := x.spec.lookupVerts
  let t := rootCut x
  let hSpec := d4_core_cut_poly_and_spec.2 x
  let hbLen : t.boundary.length = 4 * x.m * x.k := hSpec.2.2.2.2.1
  { d := 0
    G := t.H₀
    pCurr := x.p
    pins := rootPins x
    pins_sorted := List.pairwise_ofFn.mpr (fun _ _ h => h)
    host_inj := by
      intro k₁ k₂ hk
      rw [(rootPins_get x k₁).2, (rootPins_get x k₂).2] at hk
      have heq := rootCut_host_inj x hk
      apply Fin.ext
      simpa using congrArg Fin.val heq
    pinned_deg_pos := by
      intro k
      rw [(rootPins_get x k).2]
      exact root_cut_deg_pos x _
    pins_len_le := by
      simp only [rootPins, List.length_ofFn, pow_zero, Nat.div_one]
      omega
    verts := rootVert x f PktOK
    pin_sync := by
      intro w
      dsimp only [pinSyncProp, rootVert]
      constructor
      · intro hsome
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
        have hbd := (rootPinPort_mem x w r).mp hr
        let bi := D4CoreCut.idx (D4CoreCut.boundaryEdges x.G L) ((x.G.ports (D4CoreCut.origV x.G L w)).get r) hbd
        have hhost : t.host bi = w := cut_host_of_bd x w bi r (D4CoreCut.get_idx ..).symm
        have hbi_lt : bi.val < (rootPins x).length := by
          rw [rootPins, List.length_ofFn, ← hbLen]
          exact bi.isLt
        refine ⟨⟨bi.val, hbi_lt⟩, ?_⟩
        rw [(rootPins_get x ⟨bi.val, hbi_lt⟩).2]
        exact hhost
      · rintro ⟨k, hk⟩
        rw [(rootPins_get x k).2] at hk
        have hpin := (cut_pin_iff x w _).mpr hk
        dsimp only [rootPinPort]
        split
        · rename_i hnone
          change D4CoreCut.pinEdge x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec) w = some _ at hpin
          rw [hpin] at hnone
          cases hnone
        · rfl
    hp_ge := le_rfl
    hp_le := by simp
    edges_le := by simpa using hSpec.2.1
    verts_le := by simpa using hSpec.2.2.1
    deg_le := by simpa using hSpec.2.2.2.1 }

theorem rootSoloNode_d {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    (rootSoloNode x f PktOK).d = 0 := rfl

theorem rootSoloNode_G {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    (rootSoloNode x f PktOK).G = (rootCut x).H₀ := rfl

theorem rootSoloNode_pCurr {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    (rootSoloNode x f PktOK).pCurr = x.p := rfl

theorem rootSoloNode_pins {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    (rootSoloNode x f PktOK).pins = rootPins x := rfl

theorem rootSoloNode_verts {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    (rootSoloNode x f PktOK).verts = rootVert x f PktOK := rfl

theorem rootSoloNode_bits_eq {C c : ℕ} (x : Input C c) (f : ℤ[X]) (PktOK : PktPred f x.l) :
    (rootSoloNode x f PktOK).toWorkItem.bits =
      rootRaw (D4CoreCut.cutCoreRaw (D4Plan.input x)) x.p := by
  let L := x.spec.lookupVerts
  let t := rootCut x
  have hSpec := d4_core_cut_poly_and_spec.2 x
  have hcut : D4CoreCut.cutCoreRaw (D4Plan.input x) = t.encode x.G L := hSpec.1
  rw [hcut]
  unfold rootRaw D4CoreCut.Cut.encode
  rw [soloNode_toWorkItem_bits (rootSoloNode x f PktOK) 0 t.H₀ x.p (rootPins x) (rootVert x f PktOK)
    rfl rfl rfl HEq.rfl HEq.rfl]
  dsimp only [rootPins]
  simp only [fld_encodeList_id, ints_encodeNatListBin, unpack_encodeList_id,
    List.getD_cons_zero, List.getD_cons_succ]
  have hpins : (List.ofFn fun i : Fin (4 * x.m * x.k) => (i, t.host (i.cast hSpec.2.2.2.2.1.symm))).map
      (fun pv => encodeNatListBin [pv.1.val, pv.2.val]) =
      (List.range (List.ofFn fun i => (t.host i).val).length).map fun bi =>
        encodeNatListBin [bi, (List.ofFn fun i => (t.host i).val).getD bi 0] := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_ofFn, List.length_range]
      exact hSpec.2.2.2.2.1.symm
    · intro bi h₁ h₂
      simp only [List.length_map, List.length_ofFn] at h₁
      simp only [List.getElem_map, List.getElem_ofFn, List.getElem_range]
      have hbi : bi < t.boundary.length := hSpec.2.2.2.2.1 ▸ h₁
      rw [getD_ofFn_unit (fun i => (t.host i).val) ⟨bi, hbi⟩]
      rfl
  rw [hpins]
  congr 1; congr 2; congr 2; congr 2
  apply List.ext_getElem
  · simp
  · intro wIdx hw₁ hw₂
    simp only [List.length_ofFn] at hw₁
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    let w : Fin t.H₀.nV := ⟨wIdx, hw₁⟩
    unfold rootVert SoloVert.specBits rootVSpecAt
    have hov : (List.ofFn fun v => (t.orig v).val).getD wIdx 0 = (t.orig w).val :=
      getD_ofFn_unit _ w
    have hpi : (List.ofFn fun v => ((t.pin v).map fun i => i.val + 1).getD 0).getD wIdx 0 =
        ((t.pin w).map fun i => i.val + 1).getD 0 := getD_ofFn_unit _ w
    have hinc : ints ((List.ofFn fun v => encodeNatListBin (List.ofFn fun j => (t.incl v j).val)).getD wIdx []) =
        List.ofFn (fun j => (t.incl w j).val) := by
      have hlen : wIdx < (List.ofFn fun v : Fin t.H₀.nV =>
          encodeNatListBin (List.ofFn fun j => (t.incl v j).val)).length := by simp [hw₁]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_ofFn,
        Option.getD_some, ints_encodeNatListBin]
    rw [hov, hpi, hinc]
    dsimp only
    let incl := List.ofFn (fun j : Fin (t.H₀.deg w) => (t.incl w j).val)
    let pinId := ((t.pin w).map fun i => i.val + 1).getD 0
    have hdeg_eq : rootOrigDeg pinId incl = x.G.deg (t.orig w) := by
      unfold rootOrigDeg
      have hincl_len : incl.length = t.H₀.deg w := by simp [incl]
      rw [hincl_len]
      cases hp : t.pin w with
      | none =>
        have hpin0 : pinId = 0 := by simp [pinId, hp]
        rw [if_pos hpin0, Nat.add_zero]
        have hbij : Function.Bijective (t.incl w) := by
          refine ⟨cut_incl_inj x w, fun r => ?_⟩
          refine (cut_incl_mem_iff x w r).mp fun hbd => ?_
          have hr_some : rootPinPort x w = some r := (rootPinPort_mem x w r).mpr hbd
          have hpin_ne : t.pin w ≠ none := by
            intro hnone
            dsimp only [rootPinPort] at hr_some
            split at hr_some
            · cases hr_some
            · rename_i _ hsome
              change D4CoreCut.pinEdge x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec) w = none at hnone
              rw [hnone] at hsome; cases hsome
          exact hpin_ne hp
        exact (Fintype.card_fin _).symm.trans ((Fintype.card_of_bijective hbij).trans (Fintype.card_fin _))
      | some bi =>
        have hpin_ne : pinId ≠ 0 := by simp [pinId, hp]
        rw [if_neg hpin_ne]
        obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Fin (x.G.deg (t.orig w)), rootPinPort x w = some r₀ := by
          dsimp only [rootPinPort]
          split
          · rename_i hnone
            have hp' : D4CoreCut.pinEdge x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec) w = some bi := hp
            exact False.elim (by rw [hp'] at hnone; cases hnone)
          · exact ⟨_, rfl⟩
        have heq_sub : Finset.univ.image (t.incl w) = Finset.univ.erase r₀ := by
          ext r
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
          constructor
          · rintro ⟨j, rfl⟩
            refine ⟨fun heq => ?_, trivial⟩
            have hbd := (rootPinPort_mem x w (t.incl w j)).mp (heq ▸ hr₀)
            exact (cut_incl_mem_iff x w (t.incl w j)).mpr ⟨j, rfl⟩ hbd
          · rintro ⟨hne, -⟩
            refine (cut_incl_mem_iff x w r).mp fun hbd => ?_
            have := (rootPinPort_mem x w r).mpr hbd
            rw [hr₀] at this
            exact hne (Option.some.inj this).symm
        have hcard := congrArg Finset.card heq_sub
        rw [Finset.card_image_of_injective _ (cut_incl_inj x w),
          Finset.card_erase_of_mem (Finset.mem_univ r₀)] at hcard
        simp only [Finset.card_univ, Fintype.card_fin] at hcard
        change t.H₀.deg w = x.G.deg (t.orig w) - 1 at hcard
        have hpos : 0 < x.G.deg (t.orig w) := r₀.pos
        omega
    have hrlist : rootRList pinId incl = List.range (x.G.deg (t.orig w)) := by
      unfold rootRList
      have hlen_le : x.G.deg (t.orig w) ≤ 1 + incl.length := by
        rw [← hdeg_eq]; unfold rootOrigDeg; split_ifs <;> omega
      apply List.ext_getElem
      · simp only [List.length_take, List.length_range, List.length_cons, List.length_map]
        omega
      · intro i hi₁ hi₂
        simp only [List.getElem_take, List.getElem_range]
    have hpin_code : SoloVert.pinCode (rootPinPort x w) = rootPinPortPlus1 pinId incl := by
      unfold rootPinPortPlus1
      rw [hrlist]
      cases hp : t.pin w with
      | none =>
        have hr_none : rootPinPort x w = none := by
          dsimp only [rootPinPort]
          split
          · rfl
          · rename_i _ hsome
            have hp' : D4CoreCut.pinEdge x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec) w = none := hp
            rw [hp'] at hsome; cases hsome
        rw [hr_none]
        have hflt : (List.range (x.G.deg (t.orig w))).filter
            (fun r => !(incl.any (fun y => decide (y = r)))) = [] := by
          rw [List.filter_eq_nil_iff]
          intro r hr
          have hr_lt := List.mem_range.mp hr
          have hr_not_bd : (x.G.ports (t.orig w)).get ⟨r, hr_lt⟩ ∉ t.boundary := by
            intro hbd
            have := (rootPinPort_mem x w ⟨r, hr_lt⟩).mpr hbd
            rw [hr_none] at this; cases this
          obtain ⟨j, hj⟩ := (cut_incl_mem_iff x w ⟨r, hr_lt⟩).mp hr_not_bd
          simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq]
          push Not
          exact ⟨r, by simpa [incl] using ⟨j, congrArg Fin.val hj⟩, rfl⟩
        simp [hflt]; rfl
      | some bi =>
        obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Fin (x.G.deg (t.orig w)), rootPinPort x w = some r₀ := by
          dsimp only [rootPinPort]
          split
          · rename_i hnone
            have hp' : D4CoreCut.pinEdge x.G x.spec.lookupVerts (D4CoreCut.independent_of_spec x.G x.spec) w = some bi := hp
            exact False.elim (by rw [hp'] at hnone; cases hnone)
          · exact ⟨_, rfl⟩
        rw [hr₀]
        have hflt : (List.range (x.G.deg (t.orig w))).filter
            (fun r => !(incl.any (fun y => decide (y = r)))) = [r₀.val] := by
          have hmem : ∀ r, r ∈ (List.range (x.G.deg (t.orig w))).filter
              (fun r => !(incl.any (fun y => decide (y = r)))) ↔ r = r₀.val := by
            intro r
            simp only [List.mem_filter, List.mem_range, Bool.not_eq_true', List.any_eq_false,
              decide_eq_true_eq]
            constructor
            · rintro ⟨hr_lt, hnotin⟩
              by_contra hne
              have hnotbd : (x.G.ports (t.orig w)).get ⟨r, hr_lt⟩ ∉ t.boundary := by
                intro hbd
                have := (rootPinPort_mem x w ⟨r, hr_lt⟩).mpr hbd
                rw [hr₀] at this
                exact hne (congrArg Fin.val (Option.some.inj this).symm)
              obtain ⟨j, hj⟩ := (cut_incl_mem_iff x w ⟨r, hr_lt⟩).mp hnotbd
              exact hnotin r (by simpa [incl] using ⟨j, congrArg Fin.val hj⟩) rfl
            · rintro rfl
              refine ⟨r₀.isLt, fun y hy hyr => ?_⟩
              simp only [incl, List.mem_ofFn] at hy
              obtain ⟨j, hj⟩ := hy
              have hfin : t.incl w j = r₀ := Fin.ext (hj.trans hyr)
              have hbd := (rootPinPort_mem x w r₀).mp hr₀
              exact (cut_incl_mem_iff x w r₀).mpr ⟨j, hfin⟩ hbd
          have hnd : ((List.range (x.G.deg (t.orig w))).filter
              (fun r => !(incl.any (fun y => decide (y = r))))).Nodup :=
            List.nodup_range.filter _
          cases hres : (List.range (x.G.deg (t.orig w))).filter
              (fun r => !(incl.any (fun y => decide (y = r)))) with
          | nil =>
            have : r₀.val ∈ ([] : List ℕ) := by rw [← hres]; exact (hmem r₀.val).mpr rfl
            simp at this
          | cons a as =>
            have ha : a = r₀.val := (hmem a).mp (by rw [hres]; simp)
            subst ha
            have has : as = [] := by
              cases as with
              | nil => rfl
              | cons b bs =>
                have hb : b = r₀.val := (hmem b).mp (by rw [hres]; simp)
                rw [hres, List.nodup_cons] at hnd
                exact False.elim (hnd.1 (by simp [hb]))
            rw [has]
        simp [hflt, SoloVert.pinCode]; rfl
    rw [hrlist, hdeg_eq]
    erw [hpin_code]

theorem rootSoloNode_contract_eq {C c : ℕ} (x : Input C c) (f : ℤ[X]) (hf : f.Monic)
    (PktOK : PktPred f x.l) :
    let L := x.spec.lookupVerts
    let t := rootCut x
    let nd := rootSoloNode x f PktOK
    BTNContract x.G (fun v α => liftBase f x.l x.p (x.A v α)) =
      ∑ η : Fin (4 * x.m * x.k) → Bool,
        (∏ v : ↥L, liftBase f x.l x.p (x.A v.val fun j =>
          (List.ofFn η).getD (t.boundary.idxOf ((x.G.ports v.val).get j)) false)) *
        lift hf x.p (BTNContract nd.G (pin (nd.openTensor hf) (fun k => η (nd.pins.get k).1))) := by
  intro L t nd
  have hSpec := d4_core_cut_poly_and_spec.2 x
  have hcut := hSpec.2.2.2.2.2.2 (B f x.l x.p) (fun v α => liftBase f x.l x.p (x.A v α))
  rw [hcut]
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  have hL_eq : ∀ T : Tensor t.H₀ (B f x.l x.p),
      T = pin (nd.openTensor hf) (fun k => η (nd.pins.get k).1) →
      BTNContract t.H₀ T =
        lift hf x.p (BTNContract nd.G (pin (nd.openTensor hf) (fun k => η (nd.pins.get k).1))) := by
    intro T hT
    subst hT
    change BTNContract nd.G _ = lift hf x.p (BTNContract nd.G _)
    exact (self_lift hf _).symm
  change BTNContract t.H₀ _ = _
  apply hL_eq
  funext w β
  unfold pin SoloNode.openTensor
  rw [rootSoloNode_verts]
  dsimp only [rootVert]
  unfold SoloVert.eval
  congr 1
  apply congrArg (x.A (t.orig w))
  funext r
  let e := (x.G.ports (t.orig w)).get r
  by_cases hbd : e ∈ t.boundary
  · have hr_pin : rootPinPort x w = some r := (rootPinPort_mem x w r).mpr hbd
    have hbd_cut : (x.G.ports ((D4CoreCut.cutCore x.G x.spec.lookupVerts
        (D4CoreCut.independent_of_spec x.G x.spec)).orig w)).get r ∈
        (D4CoreCut.cutCore x.G x.spec.lookupVerts
          (D4CoreCut.independent_of_spec x.G x.spec)).boundary := hbd
    rw [if_pos hbd_cut]
    erw [dif_pos hr_pin]
    let bi : Fin t.boundary.length := D4CoreCut.idx (D4CoreCut.boundaryEdges x.G L) e hbd
    have hhost : t.host bi = w := cut_host_of_bd x w bi r (D4CoreCut.get_idx ..).symm
    have hbi_lt : bi.val < nd.pins.length := by
      change bi.val < (rootPins x).length
      simp only [rootPins, List.length_ofFn, ← hSpec.2.2.2.2.1]
      exact bi.isLt
    have hex : ∃ k : Fin nd.pins.length, nd.host k = w := by
      refine ⟨⟨bi.val, hbi_lt⟩, ?_⟩
      change ((rootPins x).get ⟨bi.val, hbi_lt⟩).2 = w
      rw [(rootPins_get x ⟨bi.val, hbi_lt⟩).2]
      exact hhost
    rw [dif_pos hex]
    let k₀ := Classical.choose hex
    have hk₀ : nd.host k₀ = w := Classical.choose_spec hex
    have hget_k₀ := rootPins_get x k₀
    have hk₀_host : t.host ((⟨k₀.val, k₀.isLt.trans_eq (by simp [nd, rootSoloNode, rootPins])⟩ :
        Fin (4 * x.m * x.k)).cast hSpec.2.2.2.2.1.symm) = w := by
      rw [← hget_k₀.2]
      exact hk₀
    have hk_eq : k₀.val = bi.val := by
      have := rootCut_host_inj x (hk₀_host.trans hhost.symm)
      exact congrArg Fin.val this
    have hpin1 : (nd.pins.get k₀).1 = ⟨bi.val, hSpec.2.2.2.2.1 ▸ bi.isLt⟩ := by
      change ((rootPins x).get k₀).1 = _
      rw [hget_k₀.1]
      apply Fin.ext
      exact hk_eq
    change _ = η (nd.pins.get k₀).1
    rw [hpin1]
    have hidx : (D4CoreCut.cutCore x.G x.spec.lookupVerts
        (D4CoreCut.independent_of_spec x.G x.spec)).boundary.idxOf
        ((x.G.ports ((D4CoreCut.cutCore x.G x.spec.lookupVerts
          (D4CoreCut.independent_of_spec x.G x.spec)).orig w)).get r) = bi.val := rfl
    rw [hidx, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [bi.isLt.trans_eq hSpec.2.2.2.2.1]),
      List.getElem_ofFn, Option.getD_some]
  · have hr_not : rootPinPort x w ≠ some r := fun h => hbd ((rootPinPort_mem x w r).mp h)
    have hbd_cut : ¬ ((x.G.ports ((D4CoreCut.cutCore x.G x.spec.lookupVerts
        (D4CoreCut.independent_of_spec x.G x.spec)).orig w)).get r ∈
        (D4CoreCut.cutCore x.G x.spec.lookupVerts
          (D4CoreCut.independent_of_spec x.G x.spec)).boundary) := hbd
    rw [if_neg hbd_cut]
    erw [dif_neg hr_not]
    have nodup_idxOf : ∀ {α : Type} [DecidableEq α] {xs : List α}
        (hnd : xs.Nodup) (i : ℕ) (hi : i < xs.length), xs.idxOf (xs[i]'hi) = i := by
      intro α _ xs hnd i hi
      have hi' : xs.idxOf (xs[i]'hi) < xs.length := List.idxOf_lt_length_iff.mpr (List.getElem_mem hi)
      have hget : xs.get ⟨xs.idxOf (xs[i]'hi), hi'⟩ = xs.get ⟨i, hi⟩ := by
        simp only [List.get_eq_getElem]
        exact List.getElem_idxOf hi'
      exact congrArg Fin.val (hnd.injective_get hget)
    obtain ⟨j, hj⟩ := (cut_incl_mem_iff x w r).mp hbd
    have hportMap : ((List.range (x.G.deg (t.orig w))).map
        (fun r' => (List.ofFn (fun j : Fin (t.H₀.deg w) => (t.incl w j).val)).idxOf r')).getD r.val 0 = j.val := by
      have hr_len : r.val < ((List.range (x.G.deg (t.orig w))).map
          (fun r' => (List.ofFn (fun j : Fin (t.H₀.deg w) => (t.incl w j).val)).idxOf r')).length := by
        simp only [List.length_map, List.length_range]; exact r.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_len, List.getElem_map,
        List.getElem_range, Option.getD_some]
      have hinj_val : Function.Injective (fun j : Fin (t.H₀.deg w) => (t.incl w j).val) :=
        fun a b h => cut_incl_inj x w (Fin.ext h)
      have hj_lt : j.val < (List.ofFn (fun j : Fin (t.H₀.deg w) => (t.incl w j).val)).length := by
        simp only [List.length_ofFn]; exact j.isLt
      have hget_j : (List.ofFn (fun j : Fin (t.H₀.deg w) => (t.incl w j).val))[j.val]'hj_lt = r.val := by
        simp only [List.getElem_ofFn]; exact congrArg Fin.val hj
      rw [← hget_j]
      exact nodup_idxOf (List.nodup_ofFn.mpr hinj_val) j.val hj_lt
    have he_core : ((t.H₀.ports w).map Fin.val).idxOf ((D4CoreCut.coreEdges x.G L).idxOf e) = j.val := by
      have he_eq : e = D4CoreCut.origE x.G L ((t.H₀.ports w).get j) := by
        dsimp only [e]
        rw [← hj]
        dsimp only [t, rootCut, D4CoreCut.cutCore, D4CoreCut.portIncl, L]
        exact List.getElem_idxOf _
      have hid : (D4CoreCut.coreEdges x.G L).idxOf e = ((t.H₀.ports w).get j).val := by
        rw [he_eq]
        exact nodup_idxOf ((List.nodup_finRange _).filter _) ((t.H₀.ports w).get j).val ((t.H₀.ports w).get j).isLt
      rw [hid]
      have hnd_p : ((t.H₀.ports w).map Fin.val).Nodup :=
        ((List.nodup_finRange _).filter _).map Fin.val_injective
      have hj_lt : j.val < ((t.H₀.ports w).map Fin.val).length := by
        simp only [List.length_map]; exact j.isLt
      have hget_p : ((t.H₀.ports w).map Fin.val)[j.val]'hj_lt = ((t.H₀.ports w).get j).val := by
        simp only [List.getElem_map]
        rfl
      rw [← hget_p]
      exact nodup_idxOf hnd_p j.val hj_lt
    erw [he_core]
    have hβ : (List.ofFn β).getD j.val false = β j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact j.isLt),
        List.getElem_ofFn, Option.getD_some]
    erw [hβ]
    congr 1
    exact Fin.ext hportMap.symm

end

end RootNode

end DetDLP.D4SoloRoot


