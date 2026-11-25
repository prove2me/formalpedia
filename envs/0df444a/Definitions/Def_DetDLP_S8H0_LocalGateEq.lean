-- Prove2me | Definitions.Def_DetDLP_S8H0_LocalGateEq
-- name    : DetDLP_S8H0_LocalGateEq
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:39:31.580715+00:00
-- url     : https://prove2.me/theorems/c06b2b49-c9d3-466f-b42f-a12878347683
-- title:
--   Leaf and join local-check identities including M5 register reorder
-- statement:
--   Establishes join_left, join_right, mapped_local, leaf gate agreements, and exact equivalence between the register-backed M5 multiplier test and evalNat composed with CoreCheck.reorder.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8H0_GateAgree
set_option autoImplicit false
namespace DetDLP.S8H0.LocalGateEq
open GateAgree
private theorem split_range (m n : ℕ) : List.finRange (m+n) =
    (List.finRange m).map (Fin.castAdd n) ++ (List.finRange n).map (Fin.natAdd m) := by
  simp only [← List.ofFn_id, List.map_ofFn]; exact List.ofFn_add
private theorem disj {m n : ℕ} (i : Fin m) (j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h; have H := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at H; omega
private theorem rank {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List α) (i : α) : (l.map f).idxOf (f i) = l.idxOf i := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : x = i <;> simp_all [hf.eq_iff, eq_comm]
section Join
variable (A C : w3_FactorLayout) (s : w3_factorTest A) (t : w3_factorTest C)
private theorem left_edges (g : Fin A.ng) : gateEdges (S8J.join A C) (Fin.castAdd C.ng g) =
    (gateEdges A g).map (Fin.castAdd C.ne) := by
  simp only [gateEdges,S8J.join]
  rw [split_range,List.filter_append,List.filter_map,List.filter_map]
  simp [Function.comp_def,S8J.splitMap]; exact fun _ => (disj _ _).symm
private theorem right_edges (g : Fin C.ng) : gateEdges (S8J.join A C) (Fin.natAdd A.ng g) =
    (gateEdges C g).map (Fin.natAdd A.ne) := by
  simp only [gateEdges,S8J.join]
  rw [split_range,List.filter_append,List.filter_map,List.filter_map]
  simp [Function.comp_def,S8J.splitMap, disj]
theorem join_left (g : Fin A.ng) (bits : List Bool) :
    localCheck (S8J.join A C) (S8J.joinTest s t) (Fin.castAdd C.ng g) bits = localCheck A s g bits := by
  simp only [localCheck,S8J.joinTest,Fin.addCases_left,left_edges]
  congr 1; funext e; exact congrArg (fun i => bits.getD i false) (rank _ (fun _ _ h => Fin.castAdd_inj.mp h) _ _)
theorem join_right (g : Fin C.ng) (bits : List Bool) :
    localCheck (S8J.join A C) (S8J.joinTest s t) (Fin.natAdd A.ng g) bits = localCheck C t g bits := by
  simp only [localCheck,S8J.joinTest,Fin.addCases_right,right_edges]
  congr 1; funext e; exact congrArg (fun i => bits.getD i false) (rank _ (fun _ _ h => (Fin.natAdd_inj _).mp h) _ _)
end Join
variable {S : RegisterMap.Shape}
theorem mapped_local (A : w3_FactorLayout) (t : w3_factorTest A) (r : Fin A.nb → NamedBlocks.Ref S)
    (g : Fin A.ng) (bits : List Bool) : let B := (NamedBlocks.mapped A t r).core
    localCheck B.A B.t g bits = t g fun e => (r (A.bit e.val)).read (bits.getD ((gateEdges A g).idxOf e.val) false) := rfl
theorem anchors_local (k : ℕ) (g : Fin k) (bits : List Bool) :
    localCheck (AnchoredLayout.anchors k) (fun _ _ => true) g bits = true := rfl
theorem zeroLast_local (n : ℕ) (g : Fin 1) (bits : List Bool) : let B := (PointGraph.zeroLast n).core
    localCheck B.A B.t g bits = !(bits.getD 0 false) := by
  fin_cases g; rfl


private theorem row_rank {n m : ℕ} (g : Fin n) (j : Fin m) :
    ((List.finRange (n*m)).filter (fun e => decide (e.divNat = g))).idxOf (finProdFinEquiv (g,j)) = j.val := by
  let f := fun i : Fin m => finProdFinEquiv (g,i)
  have h : StrictMono f := by intro a b hab; change a.val + m*g.val < b.val + m*g.val; omega
  have H : (List.finRange (n*m)).filter (fun e => decide (e.divNat = g)) = (List.finRange m).map f := by
    apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) ((List.pairwise_lt_finRange _).filter _) ((List.pairwise_lt_finRange _).map f (fun _ _ hab => h hab))
    intro x; obtain ⟨⟨u,v⟩,rfl⟩ := finProdFinEquiv.surjective x
    have hu : (finProdFinEquiv (u,v)).divNat = u := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (u,v))
    simp [hu,f,eq_comm]
  rw [H]; exact (rank f h.injective _ j).trans (List.idxOf_finRange _)

theorem rows_local {n m : ℕ} (r : Fin n → Fin m → NamedBlocks.Ref S)
    (test : Fin n → (Fin m → Bool) → Bool) (g : Fin n) (bits : List Bool) : let B := (NamedBlocks.rows n m r test).core
    localCheck B.A B.t g bits = test g fun j => (r g j).read (bits.getD j false) := by
  dsimp [NamedBlocks.rows,NamedBlocks.mapped,localCheck,gateEdges]; simp [row_rank]

theorem eqs_local {n : ℕ} (l r : Fin n → NamedBlocks.Ref S) (g : Fin n) (bits : List Bool) :
    let B := (NamedBlocks.eqs n l r).core
    localCheck B.A B.t g bits = decide ((l g).read (bits.getD 0 false) = (r g).read (bits.getD 1 false)) := by
  dsimp only [NamedBlocks.eqs]; rw [rows_local]; rfl

open S8C.AddLayout in
theorem add_local {n : ℕ} (cin : Bool) (a b z c : Fin n → NamedBlocks.Ref S) (g : Fin n) (bits : List Bool) :
    let B := (NamedBlocks.add cin a b z c).core
    localCheck B.A B.t g bits = CoreCheck.column n g ((a g).read (bits.getD 0 false))
      ((b g).read (bits.getD 1 false)) ((z g).read (bits.getD 2 false))
      (if g.val = 0 then cin else (c (prev g)).read (bits.getD 4 false)) ((c g).read (bits.getD 3 false)) := by
  have hr (j : Fin 5) : (gateEdges (layout n) g).idxOf (pos g j) = j.val := by
    have H : pos g j = finProdFinEquiv (g,j) := Fin.ext (Nat.add_comm _ _)
    rw [H]; exact row_rank g j
  have hb (j : Fin 5) : (layout n).bit (pos g j) = if h : j.val < 4 then reg g ⟨j.val,h⟩ else reg (prev g) 3 := by
    have hc : col (pos g j) = g := by apply Fin.ext; change (5*g.val+j.val)/5 = g.val; omega
    simp only [layout,bit,hc]; simp only [pos,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt j.isLt]
  dsimp only [NamedBlocks.add]; erw [mapped_local]; simp only [test,hb]
  simp [NamedBlocks.colRef,reg,CoreCheck.column,or_iff_not_imp_left,Nat.mul_add_div (by decide : 4 > 0)]
  erw [hr 0, hr 1, hr 2, hr 3, hr 4]; rfl

def halves (G : w4_M5Network.WireGraph) (g : Fin G.nV) :=
  ((List.finRange G.nE).filter (fun i => decide ((G.endpoints i).1 = g))).map G.leftHalf ++
  ((List.finRange G.nE).filter (fun i => decide ((G.endpoints i).2 = g))).map G.rightHalf

theorem mapped_mul_local {d : ℕ} (hd : 1 ≤ d) (w : Fin (w3_fpMulLayout d hd).nb → NamedBlocks.Ref S)
    (g : Fin (w3_fpMulLayout d hd).ng) (bits : List Bool) : let B := (NamedBlocks.mapped _ (w3_fpMulTests d hd) w).core
    let G := w3_forgetSides (w4_M5GraphBounds.graph d hd)
    localCheck B.A B.t g bits = S8J.HashGatePoly.mulLayoutCheck d g (List.ofFn fun j =>
      let e := (w3_m5LocalInc G g j).val; (w ((w3_fpMulLayout d hd).bit e)).read (bits.getD ((halves G g).idxOf e) false)) := by
  dsimp only; rw [mapped_local, ← PortEval.mul_eq]
  have h := mul_gateEdges (w3_forgetSides (w4_M5GraphBounds.graph d hd)) g
  change gateEdges (w3_fpMulLayout d hd) g = _ at h; rw [h]; rfl

open w4_M5GateOps w4_M5GraphBounds w4_M5EdgeNat w4_M5Network in
theorem reorder_eq (q : Pad) (hd : 1 ≤ q.length) (g : Fin (graph q.length hd).nV) (bits : List Bool) :
    let G := w3_forgetSides (graph q.length hd)
    CoreCheck.reorder q g bits = List.ofFn fun j => bits.getD ((halves G g).idxOf (w3_m5LocalInc G g j).val) false := by
  let D := graph q.length hd; let G := w3_forgetSides D
  change Fin G.nV at g
  have hs (e : Fin G.nE) : srcNat q.length e = (G.endpoints e).1.val := congrArg Prod.fst (endpointsNat_eq hd e)
  have ht (e : Fin G.nE) : dstNat q.length e = (G.endpoints e).2.val := congrArg Prod.snd (endpointsNat_eq hd e)
  have hp : portList q g = (G.ports g).map Fin.val := by
    unfold portList cap; erw [min_eq_left (show D.nE ≤ _ from (graph_edge_bound hd).le)]
    exact w4_M5PortEval.portsNat_eq D g _ _ hs ht
  let L := (List.finRange G.nE).filter fun i => decide ((G.endpoints i).1 = g)
  let R := (List.finRange G.nE).filter fun i => decide ((G.endpoints i).2 = g)
  have hl : (portList q g).filter (fun i => decide (srcNat q.length i = g)) = L.map Fin.val := by
    rw [hp,List.filter_map]; congr 1; unfold WireGraph.ports L; rw [List.filter_filter]; apply List.filter_congr
    intro e _; simp [hs,Fin.val_inj]; exact Or.inl
  have hr : (portList q g).filter (fun i => decide (srcNat q.length i ≠ g)) = R.map Fin.val := by
    rw [hp,List.filter_map]; congr 1; unfold WireGraph.ports R; rw [List.filter_filter]; apply List.filter_congr
    intro e _; by_cases h : (G.endpoints e).1 = g
    · have h' : (G.endpoints e).2 ≠ g := fun hh => G.loopless e (h.trans hh.symm)
      simp [hs,h,h']
    · simp [hs,Fin.val_inj,h]
  have HH : halves G g = (L++R).map (G.incidentHalf g) := by
    change L.map G.leftHalf ++ R.map G.rightHalf = _; rw [List.map_append]; apply congrArg₂ List.append
    · apply List.map_congr_left; intro e he; have h : (G.endpoints e).1 = g := by simpa [L] using he
      exact (if_pos h).symm
    · apply List.map_congr_left; intro e he; have h : (G.endpoints e).2 = g := by simpa [R] using he
      exact (if_neg (fun hh => G.loopless e (hh.trans h.symm))).symm
  change CoreCheck.reorder q g.val bits = List.ofFn fun j => bits.getD ((halves G g).idxOf (w3_m5LocalInc G g j).val) false
  simp only [CoreCheck.reorder,hl,hr,←List.map_append]; rw [hp,List.map_map]
  change _ = List.ofFn ((fun e => bits.getD ((halves G g).idxOf (G.incidentHalf g e)) false) ∘ (G.ports g).get)
  rw [←List.map_ofFn,List.ofFn_get,HH]; apply List.map_congr_left; intro e _
  simp only [Function.comp_apply,rank _ Fin.val_injective,rank _ (G.incidentHalf_injective g)]

open w4_M5GateOps in
theorem mul_register_local (q : Pad) (hd : 1 ≤ q.length) (w : Fin (w3_fpMulLayout q.length hd).nb → RegisterMap.Addr S)
    (g : Fin (w3_fpMulLayout q.length hd).ng) (bits : List Bool) :
    let B := (NamedBlocks.mapped _ (w3_fpMulTests q.length hd) (fun i => .reg (w i))).core
    localCheck B.A B.t g bits = w4_M5Dispatch.evalNat q g (CoreCheck.reorder q g bits) := by
  dsimp only; rw [mapped_mul_local, reorder_eq q hd g bits]; unfold S8J.HashGatePoly.mulLayoutCheck
  have h := List.eq_replicate_of_mem (l := q) (a := ()) (fun _ _ => rfl); rw [←h]; rfl

end DetDLP.S8H0.LocalGateEq


