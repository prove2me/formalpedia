-- Prove2me | Definitions.Def_DetDLP_D4SoloTree
-- name    : DetDLP_D4SoloTree
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T22:20:03.997992+00:00
-- url     : https://prove2.me/theorems/fd0a3929-68b4-47f8-a6f0-27c3ded80c20
-- title:
--   Unrolled Solo Tree Equivalence and Weight Product Identities
-- statement:
--   Establishes residue-word conversions, defines soloStepFn matching D4RankWalker step recursion, defines ActiveNodeCert and recursive SoloUnroll trees, and builds the unrolled node tree matching the rank walker.
-- source:
--   prove2me_m14_solo/Definitions/Def_DetDLP_D4SoloTree.lean

import Definitions.Def_DetDLP_D4SoloStepEq
import Theorems.Thm_DetDLP_f9a2_b_mul_poly
import Theorems.Thm_DetDLP_d4_raw_weight_cleared_identity
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_adaptive_padded_rank_sum
import Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DetDLP.D4SoloTree

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4GuardTree.Expansion DetDLP.D4SoloRaw DetDLP.D4SoloNode
open DetDLP.D4SoloRoot DetDLP.D4SoloStep DetDLP.D4SoloStepEq
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section

section WalkerAlgebra

private theorem readCoeff {R : Type*} [CommRing R] {g : R[X]} (hg : g.Monic)
    {n : ℕ} (hn : Nontrivial R → g.natDegree = n) (b : Fin n → R) (i : Fin n) :
    (AdjoinRoot.modByMonicHom hg (AdjoinRoot.mk _ (∑ j : Fin n, monomial j.val (b j)))).coeff i = b i := by
  nontriviality R
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hg).mpr]
  · simp only [finsetSum_coeff, coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [degree_eq_natDegree hg.ne_zero, hn inferInstance]
    simp_rw [← C_mul_X_pow_eq_monomial]
    exact degree_sum_fin_lt _

theorem pow2_replicate_eq (n k : ℕ) (hk : k ≤ n) :
    pow2 (List.replicate n true) k = 2 ^ k := by
  unfold pow2
  have htake : ((List.replicate n true).take k).map (fun _ => false) = List.replicate k false := by
    apply List.ext_getElem <;> simp [min_eq_left hk]
  rw [htake, ← countWord_two_pow k, num_countWord]

theorem residue_eq_flatten_word (f : ℤ[X]) (l q : ℕ) (hf : f.Monic) (z : B f l q) :
    residue f l q hf z = encodeNatListBin (F9A2.flatten (word f l q hf z)) := by
  unfold residue F9A2.flatten
  congr 1
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext r
  apply congrArg List.ofFn
  funext i
  have hfin : (⟨r.val * f.natDegree + i.val,
      by nlinarith [Nat.mul_le_mul_right f.natDegree r.isLt, i.isLt]⟩ : Fin (l * f.natDegree)) =
      finProdFinEquiv (r, i) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [hfin, finProdFinEquiv.symm_apply_apply]

theorem red_repr_eq_lift {f : ℤ[X]} {l p : ℕ} (hf : f.Monic) (q : ℕ) (z : B f l p) :
    red f l q (D4GuardTree.repr hf z) = lift hf q z := by
  unfold red D4GuardTree.repr lift
  simp only [← C_mul_X_pow_eq_monomial, map_sum, map_mul, map_pow, map_natCast,
    AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.map_root, AdjoinRoot.map_of]

theorem oneWord_eq_residue_one (S m p guard l : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (hl : 0 < l) (hdeg : 0 < f.natDegree) (hq : 0 < guard + p) :
    oneWord (contextV2 S m p guard l (polynomialBits f)) =
      residue f l (guard + p) hf (1 : B f l (guard + p)) := by
  unfold oneWord contextV2 residue
  simp only [fld_pack, List.getD_cons_succ, List.getD_cons_zero, List.length_replicate,
    polynomialBits, List.length_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.length_map, List.length_range] at hk₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    let kFin : Fin (l * f.natDegree) := ⟨k, by simpa using hk₁⟩
    let ji := finProdFinEquiv.symm kFin
    have hk_eq : finProdFinEquiv ji = kFin := finProdFinEquiv.apply_symm_apply _
    have hk_val : ji.2.val + f.natDegree * ji.1.val = k := congrArg Fin.val hk_eq
    have h1_eq : (1 : B f l (guard + p)) =
        AdjoinRoot.mk _ (∑ j : Fin l, monomial j.val (AdjoinRoot.mk _
          (∑ i : Fin f.natDegree, monomial i.val (if j.val = 0 ∧ i.val = 0 then (1 : ZMod (2 ^ (guard + p))) else 0)))) := by
      let j0 : Fin l := ⟨0, hl⟩
      let i0 : Fin f.natDegree := ⟨0, hdeg⟩
      rw [Finset.sum_eq_single j0]
      · simp only [j0, true_and, monomial_zero_left]
        rw [Finset.sum_eq_single i0]
        · simp [i0]
        · intro i _ hne; have : i.val ≠ 0 := fun h => hne (Fin.ext h); simp [this]
        · intro hm; exact False.elim (hm (Finset.mem_univ i0))
      · intro j _ hne; have : j.val ≠ 0 := fun h => hne (Fin.ext h); simp [this]
      · intro hm; exact False.elim (hm (Finset.mem_univ j0))
    change (if k = 0 then 1 else 0) = word f l (guard + p) hf 1 ji.1 ji.2
    rw [h1_eq]
    unfold word
    rw [readCoeff (monic_X_pow l) (fun _ => natDegree_X_pow l),
        readCoeff (hf.map _) (fun _ => hf.natDegree_map _)]
    by_cases hk0 : k = 0
    · have hsum0 : ji.2.val + f.natDegree * ji.1.val = 0 := hk_val.trans hk0
      have hj0 : ji.1.val = 0 := by
        by_contra hj
        have hge : f.natDegree ≤ f.natDegree * ji.1.val :=
          Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj)
        linarith
      have hi0 : ji.2.val = 0 := (Nat.add_eq_zero_iff.mp hsum0).1
      have hlt2 : 1 < 2 ^ (guard + p) := Nat.one_lt_pow hq.ne' (by decide)
      simp [hk0, hj0, hi0, @ZMod.val_one (2 ^ (guard + p)) ⟨hlt2⟩]
    · have hnot : ¬(ji.1.val = 0 ∧ ji.2.val = 0) := by
        rintro ⟨hj0, hi0⟩
        apply hk0
        rw [hj0, hi0] at hk_val
        omega
      simp [hk0, hnot]

theorem productV2_eq_residue_mul (S m p guard l : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (hRing : RingOK f) (hl : 0 < l) (hq : 0 < guard + p)
    (acc ans : Wd) (aVal bVal : B f l (guard + p))
    (hacc : acc = residue f l (guard + p) hf aVal)
    (hans : fld ans 1 = residue f l (guard + p) hf bVal) :
    productV2 (contextV2 S m p guard l (polynomialBits f)) acc ans =
      residue f l (guard + p) hf (aVal * bVal) := by
  let qPrec := guard + p
  let ctx := contextV2 S m p guard l (polynomialBits f)
  have hdeg : 0 < f.natDegree := hRing.1
  have hlt2 : 1 < 2 ^ qPrec := Nat.one_lt_pow hq.ne' (by decide)
  unfold productV2
  change F9A2.bMulRaw (pack [(pow2 (fld ctx 2) (fld ctx 2).length).bits, fld ctx 3,
    (fld ctx 4).map (fun _ => true),
    encodeNatListBin ((fld ctx 4).map fun b => if b then 1 else 0), acc, fld ans 1]) = _
  have hq_fld : fld ctx 2 = List.replicate qPrec true := by
    simp [ctx, contextV2, fld_pack, qPrec]
  have hl_fld : fld ctx 3 = List.replicate l true := by
    simp [ctx, contextV2, fld_pack]
  have hf_fld : fld ctx 4 = polynomialBits f := by
    simp [ctx, contextV2, fld_pack]
  rw [hq_fld, hl_fld, hf_fld]
  simp only [List.length_replicate, pow2_replicate_eq qPrec qPrec le_rfl]
  have hf_rep : (polynomialBits f).map (fun _ => true) = List.replicate f.natDegree true := by
    apply List.ext_getElem <;> simp [polynomialBits]
  have hf_coeffs : (polynomialBits f).map (fun b => if b then 1 else 0) =
      List.ofFn (fun i : Fin f.natDegree => ((f.coeff i.val : ZMod (2 ^ qPrec)).val)) := by
    apply List.ext_getElem
    · simp [polynomialBits]
    · intro i hi₁ hi₂
      simp only [List.length_map, polynomialBits, List.length_ofFn] at hi₁
      simp only [List.getElem_map, polynomialBits, List.getElem_ofFn]
      rcases hRing.2.2 i hi₁ with hc0 | hc1
      · simp [hc0]
      · simp [hc1, @ZMod.val_one (2 ^ qPrec) ⟨hlt2⟩]
  rw [hf_rep, hf_coeffs, hacc, hans, residue_eq_flatten_word f l qPrec hf aVal,
      residue_eq_flatten_word f l qPrec hf bVal, residue_eq_flatten_word f l qPrec hf (aVal * bVal)]
  exact f9a2_b_mul_poly.1 f l qPrec hf hdeg hl hq aVal bVal

theorem finishWt_eq_residue_shift (S m p guard l lossSum : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (hloss : lossSum ≤ guard) (acc : Wd) (aVal : B f l (guard + p))
    (hacc : acc = residue f l (guard + p) hf aVal) :
    finishWt (contextV2 S m p guard l (polynomialBits f)) acc lossSum =
      residue f l (guard + p) hf ((2 : B f l (guard + p)) ^ (guard - lossSum) * aVal) := by
  let qPrec := guard + p
  let k := guard - lossSum
  have hk_le : k ≤ qPrec := by omega
  let ctx := contextV2 S m p guard l (polynomialBits f)
  have hctx2 : fld ctx 2 = List.replicate qPrec true := by
    simp [ctx, contextV2, fld_pack, qPrec]
  have hctx6 : num ctx 6 = guard := by
    simp [ctx, contextV2, num, fld_pack]
  change (let q := fld ctx 2; let fac := pow2 q (num ctx 6 - lossSum); let modulus := pow2 q q.length;
    encodeNatListBin ((ints acc).map fun v => v * fac % modulus)) = _
  rw [hctx2, hctx6]
  dsimp only
  rw [List.length_replicate, pow2_replicate_eq qPrec k hk_le,
      pow2_replicate_eq qPrec qPrec le_rfl, hacc]
  unfold residue
  rw [ints_encodeNatListBin, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext idxFin
  dsimp only [Function.comp_apply]
  have ha_self : aVal = lift hf qPrec aVal := (self_lift hf aVal).symm
  have h2pow : (2 : B f l qPrec) ^ k =
      AdjoinRoot.mk _ (C (AdjoinRoot.mk _ (C ((2 ^ k : ℕ) : ZMod (2 ^ qPrec))))) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, map_pow, map_ofNat]
  have hprod : (2 : B f l qPrec) ^ k * aVal =
      AdjoinRoot.mk _ (∑ j : Fin l, monomial j.val (AdjoinRoot.mk _
        (∑ i : Fin f.natDegree, monomial i.val
          (((word f l qPrec hf aVal j i * 2 ^ k : ℕ) : ZMod (2 ^ qPrec)))))) := by
    conv_lhs => rw [ha_self, h2pow]
    unfold lift
    rw [← map_mul (AdjoinRoot.mk _), Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro j _
    rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, ← map_mul, C_mul_X_pow_eq_monomial]
    congr 1
    rw [← map_mul (AdjoinRoot.mk _), Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro i _
    rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, ← map_mul, C_mul_X_pow_eq_monomial]
    congr 1
    push_cast
    exact mul_comm _ _
  rw [hprod]
  unfold word
  rw [readCoeff (monic_X_pow l) (fun _ => natDegree_X_pow l),
      readCoeff (hf.map _) (fun _ => hf.natDegree_map _), ZMod.val_natCast]

end WalkerAlgebra

section DeterministicOracle

open Classical in
def soloCountFn (M_node : PrimitiveMachine) (o_node : Fin M_node.tapeCount)
    (ctx i : Wd) : ℕ :=
  if h0 : ∃ out0 t0 s0, RunsWithin M_node o_node (ask ctx i 0) out0 t0 s0 then
    Groundwork.PolyT.bval (Classical.choose h0)
  else 0

open Classical in
def soloBranchFn (M_node : PrimitiveMachine) (o_node : Fin M_node.tapeCount)
    (ctx i : Wd) (j : ℕ) : Wd :=
  if hd : ∃ outd td sd, RunsWithin M_node o_node (ask ctx i (j + 1)) outd td sd then
    Classical.choose hd
  else []

def soloStepFn (M_node : PrimitiveMachine) (o_node : Fin M_node.tapeCount)
    (ctx : Wd) (i : Wd) : WalkerStep :=
  ⟨soloCountFn M_node o_node ctx i, fun d => soloBranchFn M_node o_node ctx i d.val⟩

theorem soloStepFn_n_eq {M_node : PrimitiveMachine} {o_node : Fin M_node.tapeCount}
    {ctx i : Wd} {n : ℕ} {t0 s0 : ℝ}
    (hrun0 : RunsWithin M_node o_node (ask ctx i 0) (countWord n) t0 s0) :
    (soloStepFn M_node o_node ctx i).n = n := by
  classical
  have hex : ∃ out0 t0 s0, RunsWithin M_node o_node (ask ctx i 0) out0 t0 s0 := ⟨_, _, _, hrun0⟩
  unfold soloStepFn soloCountFn
  dsimp only
  rw [dif_pos hex]
  obtain ⟨t', s', h'⟩ := Classical.choose_spec hex
  rw [runsWithin_unique h' hrun0, num_countWord]

theorem soloStepFn_branch_eq {M_node : PrimitiveMachine} {o_node : Fin M_node.tapeCount}
    {ctx i ans : Wd} {n : ℕ} {_t0 _s0 td sd : ℝ}
    (_hrun0 : RunsWithin M_node o_node (ask ctx i 0) (countWord n) _t0 _s0)
    (d : Fin (soloStepFn M_node o_node ctx i).n)
    (hrund : RunsWithin M_node o_node (ask ctx i (d.val + 1)) ans td sd) :
    (soloStepFn M_node o_node ctx i).branch d = ans := by
  classical
  have hexd : ∃ outd td sd, RunsWithin M_node o_node (ask ctx i (d.val + 1)) outd td sd := ⟨_, _, _, hrund⟩
  change soloBranchFn M_node o_node ctx i d.val = ans
  unfold soloBranchFn
  rw [dif_pos hexd]
  obtain ⟨td', sd', hd'⟩ := Classical.choose_spec hexd
  exact runsWithin_unique hd' hrund

end DeterministicOracle

section UnrollCert

structure ActiveNodeCert {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ)
    (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)) where
  hd : nd.d < Nat.clog 32 (4 * x.m)
  hM : D3Stopped.threshold x.S < nd.G.nE
  hM_le : nd.G.nE ≤ x.S
  hu_pos : 1 ≤ D3Stopped.width x.S nd.d
  hu : D3Stopped.width x.S nd.d ≤ D3Stopped.shift x.S nd.d
  hu_le_M : D3Stopped.width x.S nd.d ≤ nd.G.nE
  lbl : Label (D3Stopped.shift x.S nd.d) nd.G
  s : Step lbl hu f x.l nd.pCurr
  nBranches : ℕ
  order : Fin nBranches ≃ Branch s
  hbal : D2.Balanced nd.host 1 lbl
  hsound : s.sound hf
  hinc_prec : ∀ i < D3Stopped.width x.S nd.d,
    nd.pCurr + increase nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) i ≤
      64 * nd.G.nE * tileScale (D3Stopped.shift x.S nd.d) i / D3Stopped.width x.S nd.d
  hinc_le : ∀ i,
    nd.pCurr + increase nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) i ≤
      x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d
  hmodes : ∀ t, ((s.modes t).count : ℝ) ≤ Real.exp ((K_loc : ℝ) * Real.sqrt
    ((nd.G.nE : ℝ) * (nd.pCurr + increase nd.G.nE (D3Stopped.shift x.S nd.d)
      (D3Stopped.width x.S nd.d) (AppendixD4.level t.val)) /
      tileScale (D3Stopped.shift x.S nd.d) (AppendixD4.level t.val)))
  hrun0 :
    let a := D3Stopped.shift x.S nd.d; let u := D3Stopped.width x.S nd.d
    let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
    let bnd := polyBound H_loc (D4NodeQuery.request nd.G nd.host a u nd.pCurr x.l f 0).length +
      polyBound K_loc (n + (stepInput nd.G a u nd.pCurr x.l f lbl).length) + c_loc
    RunsWithin M_node o_node (D4NodeQuery.request nd.G nd.host a u nd.pCurr x.l f 0)
      (countWord nBranches) bnd bnd
  hrun_br : ∀ j : Fin nBranches,
    let a := D3Stopped.shift x.S nd.d; let u := D3Stopped.width x.S nd.d
    let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
    let bnd := polyBound H_loc (D4NodeQuery.request nd.G nd.host a u nd.pCurr x.l f (j.val + 1)).length +
      polyBound K_loc (n + (stepInput nd.G a u nd.pCurr x.l f lbl).length) + c_loc
    RunsWithin M_node o_node (D4NodeQuery.request nd.G nd.host a u nd.pCurr x.l f (j.val + 1))
      (s.bits hf (order j)) bnd bnd
  hpkt_eval : ∀ t k' β g r α,
    let c := s.child t k' β g
    let n := nd.G.nE + nd.pCurr + f.natDegree + x.l + 2
    RunsWithin E_pkt o_pkt (Encoding.encodeList id [c.descriptor r, List.ofFn α])
      (residue f x.l _ hf (c.entry r α))
      (Real.exp ((K_loc : ℝ) * (2 ^ D3Stopped.shift x.S nd.d : ℕ) * Real.log n))
      (polyBound K_loc n)
  hdeg_f : f.natDegree = 4 * D3Stopped.level x.S

def ActiveNodeCert.childNode {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd)
    (ν : Branch cert.s) (g : Fin 64) :
    SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf) :=
  childSoloNode x hf E_pkt o_pkt K_loc nd cert.s rfl cert.hbal cert.hM_le cert.hinc_le
    cert.hpkt_eval cert.hdeg_f cert.hu_pos cert.hu_le_M ν g

def SoloUnroll {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ) :
    ℕ → SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf) → Type
  | 0, nd => PLift (Nat.clog 32 (4 * x.m) ≤ nd.d ∨ nd.G.nE ≤ D3Stopped.threshold x.S)
  | k + 1, nd =>
    PSum (PLift (Nat.clog 32 (4 * x.m) ≤ nd.d ∨ nd.G.nE ≤ D3Stopped.threshold x.S))
      (Σ cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd,
        (ν : Branch cert.s) → (g : Fin 64) →
          SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc k (cert.childNode ν g))

def mkActiveNodeCert {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic) (hRing : RingOK f)
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ)
    (hLocal : ∀ (G : Graph) (a u p l b τ : ℕ) (host : Fin b → Fin G.nV) (f' : ℤ[X]) (hf' : f'.Monic),
      1 ≤ u → (hu : u ≤ a) → u ≤ G.nE → 1 ≤ l → 1 ≤ p → RingOK f' → points G.nE a ≤ 2 ^ f'.natDegree →
      2 ^ a * 64 ^ (2 * a) ≤ G.nE → (a + 2) * 64 ^ (4 * a) * max 1 G.maxDeg ≤ G.nE → 1 ≤ τ →
      (∀ z, (Finset.univ.filter fun y => host z = host y).card ≤ τ) →
      ∃ (lbl : Label a G) (s : Step lbl hu f' l p) (order : Fin (Fintype.card (Branch s)) ≃ Branch s),
        let n := G.nE + p + f'.natDegree + l + 2
        let bound (j : ℕ) := polyBound H_loc (D4NodeQuery.request G host a u p l f' j).length +
          polyBound K_loc (n + (stepInput G a u p l f' lbl).length) + c_loc
        D2.Balanced host τ lbl ∧ Padded lbl ∧ s.sound hf' ∧
        (∀ t, ((s.modes t).count : ℝ) ≤ Real.exp ((K_loc : ℝ) * Real.sqrt
          ((G.nE : ℝ) * (p + increase G.nE a u (AppendixD4.level t.val)) / tileScale a (AppendixD4.level t.val)))) ∧
        RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' 0)
          (countWord (Fintype.card (Branch s))) (bound 0) (bound 0) ∧
        (∀ j, RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' (j.val + 1))
          (s.bits hf' (order j)) (bound (j.val + 1)) (bound (j.val + 1))) ∧
        ∀ t k β g r α, let z := s.child t k β g
          RunsWithin E_pkt o_pkt (Encoding.encodeList id [z.descriptor r, List.ofFn α])
            (residue f' l _ hf' (z.entry r α))
            (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (L₀_act : ℕ)
    (hact_all : ∀ (d M Δ p : ℕ),
      L₀_act ≤ D3Stopped.level x.S → D3Stopped.threshold x.S < M → M ≤ x.S / 8 ^ d →
      let a := D3Stopped.shift x.S d; let u := D3Stopped.width x.S d
      let last := if d = 0 then 0 else D3Stopped.shift x.S (d - 1)
      Δ ≤ max (C * Nat.ceil ((x.b : ℝ) ^ ((3 : ℝ) / 4))) (2 * 2 ^ last) →
      p ≤ x.p + 80 * x.S * 2 ^ last →
      1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 1 ≤ x.l ∧ points M a ≤ 2 ^ (4 * D3Stopped.level x.S) ∧
      2 ^ a * 64 ^ (2 * a) ≤ M ∧ (a + 2) * 64 ^ (4 * a) * max 1 Δ ≤ M ∧
      max Δ (2 * 2 ^ a) ≤ D3Stopped.cap x.S ∧
      (∀ i < u, p + increase M a u i ≤ 64 * M * tileScale a i / u) ∧
      ∀ i, p + increase M a u i ≤ x.p + 80 * x.S * 2 ^ a)
    (hL : L₀_act ≤ D3Stopped.level x.S)
    (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
    (hd : nd.d < Nat.clog 32 (4 * x.m))
    (hM : D3Stopped.threshold x.S < nd.G.nE) :
    ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd :=
  let hM_le : nd.G.nE ≤ x.S := nd.edges_le.trans (Nat.div_le_self _ _)
  let hpre := node_preconditions_hold x nd L₀_act (hact_all nd.d) hL hM
  let hex := hLocal nd.G (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d)
    nd.pCurr x.l nd.pins.length 1 nd.host f hf
    hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 (le_trans x.hp nd.hp_ge) hRing
    (hdeg_f.symm ▸ hpre.2.2.2.2.1) hpre.2.2.2.2.2.1 hpre.2.2.2.2.2.2.1 (by decide) nd.host_card_le_one
  let lbl := Classical.choose hex
  let h1 := Classical.choose_spec hex
  let s := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let order := Classical.choose h2
  let hspec := Classical.choose_spec h2
  ⟨hd, hM, hM_le, hpre.1, hpre.2.1, hpre.2.2.1, lbl, s, Fintype.card (Branch s), order,
    hspec.1, hspec.2.2.1, hpre.2.2.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.2.2,
    hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2.1, hspec.2.2.2.2.2.2, hdeg_f⟩

def buildSoloUnroll {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic) (hRing : RingOK f)
    (hdeg_f : f.natDegree = 4 * D3Stopped.level x.S)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ)
    (hLocal : ∀ (G : Graph) (a u p l b τ : ℕ) (host : Fin b → Fin G.nV) (f' : ℤ[X]) (hf' : f'.Monic),
      1 ≤ u → (hu : u ≤ a) → u ≤ G.nE → 1 ≤ l → 1 ≤ p → RingOK f' → points G.nE a ≤ 2 ^ f'.natDegree →
      2 ^ a * 64 ^ (2 * a) ≤ G.nE → (a + 2) * 64 ^ (4 * a) * max 1 G.maxDeg ≤ G.nE → 1 ≤ τ →
      (∀ z, (Finset.univ.filter fun y => host z = host y).card ≤ τ) →
      ∃ (lbl : Label a G) (s : Step lbl hu f' l p) (order : Fin (Fintype.card (Branch s)) ≃ Branch s),
        let n := G.nE + p + f'.natDegree + l + 2
        let bound (j : ℕ) := polyBound H_loc (D4NodeQuery.request G host a u p l f' j).length +
          polyBound K_loc (n + (stepInput G a u p l f' lbl).length) + c_loc
        D2.Balanced host τ lbl ∧ Padded lbl ∧ s.sound hf' ∧
        (∀ t, ((s.modes t).count : ℝ) ≤ Real.exp ((K_loc : ℝ) * Real.sqrt
          ((G.nE : ℝ) * (p + increase G.nE a u (AppendixD4.level t.val)) / tileScale a (AppendixD4.level t.val)))) ∧
        RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' 0)
          (countWord (Fintype.card (Branch s))) (bound 0) (bound 0) ∧
        (∀ j, RunsWithin M_node o_node (D4NodeQuery.request G host a u p l f' (j.val + 1))
          (s.bits hf' (order j)) (bound (j.val + 1)) (bound (j.val + 1))) ∧
        ∀ t k β g r α, let z := s.child t k β g
          RunsWithin E_pkt o_pkt (Encoding.encodeList id [z.descriptor r, List.ofFn α])
            (residue f' l _ hf' (z.entry r α))
            (Real.exp ((K_loc : ℝ) * (2 ^ a : ℕ) * Real.log n)) (polyBound K_loc n))
    (L₀_act : ℕ)
    (hact_all : ∀ (d M Δ p : ℕ),
      L₀_act ≤ D3Stopped.level x.S → D3Stopped.threshold x.S < M → M ≤ x.S / 8 ^ d →
      let a := D3Stopped.shift x.S d; let u := D3Stopped.width x.S d
      let last := if d = 0 then 0 else D3Stopped.shift x.S (d - 1)
      Δ ≤ max (C * Nat.ceil ((x.b : ℝ) ^ ((3 : ℝ) / 4))) (2 * 2 ^ last) →
      p ≤ x.p + 80 * x.S * 2 ^ last →
      1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 1 ≤ x.l ∧ points M a ≤ 2 ^ (4 * D3Stopped.level x.S) ∧
      2 ^ a * 64 ^ (2 * a) ≤ M ∧ (a + 2) * 64 ^ (4 * a) * max 1 Δ ≤ M ∧
      max Δ (2 * 2 ^ a) ≤ D3Stopped.cap x.S ∧
      (∀ i < u, p + increase M a u i ≤ 64 * M * tileScale a i / u) ∧
      ∀ i, p + increase M a u i ≤ x.p + 80 * x.S * 2 ^ a)
    (hL : L₀_act ≤ D3Stopped.level x.S) :
    ∀ (k : ℕ) (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)),
      nd.d + k = Nat.clog 32 (4 * x.m) →
      SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc k nd
  | 0, _, hk =>
    ⟨Or.inl (by omega)⟩
  | k + 1, nd, hk =>
    if hM : D3Stopped.threshold x.S < nd.G.nE then
      let cert := mkActiveNodeCert x hf hRing hdeg_f M_node E_pkt o_node o_pkt K_loc H_loc c_loc
        hLocal L₀_act hact_all hL nd (by omega) hM
      PSum.inr ⟨cert, fun ν g =>
        buildSoloUnroll x hf hRing hdeg_f M_node E_pkt o_node o_pkt K_loc H_loc c_loc
          hLocal L₀_act hact_all hL k (cert.childNode ν g) (by
            change (nd.d + 1) + k = Nat.clog 32 (4 * x.m)
            omega)⟩
    else
      PSum.inl ⟨Or.inr (Nat.not_lt.mp hM)⟩

def SoloUnroll.toExpansion {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    (hdeg : 0 < f.natDegree)
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (η : Fin (4 * x.m * x.k) → Bool) :
    (k : ℕ) → (nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)) →
    SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc k nd →
    Expansion x.S f hf x.l nd.d k nd.pCurr
      (BTNContract nd.G (pin (nd.openTensor hf) (fun j => η (nd.pins.get j).1)))
  | 0, nd, _ =>
    .leaf (BTNContract nd.G (pin (nd.openTensor hf) (fun j => η (nd.pins.get j).1)))
  | _ + 1, nd, PSum.inl _ =>
    .leaf (BTNContract nd.G (pin (nd.openTensor hf) (fun j => η (nd.pins.get j).1)))
  | k + 1, nd, PSum.inr ⟨cert, sub⟩ =>
    .step cert.s cert.hsound (nd.openTensor hf) (fun j => η (nd.pins.get j).1) cert.hM_le cert.hu_pos
      (fun ν g =>
        let cnd := cert.childNode ν g
        have hten : BTNContract cnd.G (pin (cnd.openTensor hf) (fun idx => η (cnd.pins.get idx).1)) =
            BTNContract (cert.s.child ν.1 ν.2.1 ν.2.2 g).graph
              ((cert.s.child ν.1 ν.2.1 ν.2.2 g).tensor (lift hf _)
                (pin (nd.openTensor hf) (fun idx => η (nd.pins.get idx).1))) := by
          have ht := childSoloNode_tensor_eq x hf hdeg E_pkt o_pkt K_loc nd cert.s rfl cert.hbal
            cert.hM_le cert.hinc_le cert.hpkt_eval cert.hdeg_f cert.hu_pos cert.hu_le_M ν g η
          exact congrArg (BTNContract (cert.s.child ν.1 ν.2.1 ν.2.2 g).graph) ht
        Eq.rec (motive := fun z _ => Expansion x.S f hf x.l (nd.d + 1) k
          (nd.pCurr + increase nd.G.nE (D3Stopped.shift x.S nd.d)
            (D3Stopped.width x.S nd.d) (AppendixD4.level ν.1.val)) z)
          (SoloUnroll.toExpansion hdeg η k cnd (sub ν g)) hten)

end UnrollCert

end

end DetDLP.D4SoloTree


