-- Prove2me | Definitions.Def_DetDLP_D4BEntryLengths
-- name    : DetDLP_D4BEntryLengths
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:33:50.630819+00:00
-- url     : https://prove2.me/theorems/7264f8ba-8db6-4671-9c3e-875994874dc3
-- title:
--   Length estimates for residual digit port queries and source replies
-- statement:
--   The residual vertex input and its returned residue word have length bounded by a single fixed polynomial of the original instance size, uniformly in the branch, vertex and digit assignment.

import Definitions.Def_DetDLP_D4BEntryFuel
set_option autoImplicit false
namespace DetDLP.D4BEntry
open Groundwork D4Plan AppendixD4 ResidualScalarOracle
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem np_mono (k : ℕ) : Monotone (np k) := fun _ _ h => Nat.mul_le_mul_left k (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) _)
theorem np_pb (k : ℕ) : PB (np k) := ⟨k,fun _ => le_rfl⟩
@[simp] theorem np_cast (k n : ℕ) : (np k n : ℝ) = polyBound k n := by simp [np,polyBound]
private theorem count_len {α : Type} (f : α → W) (xs : List α) : xs.length ≤ (Encoding.encodeList f xs).length := by induction xs <;> simp_all [Encoding.encodeList]; omega
private theorem enc_len {α : Type} (f : α → W) (xs : List α) (b : ℕ) (h : ∀ x ∈ xs,(f x).length ≤ b) : (Encoding.encodeList f xs).length ≤ (2*b+2)*xs.length+1 := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih => have hx := h x (by simp); have ht := ih (fun y hy => h y (by simp [hy])); simp [Encoding.encodeList,flen,Nat.mul_succ]; omega
private theorem cw_bound (n q : ℕ) (hn : n < 2^q) : (countWord n).length ≤ q+1 := by
  by_cases hh : n = 0
  · simp [countWord,hh]
  · simp only [countWord,if_neg hh,Nat.size_eq_bits_len]; exact (Nat.size_le.mpr hn).trans (by omega)
private theorem cw_small (n : ℕ) : (countWord n).length ≤ n+1 := cw_bound n n Nat.lt_two_pow_self

private def lbound (L q : ℕ) := 8*(L+2)+(2*(q+1)+2)*L+1
private theorem mat_len {C c : ℕ} {x : Input C c} (P : Plan x) (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)) (v : Fin (P.R u).nV) (t : Fin ((P.R u).deg v) → Bool) :
    let L := (digitDesc P u a).length; let q := P.guard+x.p
    let src := residue P.f x.l q P.hf (P.V u v t); let w := encodePortQuery (digitDesc P u a) v.val (List.ofFn t)
    w.length+src.length ≤ lbound L q := by
  intro L q src w
  have hb : (branch P u).length ≤ L := memberLen _ _ (by simp)
  have hR : ((P.R u).encode).length ≤ (branch P u).length := memberLen _ _ (by simp)
  have hV : (List.ofFn (P.R u).side).length ≤ ((P.R u).encode).length := memberLen _ _ (by simp)
  have nv : (P.R u).nV ≤ L := by simpa using (hV.trans hR).trans hb
  have hd := (infoLen P u a).2
  have hdeg : (P.R u).deg v ≤ L := by
    have hh : (P.R u).deg v ≤ (P.R u).nE := by simpa [BipartiteMultigraph.deg,BipartiteMultigraph.ports] using List.length_filter_le (p:=fun e : Fin (P.R u).nE => decide (((P.R u).endpoints e).1 = v ∨ ((P.R u).endpoints e).2 = v)) (l:=List.finRange (P.R u).nE)
    rw [P.edges] at hh; exact hh.trans ((beta_le_nV x).trans hd)
  have hw : w.length ≤ 8*(L+2) := by
    simp only [w, encodePortQuery, Encoding.encodeList,List.length_cons,List.length_append,flen,List.length_ofFn,id_eq,List.length_nil]; have hv := cw_small v.val; have := v.isLt; dsimp [L] at *; omega
  have hR' : (residue P.f x.l q P.hf (P.w u)).length ≤ (branch P u).length := memberLen _ _ (by simp [q])
  have hd' : x.l*P.f.natDegree ≤ L := by
    have h := count_len countWord (List.ofFn fun z => word P.f x.l q P.hf (P.w u) (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2)
    exact (by simpa only [List.length_ofFn,residue,encodeNatListBin] using h : x.l*P.f.natDegree ≤ (residue P.f x.l q P.hf (P.w u)).length) |>.trans (hR'.trans hb)
  have hs : src.length ≤ (2*(q+1)+2)*(x.l*P.f.natDegree)+1 := by
    unfold src residue encodeNatListBin
    apply (enc_len _ _ (q+1) ?_).trans; swap; simp
    · intro z; apply cw_bound; apply ZMod.val_lt
    · simp only [List.length_ofFn,le_refl]
  have hh := Nat.mul_le_mul_left (2*(q+1)+2) hd'
  unfold lbound; omega

theorem lengths {C c : ℕ} (e : ℕ) : ∃ j : ℕ, ∀ {x : Input C c} (P : Plan x) {A o}, Enumerates A o e P →
    ∀ (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)) (v : Fin (P.R u).nV) (t : Fin ((P.R u).deg v) → Bool),
    (encodePortQuery (digitDesc P u a) v.val (List.ofFn t)).length + (residue P.f x.l (P.guard+x.p) P.hf (P.V u v t)).length ≤ np j (size x) := by
  have h := np_pb e; have hg := h.add PB.id'
  have hpoly : PB (fun n => lbound (np e n) (np e n+n)) := ((((PB.const 8).mul (h.add (PB.const 2))).add ((((PB.const 2).mul (hg.add (PB.const 1))).add (PB.const 2)).mul h)).add (PB.const 1))
  obtain ⟨j,hj⟩ := hpoly
  refine ⟨j,?_⟩; intro x P A o he u a v t
  obtain ⟨_,_,_,_,hg,_,hd,_⟩ := he
  have hg' : P.guard ≤ np e (size x) := by exact_mod_cast (hg.trans_eq (np_cast ..).symm)
  have hd' : (digitDesc P u a).length ≤ np e (size x) := by exact_mod_cast ((hd u a).trans_eq (np_cast ..).symm)
  have hp : x.p ≤ size x := x.pS.trans (Nat.le_add_right ..)
  apply (mat_len P u a v t).trans; apply le_trans _ (hj _)
  change lbound _ _ ≤ lbound (np e (size x)) (np e (size x) + size x)
  unfold lbound; gcongr
end DetDLP.D4BEntry


