-- Prove2me | solution 1 for AgriSubsidy.Combined.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T10:10:38.075186+00:00
-- url     : https://prove2.me/submissions/7f502994-c25b-45ab-bd37-55440b3849c5

import Mathlib
import Definitions.Def_AgriSubsidy_Combined_Setting
import Definitions.Def_AgriSubsidy_Combined_Majorization
set_option autoImplicit false
namespace AgriResearch
open AgriSubsidy.Combined
open scoped BigOperators
lemma foc {N : ℕ} (P : Params) (z t q : Fin N → ℝ)
    (eq : IsEquilibrium P z t q) (hpos : ∀j,0<q j) (j : Fin N) :
    P.α-z j*P.cP-P.cH+t j-P.β*(∑ i,q i)=P.β*q j := by
  classical
  let R := ∑ i ∈ Finset.univ \ {j}, q i
  have hsum : ∑i, q i=q j+R := by
    have hh := Finset.sum_update_of_mem (Finset.mem_univ j) q (q j)
    simpa [R] using hh
  let f : ℝ → ℝ := fun x => (P.α-z j*P.cP-P.cH+t j-P.β*(x+R))*x
  have hf : ∀x,profit P z t (Function.update q j x) j=f x := by
    intro x
    simp [profit,Finset.sum_update_of_mem, R,f]
  have hm : IsMaxOn f (Set.Ici 0) (q j) := by
    intro x hx
    have he := eq.2 j x hx
    rw [hf] at he
    have hself := hf (q j)
    simp only [Function.update_eq_self] at hself
    exact he.trans_eq hself
  have hd : HasDerivAt f (P.α-z j*P.cP-P.cH+t j-P.β*R-2*P.β*q j) (q j) := by
    convert (((hasDerivAt_const (q j) (P.α-z j*P.cP-P.cH+t j)).sub
      (((hasDerivAt_id (q j)).add_const R).const_mul P.β)).mul (hasDerivAt_id (q j))) using 1 <;>
      (try dsimp [f]) <;> first | rfl | ring
  have hh := (hm.isLocalMax (Ici_mem_nhds (hpos j))).hasDerivAt_eq_zero hd
  rw [hsum]
  nlinarith
lemma equilibrium_formula {N : ℕ} (P : Params) (z : Fin N → ℝ)
    (h : Standing P z) (sP sH : ℝ) (q : Fin N → ℝ)
    (eq : IsEquilibrium P z (combined z sP sH) q) (hpos : ∀j,0<q j) :
    (∀j,q j=(1/P.β)*(abar P z sP sH/((N:ℝ)+1)-(z j-zbar z)*(P.cP-sP))) ∧
    (∀j,profit P z (combined z sP sH) q j=P.β*(q j)^2) := by
  have hf := foc P z (combined z sP sH) q eq hpos
  have hsum := congrArg (fun f : Fin N→ℝ => ∑j,f j) (funext hf)
  simp only [combined,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  simp only [← Finset.sum_mul,← Finset.mul_sum] at hsum
  have hβ : P.β≠0 := ne_of_gt h.2.2.1
  have hN : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt h.1
  have hN1 : (N:ℝ)+1≠0 := by positivity
  constructor
  · intro j
    have hj := hf j
    dsimp [combined] at hj
    dsimp [abar,zbar]
    field_simp
    nlinarith [congrArg (fun x : ℝ => (N:ℝ)*x) hj,
      congrArg (fun x : ℝ => ((N:ℝ)+1)*x) hj]
  · intro j
    unfold profit
    rw [hf j]
    ring
end AgriResearch

namespace AgriResearch
open AgriSubsidy.Combined
open scoped BigOperators
lemma sum_le_top {N : ℕ} (u : Fin N→ℝ) (S : Finset (Fin N)) :
    (∑i∈S,u i) ≤ topSum u S.card := by
  have hk : S.card≤N := by simpa using Finset.card_le_card (Finset.subset_univ S)
  unfold topSum; rw [dif_pos hk]
  exact Finset.le_sup' (fun T : Finset (Fin N) => ∑i∈T,u i) (by simp)
lemma top_le {N k : ℕ} (u : Fin N→ℝ) (hk : k≤N) (r : ℝ)
    (h : ∀S : Finset (Fin N),S.card=k→(∑i∈S,u i)≤r) : topSum u k≤r := by
  unfold topSum; rw [dif_pos hk]
  apply Finset.sup'_le
  intro S hS
  exact h S (Finset.mem_powersetCard.mp hS).2
lemma top_attained {N k : ℕ} (u : Fin N→ℝ) (hk : k≤N) :
    ∃ S : Finset (Fin N),S.card=k ∧ topSum u k=∑i∈S,u i := by
  unfold topSum; rw [dif_pos hk]
  obtain ⟨S,hS,he⟩ := Finset.exists_mem_eq_sup'
    (Finset.powersetCard_nonempty.mpr (show k≤(Finset.univ : Finset (Fin N)).card by simpa))
    (fun S : Finset (Fin N) => ∑i∈S,u i)
  exact ⟨S,(Finset.mem_powersetCard.mp hS).2,he⟩
lemma top_affine {N k : ℕ} (u : Fin N→ℝ) (hk : k≤N) (c d : ℝ) (hc : 0≤c) :
    topSum (fun i=>c*u i+d) k=c*topSum u k+(k:ℝ)*d := by
  apply le_antisymm
  · apply top_le _ hk
    intro S hS
    have hs := sum_le_top u S
    rw [hS] at hs
    have hh := mul_le_mul_of_nonneg_left hs hc
    simpa [Finset.sum_add_distrib,←Finset.mul_sum, hS] using add_le_add_right hh ((k:ℝ)*d)
  · obtain ⟨S,hS,he⟩ := top_attained u hk
    have hs := sum_le_top (fun i=>c*u i+d) S
    simpa [Finset.sum_add_distrib,←Finset.mul_sum,hS,←he] using hs
lemma top_neg {N k : ℕ} (u : Fin N→ℝ) (hk : k≤N) :
    topSum (fun i=>-u i) k=topSum u (N-k)-∑i,u i := by
  classical
  apply le_antisymm
  · apply top_le _ hk
    intro S hS
    have hs := sum_le_top u Sᶜ
    have hc : Sᶜ.card=N-k := by simp [Finset.card_compl,hS]
    rw [hc] at hs
    have he := Finset.sum_add_sum_compl S u
    simp only [Finset.sum_neg_distrib]
    linarith
  · obtain ⟨S,hS,he⟩ := top_attained u (show N-k≤N by omega)
    have hc : Sᶜ.card=k := by simp [Finset.card_compl,hS,Nat.sub_sub_self hk]
    have hs := sum_le_top (fun i=>-u i) Sᶜ
    rw [hc] at hs
    have hsum := Finset.sum_add_sum_compl S u
    simp only [Finset.sum_neg_distrib] at hs
    rw [he]
    linarith
lemma majorizes_neg {N : ℕ} (u v : Fin N→ℝ) (h : Majorizes u v) :
    Majorizes (fun i=>-u i) (fun i=>-v i) := by
  constructor
  · intro k hk
    rw [top_neg v hk,top_neg u hk,h.2]
    exact sub_le_sub_right (h.1 (N-k) (by omega)) _
  · simp [Finset.sum_neg_distrib,h.2]
lemma majorizes_affine_nonneg {N : ℕ} (u v : Fin N→ℝ) (h : Majorizes u v)
    (c d : ℝ) (hc : 0≤c) : Majorizes (fun i=>c*u i+d) (fun i=>c*v i+d) := by
  constructor
  · intro k hk
    rw [top_affine v hk c d hc,top_affine u hk c d hc]
    exact add_le_add (mul_le_mul_of_nonneg_left (h.1 k hk) hc) le_rfl
  · simp [Finset.sum_add_distrib,←Finset.mul_sum,h.2]
lemma majorizes_affine {N : ℕ} (u v : Fin N→ℝ) (h : Majorizes u v) (c d : ℝ) :
    Majorizes (fun i=>c*u i+d) (fun i=>c*v i+d) := by
  by_cases hc : 0≤c
  · exact majorizes_affine_nonneg u v h c d hc
  · have hh := majorizes_affine_nonneg (fun i=>-u i) (fun i=>-v i)
      (majorizes_neg u v h) (-c) d (by linarith)
    simpa using hh
end AgriResearch
namespace AgriResearch
open AgriSubsidy.Combined
open scoped BigOperators
lemma same_zbar {N : ℕ} {zA zB : Fin N→ℝ} (hz : Majorizes zA zB) : zbar zA=zbar zB := by
  unfold zbar;rw [hz.2]
lemma output_majorizes {N : ℕ} (P : Params) (zA zB : Fin N→ℝ)
    (hA : Standing P zA) (hB : Standing P zB) (hz : Majorizes zA zB)
    (sP sH : ℝ) (qA qB : Fin N→ℝ)
    (eA : IsEquilibrium P zA (combined zA sP sH) qA)
    (eB : IsEquilibrium P zB (combined zB sP sH) qB)
    (hpA : ∀j,0<qA j) (hpB : ∀j,0<qB j) : Majorizes qA qB := by
  have hqa := (equilibrium_formula P zA hA sP sH qA eA hpA).1
  have hqb := (equilibrium_formula P zB hB sP sH qB eB hpB).1
  have havg : abar P zA sP sH=abar P zB sP sH := by unfold abar;rw [same_zbar hz]
  have hh := majorizes_affine zA zB hz (-(P.cP-sP)/P.β)
    ((1/P.β)*(abar P zA sP sH/((N:ℝ)+1)+zbar zA*(P.cP-sP)))
  convert hh using 1
  · funext j;rw [hqa j];ring
  · funext j;rw [hqb j,havg,same_zbar hz];ring
lemma deltaP {N : ℕ} (P : Params) (z : Fin N→ℝ) (h : Standing P z)
    (sP sH δ : ℝ) (q qP : Fin N→ℝ)
    (eq : IsEquilibrium P z (combined z sP sH) q)
    (eqP : IsEquilibrium P z (combined z (sP+δ) sH) qP)
    (hq : ∀j,0<q j) (hP : ∀j,0<qP j) (j : Fin N) :
    qP j-q j=(δ/P.β)*(z j-((N:ℝ)/((N:ℝ)+1))*zbar z) := by
  rw [(equilibrium_formula P z h sP sH q eq hq).1 j,
    (equilibrium_formula P z h (sP+δ) sH qP eqP hP).1 j]
  have hβ : P.β≠0 := ne_of_gt h.2.2.1
  have hN : (N:ℝ)+1≠0 := by positivity
  dsimp [abar];field_simp <;> ring
lemma deltaH {N : ℕ} (P : Params) (z : Fin N→ℝ) (h : Standing P z)
    (sP sH δ : ℝ) (q qH : Fin N→ℝ)
    (eq : IsEquilibrium P z (combined z sP sH) q)
    (eqH : IsEquilibrium P z (combined z sP (sH+δ)) qH)
    (hq : ∀j,0<q j) (hH : ∀j,0<qH j) (j : Fin N) :
    qH j-q j=δ/(P.β*((N:ℝ)+1)) := by
  rw [(equilibrium_formula P z h sP sH q eq hq).1 j,
    (equilibrium_formula P z h sP (sH+δ) qH eqH hH).1 j]
  have hβ : P.β≠0 := ne_of_gt h.2.2.1
  have hN : (N:ℝ)+1≠0 := by positivity
  dsimp [abar];field_simp <;> ring
lemma profit_deltaH {N : ℕ} (P : Params) (z : Fin N→ℝ) (h : Standing P z)
    (sP sH δ : ℝ) (q qH : Fin N→ℝ)
    (eq : IsEquilibrium P z (combined z sP sH) q)
    (eqH : IsEquilibrium P z (combined z sP (sH+δ)) qH)
    (hq : ∀j,0<q j) (hH : ∀j,0<qH j) (j : Fin N) :
    profit P z (combined z sP (sH+δ)) qH j-profit P z (combined z sP sH) q j=
      (2*δ/((N:ℝ)+1))*q j+δ^2/(P.β*((N:ℝ)+1)^2) := by
  rw [(equilibrium_formula P z h sP sH q eq hq).2 j,
    (equilibrium_formula P z h sP (sH+δ) qH eqH hH).2 j]
  have hd := deltaH P z h sP sH δ q qH eq eqH hq hH j
  have he : qH j=q j+δ/(P.β*((N:ℝ)+1)) := by linarith
  rw [he]
  have hβ : P.β≠0 := ne_of_gt h.2.2.1
  have hN : (N:ℝ)+1≠0 := by positivity
  field_simp <;> ring
lemma root_partial {N : ℕ} (P : Params) (zA zB : Fin N → ℝ)
    (hA : Standing P zA) (hB : Standing P zB) (hz : Majorizes zA zB)
    (sP sH δ : ℝ) (hδ : 0 < δ)
    (qA qAP qAH qB qBP qBH : Fin N → ℝ)
    (eA : IsEquilibrium P zA (combined zA sP sH) qA)
    (eAP : IsEquilibrium P zA (combined zA (sP + δ) sH) qAP)
    (eAH : IsEquilibrium P zA (combined zA sP (sH + δ)) qAH)
    (eB : IsEquilibrium P zB (combined zB sP sH) qB)
    (eBP : IsEquilibrium P zB (combined zB (sP + δ) sH) qBP)
    (eBH : IsEquilibrium P zB (combined zB sP (sH + δ)) qBH)
    (hpos : ∀ j, 0 < qA j ∧ 0 < qAP j ∧ 0 < qAH j ∧
      0 < qB j ∧ 0 < qBP j ∧ 0 < qBH j) :
    Majorizes qA qB ∧
    Majorizes (qAP - qA) (qBP - qB) ∧
    (Majorizes (qAH - qA) (qBH - qB) ∧
      Majorizes (qBH - qB) (qAH - qA)) ∧
    Majorizes
      (fun j => profit P zA (combined zA sP (sH + δ)) qAH j -
        profit P zA (combined zA sP sH) qA j)
      (fun j => profit P zB (combined zB sP (sH + δ)) qBH j -
        profit P zB (combined zB sP sH) qB j) := by
  have hpA : ∀j,0<qA j := fun j=>(hpos j).1
  have hpAP : ∀j,0<qAP j := fun j=>(hpos j).2.1
  have hpAH : ∀j,0<qAH j := fun j=>(hpos j).2.2.1
  have hpB : ∀j,0<qB j := fun j=>(hpos j).2.2.2.1
  have hpBP : ∀j,0<qBP j := fun j=>(hpos j).2.2.2.2.1
  have hpBH : ∀j,0<qBH j := fun j=>(hpos j).2.2.2.2.2
  have hq := output_majorizes P zA zB hA hB hz sP sH qA qB eA eB hpA hpB
  refine ⟨hq,?_,?_,?_⟩
  · have hh := majorizes_affine zA zB hz (δ/P.β)
      (-(δ/P.β)*((N:ℝ)/((N:ℝ)+1))*zbar zA)
    convert hh using 1
    · funext j;change qAP j-qA j=_;rw [deltaP P zA hA sP sH δ qA qAP eA eAP hpA hpAP j];ring
    · funext j;change qBP j-qB j=_;rw [deltaP P zB hB sP sH δ qB qBP eB eBP hpB hpBP j,same_zbar hz];ring
  · have he : qAH-qA=qBH-qB := by
      funext j
      exact (deltaH P zA hA sP sH δ qA qAH eA eAH hpA hpAH j).trans
        (deltaH P zB hB sP sH δ qB qBH eB eBH hpB hpBH j).symm
    rw [he]
    have hrefl : Majorizes (qBH-qB) (qBH-qB) := ⟨fun _ _=>le_rfl,rfl⟩
    exact ⟨hrefl,hrefl⟩
  · have hh := majorizes_affine qA qB hq (2*δ/((N:ℝ)+1))
      (δ^2/(P.β*((N:ℝ)+1)^2))
    convert hh using 1
    · funext j;exact profit_deltaH P zA hA sP sH δ qA qAH eA eAH hpA hpAH j
    · funext j;exact profit_deltaH P zB hB sP sH δ qB qBH eB eBH hpB hpBH j
end AgriResearch

namespace AgriResearch
open scoped BigOperators
lemma weighted_tail_le {N : ℕ} (w d : Fin N→ℝ) (hw0 : ∀i,0≤w i) (hw : Monotone w)
    (hd : ∀k : Fin N, (∑i,if k ≤ i then d i else 0)≤0) : ∑i,w i*d i≤0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    let ws : Fin N→ℝ := fun i=>w i.succ-w 0
    let ds : Fin N→ℝ := fun i=>d i.succ
    have hws0 : ∀i,0≤ws i := by intro i;exact sub_nonneg.mpr (hw (Fin.zero_le _))
    have hws : Monotone ws := by intro i j hij;exact sub_le_sub_right (hw (Fin.succ_le_succ_iff.mpr hij)) _
    have hds : ∀k : Fin N,(∑i,if k ≤ i then ds i else 0)≤0 := by
      intro k
      have h := hd k.succ
      rw [Fin.sum_univ_succ] at h
      simpa [ds] using h
    have hi := ih ws ds hws0 hws hds
    have htot : (∑i,d i)≤0 := by simpa using hd 0
    have hmul := mul_nonpos_of_nonneg_of_nonpos (hw0 0) htot
    have he : (∑i,w i*d i)=w 0*(∑i,d i)+∑i:Fin N,ws i*ds i := by
      rw [Fin.sum_univ_succ,Fin.sum_univ_succ (f:=d)]
      dsimp [ws,ds]
      simp only [sub_mul,Finset.sum_sub_distrib,←Finset.mul_sum]
      ring
    rw [he];linarith
end AgriResearch

namespace AgriResearch
open AgriSubsidy.Combined
open scoped BigOperators
lemma tail_max {N : ℕ} (u : Fin N→ℝ) (hu : Monotone u) (a : Fin N)
    (S : Finset (Fin N)) (hS : S.card=(Finset.Ici a).card) :
    (∑i∈S,u i)≤∑i∈Finset.Ici a,u i := by
  let U := Finset.Ici a
  have hc : (S\U).card=(U\S).card := by
    simp only [Finset.card_sdiff,Finset.inter_comm S U]
    rw [hS]
  have hlow : (∑i∈S\U,u i)≤((S\U).card:ℝ)*u a := by
    calc
      _ ≤ ∑i∈S\U,u a := Finset.sum_le_sum (by
        intro i hi
        have hh := (Finset.mem_sdiff.mp hi).2
        have : ¬(a ≤ i) := by simpa [U] using hh
        exact hu (le_of_lt (lt_of_not_ge this)))
      _ = _ := by simp
  have hhigh : ((U\S).card:ℝ)*u a≤∑i∈U\S,u i := by
    calc
      _ = ∑i∈U\S,u a := by simp
      _ ≤ _ := Finset.sum_le_sum (by intro i hi;exact hu (Finset.mem_Ici.mp (Finset.mem_sdiff.mp hi).1))
  rw [hc] at hlow
  have he := Finset.sum_sdiff_sub_sum_sdiff (s₁:=U) (s₂:=S) (f:=u)
  dsimp [U] at *
  linarith
lemma top_tail {N : ℕ} (u : Fin N→ℝ) (hu : Monotone u) (a : Fin N) :
    topSum u (Finset.Ici a).card=∑i∈Finset.Ici a,u i := by
  apply le_antisymm
  · apply top_le _ (by simpa using Finset.card_le_card (Finset.subset_univ (Finset.Ici a)))
    exact fun S hS=>tail_max u hu a S hS
  · exact sum_le_top u _
lemma ordered_square {N : ℕ} (u v : Fin N→ℝ) (hu : Monotone u) (hv : Monotone v)
    (hu0 : ∀i,0≤u i) (hv0 : ∀i,0≤v i) (h : WeakSubMaj u v) :
    WeakSubMaj (fun i=>(u i)^2) (fun i=>(v i)^2) := by
  have hd : ∀a : Fin N,(∑i,if a ≤ i then v i-u i else 0)≤0 := by
    intro a
    have hh := h (Finset.Ici a).card (by simpa using Finset.card_le_card (Finset.subset_univ (Finset.Ici a)))
    rw [top_tail v hv a,top_tail u hu a] at hh
    have hf : Finset.univ.filter (fun i : Fin N=>a ≤ i)=Finset.Ici a := by ext i;simp
    rw [←Finset.sum_filter,hf,Finset.sum_sub_distrib]
    linarith
  have hsqmono : Monotone (fun i=>(v i)^2) := by
    intro i j hij
    exact pow_le_pow_left₀ (hv0 i) (hv hij) 2
  have hsqmonoU : Monotone (fun i=>(u i)^2) := by
    intro i j hij
    exact pow_le_pow_left₀ (hu0 i) (hu hij) 2
  intro k hk
  by_cases hk0 : k=0
  · subst k;simp [topSum]
  let a : Fin N := ⟨N-k,by omega⟩
  have hc : (Finset.Ici a).card=k := by simp [Fin.card_Ici,a,Nat.sub_sub_self hk]
  rw [←hc,top_tail _ hsqmono a,top_tail _ hsqmonoU a]
  let w : Fin N→ℝ := fun i=>if a ≤ i then v i else 0
  have hw0 : ∀i,0≤w i := by intro i;dsimp [w];split_ifs;exact hv0 i;exact le_rfl
  have hw : Monotone w := by
    intro i j hij;dsimp [w];split_ifs with hi hj hj
    · exact hv hij
    · exact False.elim (hj (le_trans hi hij))
    · exact hv0 j
    · exact le_rfl
  have hh := weighted_tail_le w (fun i=>v i-u i) hw0 hw hd
  have hf : Finset.univ.filter (fun i : Fin N=>a ≤ i)=Finset.Ici a := by ext i;simp
  have he : (∑i,w i*(v i-u i))=∑i∈Finset.Ici a,v i*(v i-u i) := by
    dsimp [w];simp_rw [ite_mul,zero_mul];rw [←Finset.sum_filter,hf]
  rw [he] at hh
  have hs : 0≤∑i∈Finset.Ici a,(u i-v i)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have he1 : (∑i∈Finset.Ici a,v i*(v i-u i))=
      (∑i∈Finset.Ici a,(v i)^2)-(∑i∈Finset.Ici a,u i*v i) := by
    rw [←Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intro i hi;ring
  have he2 : (∑i∈Finset.Ici a,(u i-v i)^2)=
      (∑i∈Finset.Ici a,(u i)^2)+(∑i∈Finset.Ici a,(v i)^2)-2*(∑i∈Finset.Ici a,u i*v i) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i hi;ring
  rw [he1] at hh;rw [he2] at hs;linarith
end AgriResearch

namespace AgriResearch
open AgriSubsidy.Combined
open scoped BigOperators
lemma top_equiv_le {N k : ℕ} (u : Fin N→ℝ) (e : Equiv.Perm (Fin N)) (hk : k≤N) :
    topSum (fun i=>u (e i)) k≤topSum u k := by
  apply top_le _ hk
  intro S hS
  have hh := sum_le_top u (S.map e.toEmbedding)
  simpa [Finset.sum_map,hS] using hh
lemma top_equiv {N k : ℕ} (u : Fin N→ℝ) (e : Equiv.Perm (Fin N)) (hk : k≤N) :
    topSum (fun i=>u (e i)) k=topSum u k := by
  apply le_antisymm (top_equiv_le u e hk)
  have hh := top_equiv_le (fun i=>u (e i)) e.symm hk
  simpa using hh
lemma weak_equiv {N : ℕ} (u v : Fin N→ℝ) (e : Equiv.Perm (Fin N)) :
    WeakSubMaj (fun i=>u (e i)) (fun i=>v (e i)) ↔ WeakSubMaj u v := by
  constructor <;> intro h k hk
  · have hh := h k hk; rwa [top_equiv v e hk,top_equiv u e hk] at hh
  · rw [top_equiv v e hk,top_equiv u e hk];exact h k hk
lemma anti_square {N : ℕ} (u v : Fin N→ℝ) (hu : Antitone u) (hv : Antitone v)
    (hu0 : ∀i,0≤u i) (hv0 : ∀i,0≤v i) (h : WeakSubMaj u v) :
    WeakSubMaj (fun i=>(u i)^2) (fun i=>(v i)^2) := by
  have hu' : Monotone (fun i=>u (Fin.revPerm i)) := by
    intro i j hij;exact hu (Fin.rev_le_rev.mpr hij)
  have hv' : Monotone (fun i=>v (Fin.revPerm i)) := by
    intro i j hij;exact hv (Fin.rev_le_rev.mpr hij)
  have hh := ordered_square (fun i=>u (Fin.revPerm i)) (fun i=>v (Fin.revPerm i)) hu' hv'
    (fun i=>hu0 _) (fun i=>hv0 _) ((weak_equiv u v Fin.revPerm).mpr h)
  exact (weak_equiv (fun i=>(u i)^2) (fun i=>(v i)^2) Fin.revPerm).mp hh
lemma profit_weak {N : ℕ} (P : Params) (zA zB : Fin N→ℝ)
    (hA : Standing P zA) (hB : Standing P zB) (hz : Majorizes zA zB)
    (sP sH : ℝ) (qA qB : Fin N→ℝ)
    (eA : IsEquilibrium P zA (combined zA sP sH) qA)
    (eB : IsEquilibrium P zB (combined zB sP sH) qB)
    (hpA : ∀j,0<qA j) (hpB : ∀j,0<qB j) :
    WeakSubMaj (fun j=>profit P zA (combined zA sP sH) qA j)
      (fun j=>profit P zB (combined zB sP sH) qB j) := by
  have hqa := equilibrium_formula P zA hA sP sH qA eA hpA
  have hqb := equilibrium_formula P zB hB sP sH qB eB hpB
  have hq := output_majorizes P zA zB hA hB hz sP sH qA qB eA eB hpA hpB
  have hsq : WeakSubMaj (fun i=>(qA i)^2) (fun i=>(qB i)^2) := by
    by_cases hc : 0≤P.cP-sP
    · have ha : Antitone qA := by
        intro i j hij;rw [hqa.1 i,hqa.1 j]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos.mpr hA.2.2.1))
        have hh := mul_le_mul_of_nonneg_right (hA.2.2.2.1 hij) hc
        nlinarith
      have hb : Antitone qB := by
        intro i j hij;rw [hqb.1 i,hqb.1 j]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos.mpr hB.2.2.1))
        have hh := mul_le_mul_of_nonneg_right (hB.2.2.2.1 hij) hc
        nlinarith
      exact anti_square qA qB ha hb (fun i=>(hpA i).le) (fun i=>(hpB i).le) hq.1
    · have ha : Monotone qA := by
        intro i j hij;rw [hqa.1 i,hqa.1 j]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos.mpr hA.2.2.1))
        have hh := mul_le_mul_of_nonpos_right (hA.2.2.2.1 hij) (le_of_lt (lt_of_not_ge hc))
        nlinarith
      have hb : Monotone qB := by
        intro i j hij;rw [hqb.1 i,hqb.1 j]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos.mpr hB.2.2.1))
        have hh := mul_le_mul_of_nonpos_right (hB.2.2.2.1 hij) (le_of_lt (lt_of_not_ge hc))
        nlinarith
      exact ordered_square qA qB ha hb (fun i=>(hpA i).le) (fun i=>(hpB i).le) hq.1
  have hfa : (fun j=>profit P zA (combined zA sP sH) qA j)=(fun j=>P.β*(qA j)^2+0) := by
    funext j;simpa using hqa.2 j
  have hfb : (fun j=>profit P zB (combined zB sP sH) qB j)=(fun j=>P.β*(qB j)^2+0) := by
    funext j;simpa using hqb.2 j
  rw [hfa,hfb]
  intro k hk
  rw [top_affine _ hk _ _ hA.2.2.1.le,top_affine _ hk _ _ hA.2.2.1.le]
  exact add_le_add (mul_le_mul_of_nonneg_left (hsq k hk) hA.2.2.1.le) le_rfl
end AgriResearch

open AgriSubsidy.Combined

theorem solution {N : ℕ} (P : Params) (zA zB : Fin N → ℝ)
    (hA : Standing P zA) (hB : Standing P zB) (hz : Majorizes zA zB)
    (sP sH δ : ℝ) (hδ : 0 < δ)
    (qA qAP qAH qB qBP qBH : Fin N → ℝ)
    (eA : IsEquilibrium P zA (combined zA sP sH) qA)
    (eAP : IsEquilibrium P zA (combined zA (sP + δ) sH) qAP)
    (eAH : IsEquilibrium P zA (combined zA sP (sH + δ)) qAH)
    (eB : IsEquilibrium P zB (combined zB sP sH) qB)
    (eBP : IsEquilibrium P zB (combined zB (sP + δ) sH) qBP)
    (eBH : IsEquilibrium P zB (combined zB sP (sH + δ)) qBH)
    (hpos : ∀ j, 0 < qA j ∧ 0 < qAP j ∧ 0 < qAH j ∧
      0 < qB j ∧ 0 < qBP j ∧ 0 < qBH j) :
    Majorizes qA qB ∧
    Majorizes (qAP - qA) (qBP - qB) ∧
    (Majorizes (qAH - qA) (qBH - qB) ∧
      Majorizes (qBH - qB) (qAH - qA)) ∧
    WeakSubMaj
      (fun j => profit P zA (combined zA sP sH) qA j)
      (fun j => profit P zB (combined zB sP sH) qB j) ∧
    Majorizes
      (fun j => profit P zA (combined zA sP (sH + δ)) qAH j -
        profit P zA (combined zA sP sH) qA j)
      (fun j => profit P zB (combined zB sP (sH + δ)) qBH j -
        profit P zB (combined zB sP sH) qB j) := by
  obtain ⟨hq,hp,hh,hd⟩ := AgriResearch.root_partial P zA zB hA hB hz sP sH δ hδ qA qAP qAH qB qBP qBH eA eAP eAH eB eBP eBH hpos
  refine ⟨hq,hp,hh,?_,hd⟩
  exact AgriResearch.profit_weak P zA zB hA hB hz sP sH qA qB eA eB
    (fun j=>(hpos j).1) (fun j=>(hpos j).2.2.2.1)


#print axioms solution
