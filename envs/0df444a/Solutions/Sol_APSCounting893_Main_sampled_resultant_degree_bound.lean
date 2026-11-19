-- Prove2me | solution 1 for APSCounting893.Main.sampled_resultant_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T20:05:20.140774+00:00
-- url     : https://prove2.me/submissions/ef1b3075-7c41-49dd-a5e9-f7e855c9ff53

import Definitions.Def_APSCounting893_Main_Resultant
import Definitions.Def_APSCounting893_Main_SampledResultant
import Mathlib
import Theorems.Thm_APSCounting893_Main_normalized_resultant_foundation
import Theorems.Thm_ResultantVNP_lemma_2_2
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def universalResultantSystem : ResultantVNP.ResultantSystem where
  res:=universalResultant
  spec:=by
    intro n d hn hd
    cases n with
    | zero => omega
    | succ n => exact Classical.epsilon_spec (normalized_resultant_foundation d hd).1

lemma universalResultant_homogeneous {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i,0 < d i) :
    (universalResultant d).IsHomogeneous (∑ i,∏ j ∈ Finset.univ.erase i,d j) :=
  (ResultantVNP.lemma_2_2 universalResultantSystem (by omega) d hd).2.2.1

lemma universalResultant_totalDegree_le {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i,0 < d i) :
    (universalResultant d).totalDegree ≤ ∑ i,∏ j ∈ Finset.univ.erase i,d j := by
  have hh:=universalResultant_homogeneous d hd
  exact hh.totalDegree_le

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 500000
open MvPolynomial
namespace APSCounting893.Main

lemma homogenizeAll_coefficient_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (d : ℕ) (p : MvPolynomial (Fin n) K) :
    MvPolynomial.map f (homogenizeAll d p)=homogenizeAll d (MvPolynomial.map f p) := by
  classical
  unfold homogenizeAll
  rw [map_sum]
  simp only [MvPolynomial.map_monomial,MvPolynomial.coeff_map]
  apply (Finset.sum_subset (MvPolynomial.support_map_subset f p) ?_).symm
  intro e he hne
  have hz : f (p.coeff e)=0 := by
    by_contra hn
    exact hne (by simpa only [MvPolynomial.mem_support_iff,MvPolynomial.coeff_map] using hn)
  rw [hz]
  exact MvPolynomial.monomial_zero

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 800000
open MvPolynomial
namespace APSCounting893.Main

noncomputable def auxiliaryEquation {K : Type} [CommRing K] {n : ℕ}
    (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K)
    (i : Fin (n+(n+1))) : MvPolynomial (Fin (n+(n+1))) (MvPolynomial (Fin 4) K) :=
  Fin.addCases
    (fun j => MvPolynomial.X (j.natAdd n) -
      MvPolynomial.rename (fun i : Fin n => i.castAdd (n+1)) (MvPolynomial.map MvPolynomial.C (F j)))
    (fun j => MvPolynomial.X (j.castSucc.natAdd n) -
      MvPolynomial.C (MvPolynomial.C (c j)) * MvPolynomial.X ((Fin.last n).natAdd n) -
      MvPolynomial.C (MvPolynomial.C (alpha j) * MvPolynomial.X 2)) (Fin.cast (Nat.add_comm _ _) i)

lemma equationWithAux_eq_auxiliaryEquation (F : RawMap) (c alpha : Fin F.n → ℂ)
    (i : Fin (F.n+(F.n+1))) : equationWithAux F c alpha i=auxiliaryEquation F.F c alpha i := by
  unfold equationWithAux affineLineEquations auxiliaryEquation
  generalize Fin.cast (Nat.add_comm _ _) i = j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp only [Fin.addCases_left,map_sub,MvPolynomial.map_X,MvPolynomial.map_rename,MvPolynomial.map_map]
    congr 2
    apply congrArg (fun f => MvPolynomial.map f (F.F j))
    ext z
    simp
  · intro j
    simp [Fin.addCases_right]

lemma auxiliaryEquation_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K)
    (i : Fin (n+(n+1))) :
    MvPolynomial.map (MvPolynomial.map f) (auxiliaryEquation F c alpha i)=
      auxiliaryEquation (fun j => MvPolynomial.map f (F j)) (fun j => f (c j)) (fun j => f (alpha j)) i := by
  unfold auxiliaryEquation
  generalize Fin.cast (Nat.add_comm _ _) i = j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp only [Fin.addCases_left,map_sub,MvPolynomial.map_X,MvPolynomial.map_rename,MvPolynomial.map_map]
    congr 2
    apply congrArg (fun g => MvPolynomial.map g (F j))
    ext z
    simp
  · intro j
    simp [Fin.addCases_right]

noncomputable def auxiliaryHForm {K : Type} [CommRing K] {n : ℕ} (lambda : Fin (n+1) → K) :
    MvPolynomial (Fin (n+(n+1)+1)) (MvPolynomial (Fin 4) K) :=
  MvPolynomial.C (MvPolynomial.X 3) * MvPolynomial.X 0 ^ 2 -
    MvPolynomial.X 0 * (∑ j : Fin (n+1),
      MvPolynomial.C (MvPolynomial.C (lambda j)) * MvPolynomial.X (j.natAdd n).succ) +
    ∑ j : Fin (n+(n+1)),
      MvPolynomial.C (MvPolynomial.X 1 ^ (j.val+1)) * MvPolynomial.X j.succ ^ 2

lemma auxiliaryHForm_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (lambda : Fin (n+1) → K) :
    MvPolynomial.map (MvPolynomial.map f) (auxiliaryHForm lambda)=auxiliaryHForm (fun j => f (lambda j)) := by
  simp [auxiliaryHForm,map_sum]

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 800000
open MvPolynomial
namespace APSCounting893.Main

noncomputable def auxiliaryPerturbedEquation {K : Type} [CommRing K] {n : ℕ}
    (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K)
    (degrees : Fin (n+(n+1)) → ℕ) (i : Fin (n+(n+1))) :
    MvPolynomial (Fin (n+(n+1)+1)) (MvPolynomial (Fin 4) K) :=
  homogenizeAll (degrees i) (auxiliaryEquation F c alpha i) +
    MvPolynomial.C (MvPolynomial.X 0) * MvPolynomial.X i.succ ^ degrees i

noncomputable def auxiliaryResultant {K : Type} [CommRing K] {n : ℕ}
    (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K)
    (lambda : Fin (n+1) → K) (degrees : Fin (n+(n+1)) → ℕ) : MvPolynomial (Fin 4) K :=
  homogeneousResultant (Fin.lastCases 2 degrees)
    (Fin.lastCases (auxiliaryHForm lambda) (auxiliaryPerturbedEquation F c alpha degrees))

lemma perturbedEquation_eq_auxiliary (F : RawMap) (c alpha : Fin F.n → ℂ)
    (degrees : Fin (F.n+(F.n+1)) → ℕ) (i : Fin (F.n+(F.n+1))) :
    perturbedEquation F c alpha degrees i=auxiliaryPerturbedEquation F.F c alpha degrees i := by
  simp only [perturbedEquation,homogenizedEquation,auxiliaryPerturbedEquation,
    equationWithAux_eq_auxiliaryEquation]

lemma resultantFor_eq_auxiliary (F : RawMap) (c alpha : Fin F.n → ℂ)
    (lambda : Fin (F.n+1) → ℂ) (degrees : Fin (F.n+(F.n+1)) → ℕ) :
    resultantFor F c alpha lambda degrees=auxiliaryResultant F.F c alpha lambda degrees := by
  unfold resultantFor auxiliaryResultant
  apply congrArg (homogeneousResultant _)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
    rfl
  · simp only [Fin.lastCases_castSucc,perturbedEquation_eq_auxiliary]

lemma auxiliaryPerturbedEquation_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K)
    (degrees : Fin (n+(n+1)) → ℕ) (i : Fin (n+(n+1))) :
    MvPolynomial.map (MvPolynomial.map f) (auxiliaryPerturbedEquation F c alpha degrees i)=
      auxiliaryPerturbedEquation (fun j => MvPolynomial.map f (F j))
        (fun j => f (c j)) (fun j => f (alpha j)) degrees i := by
  simp only [auxiliaryPerturbedEquation,map_add,homogenizeAll_coefficient_map,auxiliaryEquation_map,
    map_mul,map_pow,MvPolynomial.map_C,MvPolynomial.map_X]

lemma homogeneousResultant_coefficient_map {K L : Type} [CommRing K] [CommRing L]
    (f : K →+* L) {n : ℕ} (d : Fin n → ℕ) (G : Fin n → MvPolynomial (Fin n) K) :
    f (homogeneousResultant d G)=homogeneousResultant d (fun i => MvPolynomial.map f (G i)) := by
  unfold homogeneousResultant
  rw [MvPolynomial.eval₂_comp_left]
  have hcast : f.comp (Int.castRingHom K)=Int.castRingHom L := by ext z;simp
  rw [hcast]
  apply MvPolynomial.eval₂Hom_congr rfl _ rfl
  funext v
  rw [MvPolynomial.coeff_map]
  rfl

lemma auxiliaryResultant_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K)
    (lambda : Fin (n+1) → K) (degrees : Fin (n+(n+1)) → ℕ) :
    MvPolynomial.map f (auxiliaryResultant F c alpha lambda degrees)=
      auxiliaryResultant (fun j => MvPolynomial.map f (F j))
        (fun j => f (c j)) (fun j => f (alpha j)) (fun j => f (lambda j)) degrees := by
  unfold auxiliaryResultant
  rw [homogeneousResultant_coefficient_map]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last,auxiliaryHForm_map]
  · simp only [Fin.lastCases_castSucc,auxiliaryPerturbedEquation_map]

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open MvPolynomial

def AuxiliaryCoefficientDegree {K σ τ : Type} [CommRing K]
    (p : MvPolynomial σ (MvPolynomial τ K)) (D : ℕ) : Prop :=
  ∀ e,(p.coeff e).totalDegree ≤ D

lemma AuxiliaryCoefficientDegree.mono {K σ τ : Type} [CommRing K]
    {p : MvPolynomial σ (MvPolynomial τ K)} {D E : ℕ}
    (hp : AuxiliaryCoefficientDegree p D) (hDE : D ≤ E) : AuxiliaryCoefficientDegree p E :=
  fun e => (hp e).trans hDE

lemma AuxiliaryCoefficientDegree.zero {K σ τ : Type} [CommRing K] (D : ℕ) :
    AuxiliaryCoefficientDegree (0 : MvPolynomial σ (MvPolynomial τ K)) D := by intro e;simp

lemma AuxiliaryCoefficientDegree.one {K σ τ : Type} [CommRing K] :
    AuxiliaryCoefficientDegree (1 : MvPolynomial σ (MvPolynomial τ K)) 0 := by
  intro e
  classical
  simp only [MvPolynomial.coeff_one]
  split_ifs <;> simp

lemma AuxiliaryCoefficientDegree.add {K σ τ : Type} [CommRing K]
    {p q : MvPolynomial σ (MvPolynomial τ K)} {D : ℕ}
    (hp : AuxiliaryCoefficientDegree p D) (hq : AuxiliaryCoefficientDegree q D) :
    AuxiliaryCoefficientDegree (p+q) D := by
  intro e
  rw [coeff_add]
  exact (totalDegree_add _ _).trans (max_le (hp e) (hq e))

lemma AuxiliaryCoefficientDegree.sub {K σ τ : Type} [CommRing K]
    {p q : MvPolynomial σ (MvPolynomial τ K)} {D : ℕ}
    (hp : AuxiliaryCoefficientDegree p D) (hq : AuxiliaryCoefficientDegree q D) :
    AuxiliaryCoefficientDegree (p-q) D := by
  intro e
  rw [coeff_sub]
  exact (totalDegree_sub _ _).trans (max_le (hp e) (hq e))

lemma AuxiliaryCoefficientDegree.mul {K σ τ : Type} [CommRing K]
    {p q : MvPolynomial σ (MvPolynomial τ K)} {D E : ℕ}
    (hp : AuxiliaryCoefficientDegree p D) (hq : AuxiliaryCoefficientDegree q E) :
    AuxiliaryCoefficientDegree (p*q) (D+E) := by
  classical
  intro e
  rw [coeff_mul]
  apply totalDegree_finsetSum_le
  intro ab hab
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (hp ab.1) (hq ab.2))

lemma AuxiliaryCoefficientDegree.pow {K σ τ : Type} [CommRing K]
    {p : MvPolynomial σ (MvPolynomial τ K)} {D : ℕ}
    (hp : AuxiliaryCoefficientDegree p D) (r : ℕ) : AuxiliaryCoefficientDegree (p^r) (D*r) := by
  induction r with
  | zero => simpa using (AuxiliaryCoefficientDegree.one (K:=K) (σ:=σ) (τ:=τ))
  | succ r ih => simpa only [pow_succ,Nat.mul_succ] using ih.mul hp

lemma AuxiliaryCoefficientDegree.sum {K σ τ ι : Type} [CommRing K]
    (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial τ K)) (D : ℕ)
    (hf : ∀ i ∈ s,AuxiliaryCoefficientDegree (f i) D) :
    AuxiliaryCoefficientDegree (∑ i ∈ s,f i) D := by
  classical
  intro e
  rw [coeff_sum]
  exact totalDegree_finsetSum_le (fun i hi => hf i hi e)

lemma AuxiliaryCoefficientDegree.monomial {K σ τ : Type} [CommRing K]
    (e : σ →₀ ℕ) (a : MvPolynomial τ K) :
    AuxiliaryCoefficientDegree (monomial e a) a.totalDegree := by
  classical
  intro f
  simp only [coeff_monomial]
  split_ifs <;> simp

lemma AuxiliaryCoefficientDegree.C {K σ τ : Type} [CommRing K] (a : MvPolynomial τ K) :
    AuxiliaryCoefficientDegree (C a : MvPolynomial σ (MvPolynomial τ K)) a.totalDegree := by
  exact AuxiliaryCoefficientDegree.monomial 0 a

lemma AuxiliaryCoefficientDegree.X {K σ τ : Type} [CommRing K] (i : σ) :
    AuxiliaryCoefficientDegree (X i : MvPolynomial σ (MvPolynomial τ K)) 0 := by
  simpa only [MvPolynomial.X,totalDegree_one] using
    AuxiliaryCoefficientDegree.monomial (Finsupp.single i 1) (1 : MvPolynomial τ K)

lemma AuxiliaryCoefficientDegree.map_C {K σ τ : Type} [CommRing K] (p : MvPolynomial σ K) :
    AuxiliaryCoefficientDegree (MvPolynomial.map MvPolynomial.C p : MvPolynomial σ (MvPolynomial τ K)) 0 := by
  intro e
  simp [coeff_map]

lemma AuxiliaryCoefficientDegree.homogenize {K τ : Type} [CommRing K] {n : ℕ}
    {p : MvPolynomial (Fin n) (MvPolynomial τ K)} {D : ℕ}
    (hp : AuxiliaryCoefficientDegree p D) (r : ℕ) :
    AuxiliaryCoefficientDegree (homogenizeAll r p) D := by
  apply AuxiliaryCoefficientDegree.sum
  intro e he
  exact (AuxiliaryCoefficientDegree.monomial _ _).mono (hp e)

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open MvPolynomial

lemma totalDegree_eval₂_bounded_types {K L σ τ : Type} [CommRing K] [CommRing L] [Fintype σ]
    (f : K →+* L) (g : σ → MvPolynomial τ L) (D : ℕ)
    (hg : ∀ i,(g i).totalDegree ≤ D) (p : MvPolynomial σ K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ D*p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp,Function.comp_apply,totalDegree_C,zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  rw [←Finset.sum_mul]
  simpa [Finsupp.sum_fintype,Nat.mul_comm] using Nat.mul_le_mul_right D (le_totalDegree he)

lemma homogeneousResultant_auxiliary_degree {K τ : Type} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (hd : ∀ i,0 < d i)
    (G : Fin (n+1) → MvPolynomial (Fin (n+1)) (MvPolynomial τ K)) (D : ℕ)
    (hG : ∀ i,AuxiliaryCoefficientDegree (G i) D) :
    (homogeneousResultant d G).totalDegree ≤ D*(∑ i,∏ j ∈ Finset.univ.erase i,d j) := by
  have hf : (Int.castRingHom (MvPolynomial τ K))=
      MvPolynomial.C.comp (Int.castRingHom K) := by ext z;simp
  unfold homogeneousResultant
  rw [hf]
  apply (totalDegree_eval₂_bounded_types (Int.castRingHom K)
    (fun v : ResultantVNP.CoeffVar d => (G v.1).coeff v.2.val) D
    (fun v => hG v.1 v.2.val) (universalResultant d)).trans
  exact Nat.mul_le_mul_left D (universalResultant_totalDegree_le d hd)

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open MvPolynomial

lemma auxiliaryEquation_coefficient_degree {K : Type} [CommRing K] [Nontrivial K] {n : ℕ}
    (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K) (i : Fin (n+(n+1))) :
    AuxiliaryCoefficientDegree (τ:=Fin 4) (auxiliaryEquation F c alpha i) 1 := by
  unfold auxiliaryEquation
  generalize Fin.cast (Nat.add_comm _ _) i=j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp only [Fin.addCases_left]
    have hf : AuxiliaryCoefficientDegree (τ:=Fin 4)
        (MvPolynomial.rename (fun i : Fin n => i.castAdd (n+1)) (MvPolynomial.map C (F j))) 0 := by
      rw [←MvPolynomial.map_rename]
      exact AuxiliaryCoefficientDegree.map_C _
    exact ((AuxiliaryCoefficientDegree.X _).sub hf).mono (by omega)
  · intro j
    simp only [Fin.addCases_right]
    have hc : AuxiliaryCoefficientDegree (τ:=Fin 4)
        (C (C (c j)) : MvPolynomial (Fin (n+(n+1))) (MvPolynomial (Fin 4) K)) 0 := by
      simpa only [totalDegree_C] using AuxiliaryCoefficientDegree.C (σ:=Fin (n+(n+1))) (C (c j))
    have hfirst : AuxiliaryCoefficientDegree (τ:=Fin 4)
        (X (j.castSucc.natAdd n) - C (C (c j))*X ((Fin.last n).natAdd n)) 0 := by
      exact (AuxiliaryCoefficientDegree.X _).sub (by simpa using hc.mul (AuxiliaryCoefficientDegree.X _))
    have hlast : AuxiliaryCoefficientDegree (τ:=Fin 4)
        (C (C (alpha j)*X 2) : MvPolynomial (Fin (n+(n+1))) (MvPolynomial (Fin 4) K)) 1 := by
      apply (AuxiliaryCoefficientDegree.C _).mono
      exact (totalDegree_mul _ _).trans (by simp)
    exact (hfirst.mono (by omega)).sub hlast

lemma auxiliaryPerturbedEquation_coefficient_degree {K : Type} [CommRing K] [Nontrivial K] {n : ℕ}
    (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K)
    (d : Fin (n+(n+1)) → ℕ) (i : Fin (n+(n+1))) :
    AuxiliaryCoefficientDegree (τ:=Fin 4) (auxiliaryPerturbedEquation F c alpha d i) 1 := by
  have hfirst := (auxiliaryEquation_coefficient_degree F c alpha i).homogenize (d i)
  have heps : AuxiliaryCoefficientDegree (τ:=Fin 4)
      (C (X 0) : MvPolynomial (Fin (n+(n+1)+1)) (MvPolynomial (Fin 4) K)) 1 := by
    simpa using AuxiliaryCoefficientDegree.C (σ:=Fin (n+(n+1)+1)) (X (0 : Fin 4) : MvPolynomial (Fin 4) K)
  have hx : AuxiliaryCoefficientDegree (τ:=Fin 4)
      (X i.succ ^ d i : MvPolynomial (Fin (n+(n+1)+1)) (MvPolynomial (Fin 4) K)) 0 := by
    simpa using (AuxiliaryCoefficientDegree.X (K:=K) (τ:=Fin 4) i.succ).pow (d i)
  exact hfirst.add (by simpa using heps.mul hx)

lemma auxiliaryHForm_coefficient_degree {K : Type} [CommRing K] [Nontrivial K] {n : ℕ}
    (lambda : Fin (n+1) → K) :
    AuxiliaryCoefficientDegree (τ:=Fin 4) (auxiliaryHForm lambda) (n+(n+1)) := by
  let N := n+(n+1)
  have hN : 1 ≤ N := by dsimp [N];omega
  have hx (j : Fin (N+1)) (r : ℕ) :
      AuxiliaryCoefficientDegree (τ:=Fin 4) (X j^r : MvPolynomial (Fin (N+1)) (MvPolynomial (Fin 4) K)) 0 := by
    simpa using (AuxiliaryCoefficientDegree.X (K:=K) (τ:=Fin 4) j).pow r
  have ht : AuxiliaryCoefficientDegree (τ:=Fin 4)
      (C (X 3)*X 0^2 : MvPolynomial (Fin (N+1)) (MvPolynomial (Fin 4) K)) 1 := by
    have hc : AuxiliaryCoefficientDegree (τ:=Fin 4) (C (X 3) : MvPolynomial (Fin (N+1)) (MvPolynomial (Fin 4) K)) 1 := by
      simpa using AuxiliaryCoefficientDegree.C (σ:=Fin (N+1)) (X (3 : Fin 4) : MvPolynomial (Fin 4) K)
    simpa using hc.mul (hx 0 2)
  have hm : AuxiliaryCoefficientDegree (τ:=Fin 4)
      (∑ j : Fin (n+1),C (C (lambda j))*X (j.natAdd n).succ) 0 := by
    apply AuxiliaryCoefficientDegree.sum
    intro j _
    have hc : AuxiliaryCoefficientDegree (τ:=Fin 4)
        (C (C (lambda j)) : MvPolynomial (Fin (N+1)) (MvPolynomial (Fin 4) K)) 0 := by
      simpa only [totalDegree_C] using AuxiliaryCoefficientDegree.C (σ:=Fin (N+1)) (C (lambda j))
    simpa using hc.mul (AuxiliaryCoefficientDegree.X _)
  have hw : AuxiliaryCoefficientDegree (τ:=Fin 4)
      (∑ j : Fin N,C (X 1^(j.val+1))*X j.succ^2 : MvPolynomial (Fin (N+1)) (MvPolynomial (Fin 4) K)) N := by
    apply AuxiliaryCoefficientDegree.sum
    intro j _
    have hc : AuxiliaryCoefficientDegree (τ:=Fin 4)
        (C (X 1^(j.val+1)) : MvPolynomial (Fin (N+1)) (MvPolynomial (Fin 4) K)) (j.val+1) := by
      apply (AuxiliaryCoefficientDegree.C _).mono
      exact (totalDegree_pow _ _).trans (by simp)
    have hp : AuxiliaryCoefficientDegree (τ:=Fin 4)
        (C (X 1^(j.val+1))*X j.succ^2 : MvPolynomial (Fin (N+1)) (MvPolynomial (Fin 4) K)) (j.val+1) := by
      simpa using hc.mul (hx j.succ 2)
    exact hp.mono (by have := j.isLt;omega)
  unfold auxiliaryHForm
  apply ((ht.mono hN).sub ?_).add hw
  have hp : AuxiliaryCoefficientDegree (τ:=Fin 4)
      (X 0*(∑ j : Fin (n+1),C (C (lambda j))*X (j.natAdd n).succ)) 0 := by
    simpa using (AuxiliaryCoefficientDegree.X (K:=K) (τ:=Fin 4) (0 : Fin (N+1))).mul hm
  exact hp.mono (by omega)

end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace APSCounting893.Main

lemma encodeNat_length_pos (n : ℕ) : 0<(encodeNat n).length := by
  simp [encodeNat]

lemma arithmeticGate_encode_length_pos {n : ℕ} (g : ArithmeticGate n) : 0<g.encode.length := by
  cases g <;> simp [ArithmeticGate.encode,encodeNat]

lemma gates_length_le_flatMap_encode {n : ℕ} (gs : List (ArithmeticGate n)) :
    gs.length≤(gs.flatMap ArithmeticGate.encode).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg:=arithmeticGate_encode_length_pos g
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

lemma circuit_gates_length_le_encode {n : ℕ} (C : ArithmeticCircuit n) : C.gates.length≤C.encode.length := by
  have hh:=gates_length_le_flatMap_encode C.gates
  simp only [ArithmeticCircuit.encode,encodeList,List.length_append]
  omega

lemma output_count_le_encode {n : ℕ} (C : ArithmeticCircuit n) : C.outputs.length≤C.encode.length := by
  have hh : C.outputs.length≤(C.outputs.flatMap encodeNat).length := by
    induction C.outputs with
    | nil => rfl
    | cons o os ih =>
      have ho:=encodeNat_length_pos o
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      omega
  simp only [ArithmeticCircuit.encode,encodeList,List.length_append]
  omega

lemma ReducedCircuit.dimension_le_encode (I : ReducedCircuit) : I.n+1≤I.C.encode.length := by
  rw [←I.outputCount]
  exact output_count_le_encode I.C

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace APSCounting893.Main

lemma natList_getD_bound (xs : List ℕ) (M : ℕ) (h : ∀ d ∈ xs,d≤M) (i : ℕ) : (xs[i]?).getD 0≤M := by
  cases hi : xs[i]? with
  | none => simp [hi]
  | some v => simpa only [hi,Option.getD_some] using h v (List.mem_of_getElem? hi)

lemma gateFormalDegree_le_double {n : ℕ} (xs : List ℕ) (M : ℕ) (hM : 1≤M)
    (h : ∀ d ∈ xs,d≤M) (g : ArithmeticGate n) : gateFormalDegree xs g≤2*M := by
  cases g with
  | «variable» i => change 1≤2*M;omega
  | «constant» cs => exact Nat.zero_le _
  | add a b | sub a b | div a b =>
    exact (max_le (natList_getD_bound xs M h a) (natList_getD_bound xs M h b)).trans (by omega)
  | mul a b =>
    have ha:=natList_getD_bound xs M h a
    have hb:=natList_getD_bound xs M h b
    change (xs[a]?).getD 0+(xs[b]?).getD 0≤2*M
    omega

lemma formalDegree_fold_bound {n : ℕ} (gs : List (ArithmeticGate n)) (xs : List ℕ) (M : ℕ)
    (hM : 1≤M) (h : ∀ d ∈ xs,d≤M) :
    ∀ d ∈ gs.foldl (fun xs g => xs++[gateFormalDegree xs g]) xs,d≤2^gs.length*M := by
  induction gs generalizing xs M with
  | nil => simpa using h
  | cons g gs ih =>
    have hnew : ∀ d ∈ xs++[gateFormalDegree xs g],d≤2*M := by
      intro d hd
      rcases List.mem_append.mp hd with hd|hd
      · exact (h d hd).trans (by omega)
      · have heq : d=gateFormalDegree xs g := by simpa using hd
        rw [heq]
        exact gateFormalDegree_le_double xs M hM h g
    intro d hd
    have hh:=ih (xs++[gateFormalDegree xs g]) (2*M) (by omega) hnew d hd
    simpa [pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hh

lemma formalDegrees_entry_le_exponential {n : ℕ} (C : ArithmeticCircuit n) (i : ℕ) :
    ((formalDegrees C)[i]?).getD 0≤2^C.gates.length := by
  apply natList_getD_bound
  simpa only [formalDegrees,mul_one] using formalDegree_fold_bound C.gates [] 1 le_rfl (by simp)

lemma outputFormalDegree_le_exponential {n : ℕ} (C : ArithmeticCircuit n) (j : Fin C.outputs.length) :
    outputFormalDegree C j≤2^C.gates.length := formalDegrees_entry_le_exponential C C.outputs[j]

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def polynomialGateValue (P : CoefficientPresentation) {n : ℕ}
    (prior : List (MvPolynomial (Fin n) P.Field)) : ArithmeticGate n → Option (MvPolynomial (Fin n) P.Field)
  | .variable i => some (MvPolynomial.X i)
  | .constant cs => some (MvPolynomial.C (P.scalar cs))
  | .add a b => do return (← prior[a]?) + (← prior[b]?)
  | .sub a b => do return (← prior[a]?) - (← prior[b]?)
  | .mul a b => do return (← prior[a]?) * (← prior[b]?)
  | .div _ _ => none

noncomputable def polynomialCircuitStep (P : CoefficientPresentation) {n : ℕ}
    (acc : Option (List (MvPolynomial (Fin n) P.Field))) (g : ArithmeticGate n) :
    Option (List (MvPolynomial (Fin n) P.Field)) := do
  let prior ← acc
  let value ← polynomialGateValue P prior g
  return prior ++ [value]

noncomputable def polynomialCircuitValues (P : CoefficientPresentation) {n : ℕ}
    (C : ArithmeticCircuit n) : Option (List (MvPolynomial (Fin n) P.Field)) :=
  C.gates.foldl (polynomialCircuitStep P) (some [])

lemma polynomialGateValue_fraction {n : ℕ} (P : CoefficientPresentation)
    (prior : List (MvPolynomial (Fin n) P.Field)) (g : ArithmeticGate n)
    (hg : match g with | .div _ _ => False | _ => True) :
    gateValue P (prior.map (algebraMap (MvPolynomial (Fin n) P.Field) (CircuitFunctionField P n))) g =
      (polynomialGateValue P prior g).map (algebraMap _ (CircuitFunctionField P n)) := by
  cases g with
  | «variable» i => rfl
  | «constant» cs => rfl
  | add a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [gateValue,polynomialGateValue,List.getElem?_map,ha,hb,map_add]
  | sub a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [gateValue,polynomialGateValue,List.getElem?_map,ha,hb,map_sub]
  | mul a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [gateValue,polynomialGateValue,List.getElem?_map,ha,hb,map_mul]
  | div a b => exact hg.elim

lemma polynomialCircuitValues_fraction {n : ℕ} (P : CoefficientPresentation) (C : ArithmeticCircuit n)
    (hdf : ∀ g ∈ C.gates, match g with | .div _ _ => False | _ => True) :
    circuitValues P C = (polynomialCircuitValues P C).map
      (List.map (algebraMap (MvPolynomial (Fin n) P.Field) (CircuitFunctionField P n))) := by
  let f := algebraMap (MvPolynomial (Fin n) P.Field) (CircuitFunctionField P n)
  have hstep (acc : Option (List (MvPolynomial (Fin n) P.Field))) (g : ArithmeticGate n)
      (hg : match g with | .div _ _ => False | _ => True) :
      (do
        let prior ← acc.map (List.map f)
        let value ← gateValue P prior g
        pure (prior ++ [value])) = (polynomialCircuitStep P acc g).map (List.map f) := by
    cases acc with
    | none => rfl
    | some prior =>
      change (gateValue P (prior.map f) g).bind (fun value => some (prior.map f ++ [value])) = _
      rw [polynomialGateValue_fraction P prior g hg]
      cases hval : polynomialGateValue P prior g <;>
        simp [polynomialCircuitStep,hval,f]
  have hfold (gs : List (ArithmeticGate n))
      (hgs : ∀ g ∈ gs, match g with | .div _ _ => False | _ => True)
      (acc : Option (List (MvPolynomial (Fin n) P.Field))) :
      gs.foldl (fun acc g => do
        let prior ← acc
        let value ← gateValue P prior g
        pure (prior ++ [value])) (acc.map (List.map f)) =
      (gs.foldl (polynomialCircuitStep P) acc).map (List.map f) := by
    induction gs generalizing acc with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,List.foldl_cons,hstep acc g (hgs g (by simp))]
      exact ih (fun g hg => hgs g (by simp [hg])) _
  exact hfold C.gates hdf (some [])

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomialGateValue_degree {n : ℕ} (P : CoefficientPresentation)
    (prior : List (MvPolynomial (Fin n) P.Field)) (g : ArithmeticGate n)
    (f : MvPolynomial (Fin n) P.Field) (hf : polynomialGateValue P prior g=some f) :
    f.totalDegree ≤ gateFormalDegree (prior.map MvPolynomial.totalDegree) g := by
  cases g with
  | «variable» i =>
    simp only [polynomialGateValue,Option.some.injEq] at hf
    subst f
    simp [gateFormalDegree]
  | «constant» cs =>
    simp only [polynomialGateValue,Option.some.injEq] at hf
    subst f
    simp [gateFormalDegree]
  | add a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [polynomialGateValue,ha,hb] at hf
    subst f
    simpa [gateFormalDegree,List.getElem?_map,ha,hb] using MvPolynomial.totalDegree_add _ _
  | sub a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [polynomialGateValue,ha,hb] at hf
    subst f
    simpa [gateFormalDegree,List.getElem?_map,ha,hb] using MvPolynomial.totalDegree_sub _ _
  | mul a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [polynomialGateValue,ha,hb] at hf
    subst f
    simpa [gateFormalDegree,List.getElem?_map,ha,hb] using MvPolynomial.totalDegree_mul _ _
  | div a b => simp [polynomialGateValue] at hf

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace APSCounting893.Main

lemma list_getD_le_of_forall₂ {xs ys : List ℕ} (h : List.Forall₂ (· ≤ ·) xs ys) (i : ℕ) :
    (xs[i]?).getD 0 ≤ (ys[i]?).getD 0 := by
  induction h generalizing i with
  | nil => simp
  | @cons a b xs ys hab htail ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma gateFormalDegree_mono {n : ℕ} {xs ys : List ℕ} (h : List.Forall₂ (· ≤ ·) xs ys)
    (g : ArithmeticGate n) : gateFormalDegree xs g ≤ gateFormalDegree ys g := by
  cases g with
  | «variable» i => rfl
  | «constant» cs => rfl
  | add a b | sub a b | div a b => exact max_le_max (list_getD_le_of_forall₂ h a) (list_getD_le_of_forall₂ h b)
  | mul a b => exact Nat.add_le_add (list_getD_le_of_forall₂ h a) (list_getD_le_of_forall₂ h b)

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomialCircuitFold_none {n : ℕ} (P : CoefficientPresentation) (gs : List (ArithmeticGate n)) :
    gs.foldl (polynomialCircuitStep P) none=none := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change gs.foldl (polynomialCircuitStep P) none=none
    exact ih

lemma polynomialCircuitFold_degrees {n : ℕ} (P : CoefficientPresentation) (gs : List (ArithmeticGate n))
    (prior : List (MvPolynomial (Fin n) P.Field)) (ds : List ℕ)
    (hprior : List.Forall₂ (· ≤ ·) (prior.map MvPolynomial.totalDegree) ds)
    (out : List (MvPolynomial (Fin n) P.Field))
    (hout : gs.foldl (polynomialCircuitStep P) (some prior)=some out) :
    List.Forall₂ (· ≤ ·) (out.map MvPolynomial.totalDegree)
      (gs.foldl (fun ds g => ds++[gateFormalDegree ds g]) ds) := by
  induction gs generalizing prior ds with
  | nil =>
    have heq : prior=out := Option.some.inj hout
    subst out
    exact hprior
  | cons g gs ih =>
    cases hv : polynomialGateValue P prior g with
    | none =>
      have hs : polynomialCircuitStep P (some prior) g=none := by simp [polynomialCircuitStep,hv]
      rw [List.foldl_cons,hs,polynomialCircuitFold_none] at hout
      cases hout
    | some v =>
      have hs : polynomialCircuitStep P (some prior) g=some (prior++[v]) := by simp [polynomialCircuitStep,hv]
      rw [List.foldl_cons,hs] at hout
      rw [List.foldl_cons]
      apply ih (prior++[v]) (ds++[gateFormalDegree ds g]) ?_ hout
      rw [List.map_append]
      apply List.rel_append hprior
      exact .cons ((polynomialGateValue_degree P prior g v hv).trans (gateFormalDegree_mono hprior g)) .nil

lemma polynomialCircuitValues_degrees {n : ℕ} (P : CoefficientPresentation) (C : ArithmeticCircuit n)
    (prior : List (MvPolynomial (Fin n) P.Field)) (hp : polynomialCircuitValues P C=some prior) :
    List.Forall₂ (· ≤ ·) (prior.map MvPolynomial.totalDegree) (formalDegrees C) :=
  polynomialCircuitFold_degrees P C.gates [] [] .nil prior hp

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma circuitPolynomials_eq_of_polynomial_values {n : ℕ} (P : CoefficientPresentation)
    (C : ArithmeticCircuit n) (prior : List (MvPolynomial (Fin n) P.Field))
    (hv : circuitValues P C = some (prior.map (algebraMap _ (CircuitFunctionField P n))))
    (j : Fin C.outputs.length) : circuitPolynomials P C j=(prior[C.outputs[j]]?).getD 0 := by
  classical
  let f := algebraMap (MvPolynomial (Fin n) P.Field) (CircuitFunctionField P n)
  let v := ((circuitValues P C).getD [])[C.outputs[j]]?.getD 0
  let p := (prior[C.outputs[j]]?).getD 0
  have hp : f p=v := by
    dsimp only [v,p]
    rw [hv]
    simp only [Option.getD_some,List.getElem?_map]
    cases hh : prior[C.outputs[j]]? <;> simp [f,hh]
  have hex : ∃ p : MvPolynomial (Fin n) P.Field, f p=v := ⟨p,hp⟩
  have hchosen : f (circuitPolynomials P C j)=v := by
    unfold circuitPolynomials
    dsimp only
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact (IsFractionRing.injective _ _) (hchosen.trans hp.symm)

lemma polynomialCircuitValues_exists_of_valid_divisionFree {n : ℕ} (P : CoefficientPresentation)
    (C : ArithmeticCircuit n) (hvalid : ValidCircuit P C)
    (hdf : ∀ g ∈ C.gates, match g with | .div _ _ => False | _ => True) :
    ∃ prior : List (MvPolynomial (Fin n) P.Field), polynomialCircuitValues P C=some prior ∧
      ∀ j : Fin C.outputs.length, circuitPolynomials P C j=(prior[C.outputs[j]]?).getD 0 := by
  have hv:=polynomialCircuitValues_fraction P C hdf
  obtain ⟨values,hvalues,_⟩:=hvalid.2
  cases hp : polynomialCircuitValues P C with
  | none => rw [hp,Option.map_none,hvalues] at hv;cases hv
  | some prior =>
    refine ⟨prior,rfl,?_⟩
    have heq : circuitValues P C=some (prior.map (algebraMap _ (CircuitFunctionField P n))) := by
      simpa only [hp,Option.map_some] using hv
    exact circuitPolynomials_eq_of_polynomial_values P C prior heq

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
open MvPolynomial
namespace APSCounting893.Main
lemma coefficientMap_totalDegree_le {K L σ : Type} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (p : MvPolynomial σ K) :
    (MvPolynomial.map f p).totalDegree ≤ p.totalDegree := by
  classical
  exact Finset.sup_mono (MvPolynomial.support_map_subset f p)
end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace APSCounting893.Main

lemma divisionFree_circuitPolynomials_totalDegree_le {n : ℕ} (P : CoefficientPresentation)
    (C : ArithmeticCircuit n) (hvalid : ValidCircuit P C)
    (hdf : ∀ g ∈ C.gates, match g with | .div _ _ => False | _ => True)
    (j : Fin C.outputs.length) : (circuitPolynomials P C j).totalDegree≤outputFormalDegree C j := by
  obtain ⟨prior,hp,hchosen⟩:=polynomialCircuitValues_exists_of_valid_divisionFree P C hvalid hdf
  rw [hchosen j]
  have hh:=list_getD_le_of_forall₂ (polynomialCircuitValues_degrees P C prior hp) C.outputs[j]
  change _≤((formalDegrees C)[C.outputs[j]]?).getD 0
  cases ha : prior[C.outputs[j]]? <;>
    simpa only [List.getElem?_map,ha,Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,MvPolynomial.totalDegree_zero] using hh

lemma ReducedCircuit.output_degree_le (I : ReducedCircuit) (j : Fin (I.n+1)) :
    (I.rawMap.F j).totalDegree ≤ max 1 (outputFormalDegree I.C (Fin.cast I.outputCount.symm j)) := by
  have hh:=divisionFree_circuitPolynomials_totalDegree_le .rational I.C I.valid I.divisionFree (Fin.cast I.outputCount.symm j)
  have hm := (coefficientMap_totalDegree_le (algebraMap ℚ ℂ) (circuitPolynomials .rational I.C (Fin.cast I.outputCount.symm j))).trans hh
  change _ ≤ max 1 (outputFormalDegree I.C (Fin.cast I.outputCount.symm j))
  exact hm.trans (le_max_right _ _)

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace APSCounting893.Main

lemma outputFormalDegree_le_input_exponential {n : ℕ} (C : ArithmeticCircuit n)
    (j : Fin C.outputs.length) : outputFormalDegree C j ≤ 2 ^ C.encode.length := by
  exact (outputFormalDegree_le_exponential C j).trans
    (Nat.pow_le_pow_right (by omega) (circuit_gates_length_le_encode C))

lemma ReducedCircuit.degree_le_input_exponential (I : ReducedCircuit) :
    I.rawMap.d ≤ 2 ^ (I.C.encode.length+1) := by
  have hone : 1 ≤ 2^I.C.encode.length := Nat.one_le_pow _ _ (by omega)
  change max 2 (Finset.univ.sup (outputFormalDegree I.C)) ≤ _
  apply max_le
  · rw [pow_succ]; omega
  · apply (Finset.sup_le ?_).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
    intro j hj
    exact outputFormalDegree_le_input_exponential I.C j

lemma ReducedCircuit.output_degree_le_input_exponential (I : ReducedCircuit) (j : Fin (I.n+1)) :
    (I.rawMap.F j).totalDegree ≤ 2 ^ (I.C.encode.length+1) := by
  apply (I.output_degree_le j).trans
  apply max_le
  · exact Nat.one_le_pow _ _ (by omega)
  · exact (outputFormalDegree_le_input_exponential I.C _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))

lemma ReducedCircuit.dimension_le_input_length (I : ReducedCircuit) : I.n ≤ I.C.encode.length := by
  have := I.dimension_le_encode
  omega

lemma ReducedCircuit.homogenizingDegrees_pos (I : ReducedCircuit)
    (i : Fin (I.n + (I.n+1))) : 0 < I.homogenizingDegrees i := by
  unfold ReducedCircuit.homogenizingDegrees
  generalize Fin.cast (Nat.add_comm _ _) i = j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp
  · intro j
    simp

lemma ReducedCircuit.homogenizingDegrees_le (I : ReducedCircuit)
    (i : Fin (I.n + (I.n+1))) : I.homogenizingDegrees i ≤ I.rawMap.d := by
  unfold ReducedCircuit.homogenizingDegrees
  generalize Fin.cast (Nat.add_comm _ _) i = j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp only [Fin.addCases_left]
    change max 1 (outputFormalDegree I.C _) ≤ max 2 (Finset.univ.sup (outputFormalDegree I.C))
    exact max_le_max (by omega) (Finset.le_sup (f := outputFormalDegree I.C) (Finset.mem_univ _))
  · intro j
    simp only [Fin.addCases_right]
    change 1 ≤ max 2 _
    omega

end APSCounting893.Main
end Component_16

section Component_17
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma auxiliaryResultant_degree_bound {K : Type} [CommRing K] [Nontrivial K] {n : ℕ}
    (F : Fin (n+1) → MvPolynomial (Fin n) K) (c alpha : Fin n → K) (lambda : Fin (n+1) → K)
    (degrees : Fin (n+(n+1)) → ℕ) (D : ℕ) (hD : 2 ≤ D)
    (hpos : ∀ i,0 < degrees i) (hdeg : ∀ i,degrees i ≤ D) :
    (auxiliaryResultant F c alpha lambda degrees).totalDegree ≤ sourceDStar n D := by
  let N:=n+(n+1)
  let d : Fin (N+1) → ℕ := Fin.lastCases 2 degrees
  have hd : ∀ i,0 < d i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [d]
    · simpa only [d,Fin.lastCases_castSucc] using hpos j
  have hdb : ∀ i,d i ≤ D := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [d] using hD
    · simpa only [d,Fin.lastCases_castSucc] using hdeg j
  have hG : ∀ i,AuxiliaryCoefficientDegree
      (Fin.lastCases (auxiliaryHForm lambda) (auxiliaryPerturbedEquation F c alpha degrees) i) N := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using auxiliaryHForm_coefficient_degree lambda
    · simp only [Fin.lastCases_castSucc]
      exact (auxiliaryPerturbedEquation_coefficient_degree F c alpha degrees j).mono (by dsimp [N];omega)
  have hres := homogeneousResultant_auxiliary_degree d hd
    (Fin.lastCases (auxiliaryHForm lambda) (auxiliaryPerturbedEquation F c alpha degrees)) N hG
  have hprod (i : Fin (N+1)) : (∏ j ∈ Finset.univ.erase i,d j) ≤ D^N := by
    have hh := Finset.prod_le_prod' (s:=Finset.univ.erase i) (g:=fun _ => D) (fun j _ => hdb j)
    simpa using hh
  have hsum : (∑ i,∏ j ∈ Finset.univ.erase i,d j) ≤ (N+1)*D^N := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hprod i)
    simpa using hh
  unfold auxiliaryResultant
  change (homogeneousResultant d (Fin.lastCases (auxiliaryHForm lambda)
    (auxiliaryPerturbedEquation F c alpha degrees))).totalDegree ≤ _
  apply hres.trans
  calc
    N*(∑ i,∏ j ∈ Finset.univ.erase i,d j) ≤ N*((N+1)*D^N) := Nat.mul_le_mul_left N hsum
    _ ≤ (N+1)*(2*N+1)*D^N := by nlinarith [Nat.zero_le (D^N)]

lemma sampledResultant_degree_bound (I : ReducedCircuit) (theta : SampleTuple I) :
    (sampledResultant I theta).totalDegree ≤ sourceDStar I.n I.rawMap.d := by
  unfold sampledResultant
  rw [resultantFor_eq_auxiliary]
  apply auxiliaryResultant_degree_bound
  · change 2 ≤ max 2 _
    exact le_max_left _ _
  · exact I.homogenizingDegrees_pos
  · exact I.homogenizingDegrees_le

end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main

lemma sourceDStar_singly_exponential (I : ReducedCircuit) :
    sourceDStar I.n I.rawMap.d ≤ 2^polyBound 32 2 I.C.encode.length := by
  let L := I.C.encode.length
  let N := I.n+(I.n+1)
  have hn := I.dimension_le_input_length
  have hN : N ≤ 2*L+1 := by dsimp [N,L];omega
  have hd := I.degree_le_input_exponential
  have hf : N+1 ≤ 2^(N+1) := Nat.lt_two_pow_self.le
  have hg : 2*N+1 ≤ 2^(2*N+1) := Nat.lt_two_pow_self.le
  have hp : I.rawMap.d^N ≤ 2^((L+1)*N) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hd N
  have he : N+1+(2*N+1)+(L+1)*N ≤ 32*(L+1)^2 := by
    have hm := Nat.mul_le_mul_left (L+4) hN
    nlinarith
  change (N+1)*(2*N+1)*I.rawMap.d^N ≤ 2^(32*(L+1)^2)
  calc
    _ ≤ 2^(N+1)*2^(2*N+1)*2^((L+1)*N) := Nat.mul_le_mul (Nat.mul_le_mul hf hg) hp
    _ = 2^(N+1+(2*N+1)+(L+1)*N) := by rw [←pow_add,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

lemma sampledResultant_singly_exponential_degree (I : ReducedCircuit) (theta : SampleTuple I) :
    (sampledResultant I theta).totalDegree ≤ 2^polyBound 32 2 I.C.encode.length :=
  (sampledResultant_degree_bound I theta).trans (sourceDStar_singly_exponential I)

end APSCounting893.Main
end Component_18

open APSCounting893.Main
theorem solution
    (I : ReducedCircuit) (theta : SampleTuple I) :
    (sampledResultant I theta).totalDegree ≤ sourceDStar I.n I.rawMap.d ∧
      sourceDStar I.n I.rawMap.d ≤ 2 ^ polyBound 32 2 I.C.encode.length := by
  exact ⟨sampledResultant_degree_bound I theta,sourceDStar_singly_exponential I⟩
