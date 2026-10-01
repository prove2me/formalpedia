-- Prove2me | solution 1 for AlonMilman.Diameter.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:44:53.153896+00:00
-- url     : https://prove2.me/submissions/16087b95-7ec5-4891-9364-a4174c53b91a

import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_AlonMilman_Diameter_lambda1
import Mathlib.Tactic

open Matrix Finset WithLp
open scoped InnerProductSpace

namespace AlonProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable abbrev ev := (G.isHermitian_lapMatrix ℝ).eigenvalues₀
noncomputable abbrev basis :=
  (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis
    finrank_euclideanSpace

theorem ev_nonneg (i : Fin (Fintype.card V)) : 0 ≤ ev G i := by
  have h := (G.posSemidef_lapMatrix ℝ).eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card V) ≃ V) i)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

theorem eigen (i : Fin (Fintype.card V)) :
    G.lapMatrix ℝ *ᵥ ⇑(basis G i) = ev G i • ⇑(basis G i) := by
  have h := (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).apply_eigenvectorBasis
    finrank_euclideanSpace i
  exact congrArg (fun x : EuclideanSpace ℝ V => (x : V → ℝ)) h

theorem last_zero (hn : 2 ≤ Fintype.card V) :
    ev G ⟨Fintype.card V - 1, by omega⟩ = 0 := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hd := G.det_lapMatrix_eq_zero
  rw [(G.isHermitian_lapMatrix ℝ).det_eq_prod_eigenvalues] at hd
  obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hd
  apply le_antisymm _ (ev_nonneg G _)
  let i := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card V) ≃ V).symm v
  have hi : ev G i = 0 := hv
  rw [← hi]
  apply (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
  apply Fin.le_iff_val_le_val.mpr
  change i.val ≤ Fintype.card V - 1
  have := i.isLt
  omega

theorem constant_of_zero (hG : G.Connected) (i : Fin (Fintype.card V)) (hi : ev G i = 0)
    (u v : V) : basis G i u = basis G i v := by
  have h := eigen G i
  rw [hi,zero_smul] at h
  exact (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp h) u v (hG.preconnected u v)

theorem zero_unique (hG : G.Connected) (i j : Fin (Fintype.card V))
    (hi : ev G i = 0) (hj : ev G j = 0) : i = j := by
  by_contra hij
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.arbitrary V
  have hnormi := (basis G).inner_eq_one i
  have hnormj := (basis G).inner_eq_one j
  have horth := (basis G).inner_eq_zero hij
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct] at *
  have hi' : ∀ u, basis G i u = basis G i v := fun u => constant_of_zero G hG i hi u v
  have hj' : ∀ u, basis G j u = basis G j v := fun u => constant_of_zero G hG j hj u v
  simp_rw [hi',hj',sum_const,card_univ,nsmul_eq_mul] at hnormi hnormj horth
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (show Fintype.card V ≠ 0 by omega)
  have hvi : basis G i v ≠ 0 := by intro h; rw [h] at hnormi; simp at hnormi
  have hvj : basis G j v ≠ 0 := by intro h; rw [h] at hnormj; simp at hnormj
  exact (mul_ne_zero hn (mul_ne_zero hvj hvi)) horth

theorem gap_pos (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    0 < AlonMilman.Diameter.lambda1 G := by
  rw [AlonMilman.Diameter.lambda1, dif_pos hn]
  apply lt_of_le_of_ne (ev_nonneg G _) (Ne.symm _)
  intro h
  have hh := zero_unique G hG ⟨Fintype.card V - 2, by omega⟩
    ⟨Fintype.card V - 1, by omega⟩ h (last_zero G hn)
  have := congrArg Fin.val hh
  change Fintype.card V - 2 = Fintype.card V - 1 at this
  omega

theorem last_coeff_zero (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (f : V → ℝ) (hf : ∑ v, f v = 0) :
    (basis G).repr (toLp 2 f) ⟨Fintype.card V - 1, by omega⟩ = 0 := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.arbitrary V
  rw [OrthonormalBasis.repr_apply_apply,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  simp_rw [constant_of_zero G hG _ (last_zero G hn) _ v]
  rw [← Finset.sum_mul,hf,zero_mul]

theorem parseval (x y : EuclideanSpace ℝ V) :
    ∑ i, (basis G).repr x i * (basis G).repr y i =
      (x : V → ℝ) ⬝ᵥ (y : V → ℝ) := by
  have h := (basis G).repr.inner_map_map x y
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm] using h

theorem repr_mul (f : V → ℝ) (i : Fin (Fintype.card V)) :
    (basis G).repr (toLp 2 (G.lapMatrix ℝ *ᵥ f)) i =
      ev G i * (basis G).repr (toLp 2 f) i := by
  exact (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace (toLp 2 f) i

theorem rayleigh (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (f : V → ℝ) (hf : ∑ v, f v = 0) :
    AlonMilman.Diameter.lambda1 G * (f ⬝ᵥ f) ≤ f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) := by
  let c := (basis G).repr (toLp 2 f)
  have hc := last_coeff_zero G hG hn f hf
  change c ⟨Fintype.card V - 1, by omega⟩ = 0 at hc
  have hnrm := parseval G (toLp 2 f) (toLp 2 f)
  have hq := parseval G (toLp 2 f) (toLp 2 (G.lapMatrix ℝ *ᵥ f))
  simp only [repr_mul] at hq
  change ∑ i, c i * c i = f ⬝ᵥ f at hnrm
  change ∑ i, c i * (ev G i * c i) = f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) at hq
  rw [← hnrm, ← hq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases he : i = ⟨Fintype.card V - 1, by omega⟩
  · subst i
    rw [hc]
    simp
  · have hle : i ≤ (⟨Fintype.card V - 2, by omega⟩ : Fin (Fintype.card V)) := by
      apply Fin.le_iff_val_le_val.mpr
      change i.val ≤ Fintype.card V - 2
      have hiLt := i.isLt
      have hv : i.val ≠ Fintype.card V - 1 := fun h => he (Fin.ext h)
      omega
    have hge := (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone hle
    rw [AlonMilman.Diameter.lambda1, dif_pos hn]
    nlinarith [sq_nonneg (c i),mul_nonneg (sub_nonneg.mpr hge) (sq_nonneg (c i))]
end AlonProof

namespace AlonProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def setDist (A : Finset V) (hA : A.Nonempty) (v : V) : ℕ :=
  A.inf' hA (fun a => G.dist a v)

noncomputable def clipDist (A : Finset V) (hA : A.Nonempty) (ρ : ℕ) (v : V) : ℝ :=
  min (ρ : ℝ) (setDist G A hA v : ℝ)

theorem setDist_zero (A : Finset V) (hA : A.Nonempty) (v : V) (hv : v ∈ A) :
    setDist G A hA v = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (Finset.inf'_le (fun a => G.dist a v) hv).trans (by simp)

theorem setDist_le_add_one (hG : G.Connected) (A : Finset V) (hA : A.Nonempty)
    (u v : V) (huv : G.Adj u v) : setDist G A hA u ≤ setDist G A hA v + 1 := by
  obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_inf' hA (fun a => G.dist a v)
  have hle := Finset.inf'_le (fun a => G.dist a u) ha
  have hd : G.dist a u ≤ G.dist a v + G.dist v u := hG.dist_triangle
  rw [G.dist_eq_one_iff_adj.mpr huv.symm] at hd
  change setDist G A hA v = G.dist a v at he
  rw [he]
  exact hle.trans hd

theorem clip_zero (A : Finset V) (hA : A.Nonempty) (ρ : ℕ) (v : V) (hv : v ∈ A) :
    clipDist G A hA ρ v = 0 := by
  simp [clipDist,setDist_zero G A hA v hv]

theorem clip_eq (A B : Finset V) (hA : A.Nonempty) (ρ : ℕ)
    (hdist : ∀ u ∈ A, ∀ v ∈ B, ρ ≤ G.dist u v) (v : V) (hv : v ∈ B) :
    clipDist G A hA ρ v = ρ := by
  apply min_eq_left
  exact_mod_cast Finset.le_inf' hA (fun a => G.dist a v) (fun a ha => hdist a ha v hv)

theorem clip_lipschitz (hG : G.Connected) (A : Finset V) (hA : A.Nonempty) (ρ : ℕ)
    (u v : V) (huv : G.Adj u v) : |clipDist G A hA ρ u - clipDist G A hA ρ v| ≤ 1 := by
  have h1 : (setDist G A hA u : ℝ) ≤ setDist G A hA v + 1 := by
    exact_mod_cast setDist_le_add_one G hG A hA u v huv
  have h2 : (setDist G A hA v : ℝ) ≤ setDist G A hA u + 1 := by
    exact_mod_cast setDist_le_add_one G hG A hA v u huv.symm
  have ha : |(setDist G A hA u : ℝ) - setDist G A hA v| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  exact (abs_min_sub_min_le_max (ρ : ℝ) (setDist G A hA u : ℝ)
    (ρ : ℝ) (setDist G A hA v : ℝ)).trans (by simp [max_le_iff,ha])

theorem sets_disjoint (A B : Finset V) (ρ : ℕ) (hρ : 1 ≤ ρ)
    (hdist : ∀ u ∈ A, ∀ v ∈ B, ρ ≤ G.dist u v) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro v ha hb
  have h := hdist v ha v hb
  simp at h
  omega

theorem variance_bound (A B : Finset V) (hab : Disjoint A B)
    (g : V → ℝ) (r m : ℝ) (ha : ∀ u ∈ A, g u = 0) (hb : ∀ u ∈ B, g u = r) :
    (A.card : ℝ) * (B.card : ℝ) * r^2 ≤
      ((A.card : ℝ)+(B.card : ℝ)) * (∑ u, (g u-m)^2) := by
  have hh : (A.card : ℝ)*m^2 + (B.card : ℝ)*(r-m)^2 ≤ ∑ u, (g u-m)^2 := by
    calc
      _ = (∑ u ∈ A, (g u-m)^2) + ∑ u ∈ B, (g u-m)^2 := by
        have hea : (∑ u ∈ A, (g u-m)^2) = (A.card : ℝ)*m^2 := by
          calc
            _ = ∑ u ∈ A, m^2 := Finset.sum_congr rfl (fun u hu => by rw [ha u hu]; ring)
            _ = _ := by simp
        have heb : (∑ u ∈ B, (g u-m)^2) = (B.card : ℝ)*(r-m)^2 := by
          calc
            _ = ∑ u ∈ B, (r-m)^2 := Finset.sum_congr rfl (fun u hu => by rw [hb u hu])
            _ = _ := by simp
        rw [hea,heb]
      _ = ∑ u ∈ A ∪ B, (g u-m)^2 := (Finset.sum_union hab).symm
      _ ≤ ∑ u, (g u-m)^2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (by intros; positivity)
  have ha0 : 0 ≤ (A.card : ℝ) := by positivity
  have hb0 : 0 ≤ (B.card : ℝ) := by positivity
  nlinarith [sq_nonneg ((A.card : ℝ)*m-(B.card : ℝ)*(r-m)),
    mul_nonneg (add_nonneg ha0 hb0) (sub_nonneg.mpr hh)]

theorem centered_poincare (hG : G.Connected) (hn : 2 ≤ Fintype.card V) (g : V → ℝ) :
    AlonMilman.Diameter.lambda1 G *
      (∑ u, (g u - (∑ v, g v)/(Fintype.card V : ℝ))^2) ≤
      (∑ u, ∑ v, if G.Adj u v then (g u-g v)^2 else 0)/2 := by
  let m : ℝ := (∑ v, g v)/(Fintype.card V : ℝ)
  let f : V → ℝ := fun u => g u-m
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (show Fintype.card V ≠ 0 by omega)
  have hf : ∑ u, f u = 0 := by
    simp only [f,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,m,nsmul_eq_mul]
    field_simp [hn0]
    ring
  have hh := rayleigh G hG hn f hf
  have he : f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) =
      (∑ u, ∑ v, if G.Adj u v then (g u-g v)^2 else 0)/2 := by
    rw [← (G.lapMatrix ℝ).toLinearMap₂'_apply' f f, G.lapMatrix_toLinearMap₂' ℝ]
    simp [f]
  rw [he] at hh
  simpa only [dotProduct,f,pow_two] using hh
end AlonProof

namespace AlonProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem energy_le_core_degree (C : Finset V) (g : V → ℝ)
    (hconst : ∀ u v, G.Adj u v → u ∉ C → v ∉ C → g u = g v)
    (hlip : ∀ u v, G.Adj u v → |g u-g v| ≤ 1) :
    (∑ u, ∑ v, if G.Adj u v then (g u-g v)^2 else 0)/2 ≤
      (G.maxDegree : ℝ)*(C.card : ℝ) := by
  let c : V → ℝ := fun u => if u ∈ C then 1 else 0
  let a : V → V → ℝ := fun u v => if G.Adj u v then 1 else 0
  have ha : ∀ u v, (if G.Adj u v then (g u-g v)^2 else 0) ≤ a u v*(c u+c v) := by
    intro u v
    by_cases hadj : G.Adj u v
    · have hh := abs_le.mp (hlip u v hadj)
      have hs : (g u-g v)^2 ≤ 1 := by nlinarith
      by_cases hu : u ∈ C <;> by_cases hv : v ∈ C
      · simp only [hadj,a,c,hu,hv,if_pos,true_and] at *
        linarith
      · simpa [hadj,a,c,hu,hv] using hs
      · simpa [hadj,a,c,hu,hv] using hs
      · simp [hadj,a,c,hu,hv,hconst u v hadj hu hv]
    · simp [hadj,a]
  have hrow (u : V) : ∑ v, a u v*c u = if u ∈ C then (G.degree u : ℝ) else 0 := by
    by_cases hu : u ∈ C
    · simp [a,c,hu,← G.degree_eq_sum_if_adj]
    · simp [c,hu]
  have hcol (v : V) : ∑ u, a u v*c v = if v ∈ C then (G.degree v : ℝ) else 0 := by
    simpa only [a,G.adj_comm] using hrow v
  have hsum : ∑ u, ∑ v, a u v*(c u+c v) = 2*∑ u ∈ C, (G.degree u : ℝ) := by
    simp_rw [mul_add,Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun u v => a u v*c v)]
    simp_rw [hrow,hcol]
    simp [Finset.sum_ite_mem]
    ring
  have he : (∑ u, ∑ v, if G.Adj u v then (g u-g v)^2 else 0) ≤
      2*∑ u ∈ C, (G.degree u : ℝ) := by
    rw [← hsum]
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ha u v
  have hd : (∑ u ∈ C, (G.degree u : ℝ)) ≤ (G.maxDegree : ℝ)*(C.card : ℝ) := by
    calc
      _ ≤ ∑ u ∈ C, (G.maxDegree : ℝ) := Finset.sum_le_sum fun u _ => by exact_mod_cast G.degree_le_maxDegree u
      _ = _ := by simp [mul_comm]
  linarith

theorem clip_core_energy (hG : G.Connected) (A B : Finset V) (hA : A.Nonempty) (ρ : ℕ)
    (hρ : 1 < ρ) (hdist : ∀ u ∈ A, ∀ v ∈ B, ρ ≤ G.dist u v) :
    (∑ u, ∑ v, if G.Adj u v then (clipDist G A hA ρ u-clipDist G A hA ρ v)^2 else 0)/2 ≤
      (G.maxDegree : ℝ)*((Fintype.card V : ℝ)-(A.card : ℝ)-(B.card : ℝ)) := by
  have hab := sets_disjoint G A B ρ (by omega) hdist
  have hcard : ((A ∪ B)ᶜ.card : ℝ) = (Fintype.card V : ℝ)-(A.card : ℝ)-(B.card : ℝ) := by
    have h := Finset.card_compl_add_card (A ∪ B)
    rw [Finset.card_union_of_disjoint hab] at h
    have hh : (((A ∪ B)ᶜ.card : ℝ)+(A.card : ℝ)+(B.card : ℝ)) = Fintype.card V := by exact_mod_cast (show (A ∪ B)ᶜ.card + A.card + B.card = Fintype.card V by omega)
    linarith
  rw [← hcard]
  apply energy_le_core_degree
  · intro u v hadj hu hv
    have hu' : u ∈ A ∨ u ∈ B := by simpa only [Finset.mem_compl,not_not,Finset.mem_union] using hu
    have hv' : v ∈ A ∨ v ∈ B := by simpa only [Finset.mem_compl,not_not,Finset.mem_union] using hv
    rcases hu' with hu'|hu' <;> rcases hv' with hv'|hv'
    · rw [clip_zero G A hA ρ u hu',clip_zero G A hA ρ v hv']
    · have hh := hdist u hu' v hv'
      rw [G.dist_eq_one_iff_adj.mpr hadj] at hh
      omega
    · have hh := hdist v hv' u hu'
      rw [G.dist_eq_one_iff_adj.mpr hadj.symm] at hh
      omega
    · rw [clip_eq G A B hA ρ hdist u hu',clip_eq G A B hA ρ hdist v hv']
  · exact clip_lipschitz G hG A hA ρ
end AlonProof

namespace AlonProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem max_degree_pos (hG : G.Connected) (hn : 2 ≤ Fintype.card V) : 0 < (G.maxDegree : ℝ) := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hm := hG.preconnected.minDegree_pos_of_nontrivial
  exact_mod_cast hm.trans_le G.minDegree_le_maxDegree

theorem distance_set_bound (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (A B : Finset V) (ρ : ℕ) (hρ : 1 < ρ)
    (hdist : ∀ u ∈ A, ∀ v ∈ B, ρ ≤ G.dist u v) :
    (B.card : ℝ)/Fintype.card V ≤ (1-(A.card : ℝ)/Fintype.card V)/
      (1+(AlonMilman.Diameter.lambda1 G/(G.maxDegree : ℝ))*((A.card : ℝ)/Fintype.card V)*(ρ : ℝ)^2) := by
  have hnpos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hdpos := max_degree_pos G hG hn
  have hlpos := gap_pos G hG hn
  have ha0 : 0 ≤ (A.card : ℝ) := by positivity
  have hb0 : 0 ≤ (B.card : ℝ) := by positivity
  have hab := sets_disjoint G A B ρ (by omega) hdist
  have hsum : (A.card : ℝ)+(B.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast ((Finset.card_union_of_disjoint hab).symm.trans_le (Finset.card_le_univ (A ∪ B)))
  have hden : 0 < 1+(AlonMilman.Diameter.lambda1 G/(G.maxDegree : ℝ))*
      ((A.card : ℝ)/Fintype.card V)*(ρ : ℝ)^2 := by positivity
  by_cases hA : A.Nonempty
  · let g := clipDist G A hA ρ
    let m : ℝ := (∑ v, g v)/(Fintype.card V : ℝ)
    let Z : ℝ := ∑ u, (g u-m)^2
    have hvar : (A.card : ℝ)*(B.card : ℝ)*(ρ : ℝ)^2 ≤ ((A.card : ℝ)+(B.card : ℝ))*Z :=
      variance_bound A B hab g (ρ : ℝ) m (clip_zero G A hA ρ) (clip_eq G A B hA ρ hdist)
    have hp : AlonMilman.Diameter.lambda1 G*Z ≤ (G.maxDegree : ℝ)*
        ((Fintype.card V : ℝ)-(A.card : ℝ)-(B.card : ℝ)) :=
      (centered_poincare G hG hn g).trans (clip_core_energy G hG A B hA ρ hρ hdist)
    have hc0 : 0 ≤ ((Fintype.card V : ℝ)-(A.card : ℝ)-(B.card : ℝ)) := by linarith
    have hmain : AlonMilman.Diameter.lambda1 G*(A.card : ℝ)*(B.card : ℝ)*(ρ : ℝ)^2 ≤
        (Fintype.card V : ℝ)*(G.maxDegree : ℝ)*
          ((Fintype.card V : ℝ)-(A.card : ℝ)-(B.card : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hvar hlpos.le
      have h2 := mul_le_mul_of_nonneg_left hp (add_nonneg ha0 hb0)
      have h3 := mul_le_mul_of_nonneg_right hsum (mul_nonneg hdpos.le hc0)
      nlinarith
    rw [div_le_div_iff₀ hnpos hden]
    apply (mul_le_mul_iff_right₀ (mul_pos hdpos hnpos)).mp
    field_simp [ne_of_gt hnpos,ne_of_gt hdpos]
    nlinarith
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simpa [hAe] using (div_le_one hnpos).mpr (show (B.card : ℝ) ≤ Fintype.card V by exact_mod_cast Finset.card_le_univ B)
end AlonProof

open AlonMilman.Diameter

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (A B : Finset V) (ρ : ℕ) (hρ : 1 < ρ)
    (hdist : ∀ u ∈ A, ∀ v ∈ B, ρ ≤ G.dist u v) :
    (B.card : ℝ) / Fintype.card V ≤
      (1 - (A.card : ℝ) / Fintype.card V) /
        (1 + (lambda1 G / (G.maxDegree : ℝ)) * ((A.card : ℝ) / Fintype.card V) * (ρ : ℝ) ^ 2) := by
  exact AlonProof.distance_set_bound G hG hn A B ρ hρ hdist


