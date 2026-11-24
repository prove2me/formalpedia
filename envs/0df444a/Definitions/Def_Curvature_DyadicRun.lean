-- Prove2me | Definitions.Def_Curvature_DyadicRun
-- name    : Curvature_DyadicRun
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:13:16.511996+00:00
-- url     : https://prove2.me/theorems/b94cdfda-80aa-4ff4-8975-0d852efbbb67
-- title:
--   Admissible descriptions, representation cost and the dyadic coordinate initialization
-- statement:
--   This file defines the coordinate data that Algorithm 4 uses on a general domain and the dyadic initialization built from these data. An **admissible description** $\mathcal D$ of a set $\mathcal K\subset\mathbb R^d$ consists of an integer $N\ge1$, a center $w_\circ\in\mathbb R^d$, a matrix $A\in\mathbb R^{d\times N}$, lengths $\ell\in(0,\infty)^N$ with $\lVert Ae_j\rVert_2\le\ell_j$ for every column, and integers $J_j\ge0$ that fix the thresholds $h_j\coloneqq2^{-J_j}$, such that every $u\in\mathcal K$ can be written as $u=w_\circ+Av$ with $v\in[-1,1]^N$. For each $u\in\mathcal K$, the file chooses such a $v$ that minimizes the coefficient cost $\Phi_{\ell,h}(v)$; a minimizer exists by compactness. As in Appendix A.1 of the paper, the **representation cost** of the description is
--
--   $$
--   C_{\mathcal D}(\mathcal K)\coloneqq\sup_{u\in\mathcal K}\ \min\bigl\{\Phi_{\ell,h}(v):v\in[-1,1]^N,\ w_\circ+Av=u\bigr\}.
--   $$
--
--   Fix $\varepsilon\in(0,1]$. The dyadic initialization in $\mathbb R^N$ uses the diagonal matrix $B=\operatorname{diag}(16\ell_1/\varepsilon,\ldots,16\ell_N/\varepsilon)$ and, for each coordinate $j$ and level $k=0,\ldots,J_j-1$, an initial quadratic regularization term with direction $e_j$, value $0$, threshold $2^kh_j$ and coefficient $16\ell_j/(\varepsilon\,2^kh_j)$. The creation threshold in round $t$ is $\bigl(\sum_j\ell_jh_j\bigr)/(t+1)^4$. The representation cost is the factor through which the domain enters the guarantee of Algorithm 4 with this initialization (Appendices B.1, B.5 and B.6).
-- source:
--   arXiv:2611.27572v1, Appendix A.1, p. 23; Appendices B.1 and B.6, pp. 33–34 and 39–40. https://arxiv.org/html/2611.27572v1#A2.SS1

import Definitions.Def_Curvature_GeneralRun
import Definitions.Def_Curvature_InitialCoordinates
import Definitions.Def_Curvature_WeightedTrace
import Mathlib.Topology.Order.Compact

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {N : ℕ}

abbrev DyadicLevel (J : Fin N → ℕ) := (j : Fin N) × Fin (J j)

def dyadicFloor (J : Fin N → ℕ) (j : Fin N) : ℝ := ((2 : ℝ) ^ J j)⁻¹

theorem dyadicFloor_pos (J : Fin N → ℕ) (j : Fin N) : 0 < dyadicFloor J j := by
  unfold dyadicFloor
  positivity

def dyadicBase (ε : ℝ) (ℓ : Vec N) : Mat N :=
  Matrix.diagonal (fun j => 16 / ε * ℓ j)

def dyadicTerm (ε : ℝ) (ℓ : Vec N) (J : Fin N → ℕ) (i : DyadicLevel J) : Term N :=
  let h := 2 ^ i.2.val * dyadicFloor J i.1
  ⟨0, Pi.single i.1 1, 0, 16 / ε * ℓ i.1 / h, h⟩

def dyadicTerms (ε : ℝ) (ℓ : Vec N) (J : Fin N → ℕ) : List (Term N) :=
  (Finset.univ : Finset (DyadicLevel J)).toList.map (dyadicTerm ε ℓ J)

theorem dyadicTerm_injective (ε : ℝ) (ℓ : Vec N) (J : Fin N → ℕ) :
    Function.Injective (dyadicTerm ε ℓ J) := by
  rintro ⟨j,k⟩ ⟨j',k'⟩ heq
  have hq := congrArg (fun a : Term N => a.q j) heq
  have hj : j = j' := by
    by_contra hne
    simp [dyadicTerm, hne] at hq
  subst j'
  have hh := congrArg Term.h heq
  have hp : (2:ℝ)^k.val = 2^k'.val :=
    mul_right_cancel₀ (dyadicFloor_pos J j).ne' hh
  have hk : k = k' := Fin.ext ((pow_right_strictMono₀ (by norm_num : (1:ℝ)<2)).injective hp)
  subst k'
  rfl


theorem dyadicTerms_valid {ε : ℝ} (hε : 0 < ε) {ℓ : Vec N} (hℓ : ∀ j, 0 < ℓ j)
    (J : Fin N → ℕ) : GeneralInitialTerms (dyadicTerms ε ℓ J) := by
  constructor <;> intro a ha <;> obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  · rfl
  · rfl
  · exact (div_pos (mul_pos (by positivity) (hℓ i.1)) (mul_pos (by positivity)
      (dyadicFloor_pos J i.1))).le
  · exact mul_pos (by positivity) (dyadicFloor_pos J i.1)

theorem dyadicBase_posDef {ε : ℝ} (hε : 0 < ε) {ℓ : Vec N} (hℓ : ∀ j, 0 < ℓ j) :
    (dyadicBase ε ℓ).PosDef :=
  Matrix.PosDef.diagonal (fun j => mul_pos (by positivity) (hℓ j))

theorem dyadicTerm_signed (ε : ℝ) (ℓ : Vec N) (J : Fin N → ℕ) (i : DyadicLevel J)
    (v z : Vec N) :
    let a := dyadicTerm ε ℓ J i
    2 * (a.value v - a.divergence v z) =
      (16/ε * ℓ i.1) * ((2*z i.1*v i.1-(z i.1)^2) / (2^i.2.val * dyadicFloor J i.1)) := by
  simp [Term.value, Term.divergence, Term.residual, dyadicTerm, single_dotProduct]
  ring

theorem dyadicBase_quadratic (ε : ℝ) (ℓ v : Vec N) :
    dotProduct v ((dyadicBase ε ℓ).mulVec v) = ∑ j, (16/ε * ℓ j) * v j ^ 2 := by
  simp [dyadicBase, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dyadicTerm_curvature (ε : ℝ) (ℓ : Vec N) (J : Fin N → ℕ) (i : DyadicLevel J) :
    (dyadicTerm ε ℓ J i).curvature = Matrix.diagonal (Pi.single i.1 (dyadicTerm ε ℓ J i).γ) := by
  ext j k
  by_cases hj : j = i.1 <;> by_cases hk : k = i.1 <;> by_cases hjk : j = k <;>
    simp_all [Term.curvature, dyadicTerm]

theorem dyadicSurvivorMatrix (ε : ℝ) (ℓ : Vec N) (J : Fin N → ℕ)
    (revoked : Fin N → ℕ → Bool) :
    dyadicBase ε ℓ + (∑ i : DyadicLevel J,
      if revoked i.1 i.2.val then 0 else (dyadicTerm ε ℓ J i).curvature) =
      survivingDiagonal (16/ε) ℓ (dyadicFloor J) J revoked := by
  classical
  rw [Fintype.sum_sigma]
  ext j k
  simp only [Matrix.add_apply, Matrix.sum_apply, dyadicTerm_curvature]
  by_cases hjk : j = k
  · subst k
    simp only [dyadicBase, survivingDiagonal, Matrix.diagonal_apply_eq]
    have hsum (i : Fin N) :
        (∑ t : Fin (J i), (if revoked i t.val then (0 : Mat N) else
          Matrix.diagonal (Pi.single i (dyadicTerm ε ℓ J ⟨i,t⟩).γ)) j j) =
        if i = j then (16/ε*ℓ i) * (activeScaleWeight (J i) (dyadicFloor J i) (revoked i) - 1) else 0 := by
      by_cases heq : i = j
      · subst i
        rw [if_pos rfl, activeScaleWeight]
        rw [add_sub_cancel_left, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro t _
        cases revoked j t.val <;> simp [dyadicTerm, div_eq_mul_inv]
      · simp only [if_neg heq]
        apply Finset.sum_eq_zero
        intro t _
        split <;> simp [Ne.symm heq]
    simp_rw [hsum]
    simp
    ring
  · simp only [dyadicBase, survivingDiagonal, Matrix.diagonal_apply_ne _ hjk]
    simp only [zero_add]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro t _
    split <;> simp [Matrix.diagonal_apply_ne _ hjk]

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {N : ℕ}

/-- Initial regularization, the weighted trace and the total budget for skipped additions. -/
theorem dyadicCostBound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1) {ℓ : Vec N} (hℓ : ∀ j, 0 < ℓ j)
    (J : Fin N → ℕ) (v : Vec N) (hv : ∀ j, |v j| ≤ 1)
    (x : Fin N → ℕ → ℝ) (revoked : Fin N → ℕ → Bool)
    (hend : ∀ j k, k < J j → |x j k| ≤ 3*(2^k*dyadicFloor J j))
    (hit : ∀ j k, k < J j → revoked j k = true → 2^k*dyadicFloor J j ≤ |x j k|)
    (cov : Mat N) (hdiag : ∀ j, cov j j ≤ ℓ j ^ 2) :
    let τ := ε ^ 2 / 48
    let c := (1 + τ) * (2 + τ) / τ
    dotProduct v ((dyadicBase ε ℓ).mulVec v) +
      (∑ i : DyadicLevel J, (16/ε * ℓ i.1) *
        ((2*x i.1 i.2.val*v i.1 - (x i.1 i.2.val)^2) / (2^i.2.val*dyadicFloor J i.1))) +
      c * (cov * (survivingDiagonal (16/ε) ℓ (dyadicFloor J) J revoked)⁻¹).trace +
      (∑ j, ℓ j * dyadicFloor J j) / 8 ≤
      192 / ε * coefficientCost ℓ (dyadicFloor J) v := by
  let scale := 16/ε
  let τ := ε^2/48
  let c := (1+τ)*(2+τ)/τ
  let β := c/scale^2
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hβ : β ≤ 25/64 := by
    apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
    exact (weightedTraceCoefficient_le hε hε').trans_eq (by dsimp [scale]; field_simp; ring)
  have hβ₀ : 0 ≤ β := div_nonneg hc (sq_nonneg _)
  let h := dyadicFloor J
  let w := fun j => activeScaleWeight (J j) (h j) (revoked j)
  let raw := fun j => ∑ k ∈ Finset.range (J j), (2 * x j k * v j - (x j k)^2) / (2^k * h j)
  let cost := fun j => h j + |v j| * (1 + Real.log (max 1 (|v j| / h j)))
  have hsum : (∑ j, ((scale*ℓ j)*(v j)^2 + (scale*ℓ j)*raw j +
      c * (ℓ j / scale * (w j)⁻¹) + (ℓ j*h j)/8)) ≤
      ∑ j, (192 / ε) * (ℓ j*cost j) := by
    apply Finset.sum_le_sum
    intro j _
    have hf : 1 ≤ 2 ^ J j * h j := by simp [h, dyadicFloor]
    have hj := initialCoordinateCost_le (J j) (h j) (v j) ε β (dyadicFloor_pos J j) hf
      (hv j) hε' hβ₀ hβ (x j) (revoked j) (hend j) (hit j)
    have hscaled := mul_le_mul_of_nonneg_left hj (mul_pos hs (hℓ j)).le
    change (scale*ℓ j) * ((v j)^2 + raw j + β*(w j)⁻¹ + ε/128*h j) ≤
      (scale*ℓ j)*(12*cost j) at hscaled
    calc
      _ = (scale*ℓ j) * ((v j)^2 + raw j + β*(w j)⁻¹ + ε/128*h j) := by
        dsimp only [β, scale]
        field_simp [hε.ne']; ring
      _ ≤ (scale*ℓ j)*(12*cost j) := hscaled
      _ = _ := by dsimp only [scale]; ring
  have ht := mul_le_mul_of_nonneg_left
    (trace_survivingDiagonal_le cov scale hs ℓ h hℓ (dyadicFloor_pos J) J revoked hdiag) hc
  have hraw : (∑ i : DyadicLevel J, (scale * ℓ i.1) *
      ((2*x i.1 i.2.val*v i.1-(x i.1 i.2.val)^2)/(2^i.2.val*h i.1))) =
      ∑ j, (scale*ℓ j)*raw j := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [raw]
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  dsimp only
  rw [dyadicBase_quadratic, hraw]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  change _ ≤ 192 / ε * (∑ j, ℓ j * cost j)
  change c * _ ≤ c * (∑ j, ℓ j / scale * (w j)⁻¹) at ht
  dsimp only [scale, h, c, τ, w] at ht hsum
  linarith only [ht, hsum]

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {d : ℕ}

structure AdmissibleDescription (K : Set (Vec d)) where
  N : ℕ
  dimension_pos : 0 < N
  center : Vec d
  A : Matrix (Fin d) (Fin N) ℝ
  ℓ : Vec N
  J : Fin N → ℕ
  positive : ∀ j, 0 < ℓ j
  columns : ∀ j, norm₂ (fun i => A i j) ≤ ℓ j
  covers : ∀ u ∈ K, ∃ v : Vec N, (∀ j, |v j| ≤ 1) ∧ center + A.mulVec v = u

theorem coefficientCost_continuous {N : ℕ} (ℓ h : Vec N) :
    Continuous (coefficientCost ℓ h) := by
  unfold coefficientCost
  apply continuous_finsetSum
  intro j _
  apply continuous_const.mul
  apply continuous_const.add
  apply (continuous_apply j).abs.mul
  apply continuous_const.add
  apply Continuous.log
  · fun_prop
  · intro v
    exact (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'

namespace AdmissibleDescription
variable {K : Set (Vec d)} (D : AdmissibleDescription K)

def fiber (u : Vec d) : Set (Vec D.N) :=
  Set.Icc (fun _ => -1) (fun _ => 1) ∩ {v | D.center + D.A.mulVec v = u}

theorem fiber_nonempty (u : K) : (D.fiber u).Nonempty := by
  obtain ⟨v,hv,heq⟩ := D.covers u u.2
  exact ⟨v, ⟨fun j => (abs_le.mp (hv j)).1, fun j => (abs_le.mp (hv j)).2⟩, heq⟩

theorem fiber_compact (u : Vec d) : IsCompact (D.fiber u) := by
  apply isCompact_Icc.inter_right
  apply isClosed_eq _ continuous_const
  apply continuous_const.add
  unfold Matrix.mulVec dotProduct
  exact continuous_pi fun i => by fun_prop

private theorem exists_minimum (u : K) :
    ∃ v ∈ D.fiber u, IsMinOn (coefficientCost D.ℓ (dyadicFloor D.J)) (D.fiber u) v :=
  (D.fiber_compact u).exists_isMinOn (D.fiber_nonempty u)
    (coefficientCost_continuous _ _).continuousOn

def minimizingCoefficients (u : K) : Vec D.N := (D.exists_minimum u).choose

theorem minimizingCoefficients_spec (u : K) :
    (∀ j, |D.minimizingCoefficients u j| ≤ 1) ∧
    D.center + D.A.mulVec (D.minimizingCoefficients u) = u ∧
    ∀ v ∈ D.fiber u, coefficientCost D.ℓ (dyadicFloor D.J) (D.minimizingCoefficients u) ≤
      coefficientCost D.ℓ (dyadicFloor D.J) v := by
  obtain ⟨⟨hc, hr⟩, hmin⟩ := (D.exists_minimum u).choose_spec
  exact ⟨fun j => abs_le.mpr ⟨hc.1 j, hc.2 j⟩, hr, fun _ hv => hmin hv⟩

def representationCost : ℝ :=
  ⨆ u : K, coefficientCost D.ℓ (dyadicFloor D.J) (D.minimizingCoefficients u)

theorem minimum_le_representationCost (u : K) :
    coefficientCost D.ℓ (dyadicFloor D.J) (D.minimizingCoefficients u) ≤ D.representationCost := by
  apply le_ciSup _ u
  have cube := (isCompact_Icc (a := (fun _ : Fin D.N => (-1 : ℝ))) (b := fun _ => 1))
  have hb := (cube.image (coefficientCost_continuous D.ℓ (dyadicFloor D.J))).bddAbove
  apply hb.mono
  rintro _ ⟨y,rfl⟩
  exact ⟨_, (D.exists_minimum y).choose_spec.1.1, rfl⟩

end AdmissibleDescription
end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d N : ℕ}

private theorem endpointPayloads {ι α β : Type*} [Fintype ι] (label : ι → α)
    (hinj : Function.Injective label) (entries : List (α × β))
    (hentries : (entries.map Prod.fst).Perm (Finset.univ.toList.map label)) :
    ∃ payload : ι → β, (∀ i, (label i, payload i) ∈ entries) ∧
      entries.Perm (Finset.univ.toList.map fun i => (label i, payload i)) := by
  classical
  have hexists (i : ι) : ∃ b, (label i, b) ∈ entries := by
    have hlabel : label i ∈ entries.map Prod.fst := hentries.mem_iff.mpr
      (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩)
    obtain ⟨⟨a, b⟩, hb, ha⟩ := List.mem_map.mp hlabel
    exact ⟨b, ha ▸ hb⟩
  let payload (i : ι) := Classical.choose (hexists i)
  have hp (i : ι) : (label i, payload i) ∈ entries := Classical.choose_spec (hexists i)
  refine ⟨payload, hp, ?_⟩
  have hkeys : (entries.map Prod.fst).Nodup :=
    hentries.nodup_iff.mpr (Finset.nodup_toList _ |>.map hinj)
  have hinj' : Function.Injective (fun i => (label i, payload i)) :=
    fun _ _ h => hinj (congrArg Prod.fst h)
  apply List.perm_of_nodup_nodup_toFinset_eq (hkeys.of_map Prod.fst)
    (Finset.nodup_toList _ |>.map hinj')
  ext e
  simp only [List.mem_toFinset]
  constructor
  · intro he
    have hlabel : e.1 ∈ Finset.univ.toList.map label :=
      hentries.mem_iff.mp (List.mem_map_of_mem (f := Prod.fst) he)
    obtain ⟨i, hi, hlabel⟩ := List.mem_map.mp hlabel
    have heq : (label i, payload i) = e :=
      List.inj_on_of_nodup_map hkeys (hp i) he hlabel
    exact List.mem_map.mpr ⟨i, hi, heq⟩
  · intro he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    exact hp i

def dyadicSkip (ℓ : Vec N) (J : Fin N → ℕ) (t : ℕ) : ℝ :=
  (∑ j, ℓ j * dyadicFloor J j) / ((t : ℝ) + 2) ^ 4

theorem dyadicSkip_nonneg {ℓ : Vec N} (hℓ : ∀ j, 0 < ℓ j) (J : Fin N → ℕ) (t : ℕ) :
    0 ≤ dyadicSkip ℓ J t := by
  unfold dyadicSkip
  exact div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hℓ j).le (dyadicFloor_pos J j).le)
    (by positivity)

private theorem dyadicTerm_residual (ε : ℝ) (ℓ : Vec N) (J : Fin N → ℕ)
    (i : DyadicLevel J) (z : Vec N) :
    (dyadicTerm ε ℓ J i).residual z = z i.1 := by
  simp [Term.residual, dyadicTerm, single_dotProduct]

private theorem dyadicInitialEndpoints {ε : ℝ} {ℓ : Vec N} {J : Fin N → ℕ}
    {ζ : ℕ → ℝ} {s : ℕ → BallState N} {q : ℕ → Vec N} {T : ℕ}
    {removed : List (Term N × Vec N)}
    (hist : GeneralRunHistory (dyadicTerms ε ℓ J) ε ζ s q T removed)
    (hI : GeneralInitialTerms (dyadicTerms ε ℓ J)) :
    ∃ location : DyadicLevel J → Vec N, ∃ revoked : Fin N → ℕ → Bool,
      (∀ i : DyadicLevel J, |location i i.1| ≤ 3 * (2 ^ i.2.val * dyadicFloor J i.1)) ∧
      (∀ i : DyadicLevel J, revoked i.1 i.2.val = true →
        2 ^ i.2.val * dyadicFloor J i.1 ≤ |location i i.1|) ∧
      (dyadicBase ε ℓ + ((generalInitialSurvivors (s T).active).map Term.curvature).sum =
        survivingDiagonal (16/ε) ℓ (dyadicFloor J) J revoked) ∧
      (∀ f : Term N → Vec N → ℝ,
        ((generalInitialRemoved removed).map fun e => f e.1 e.2).sum +
          ((generalInitialSurvivors (s T).active).map fun a => f a (s T).z).sum =
        ∑ i : DyadicLevel J, f (dyadicTerm ε ℓ J i) (location i)) := by
  classical
  let entries : List (Term N × (Vec N × Bool)) :=
    ((generalInitialRemoved removed).map fun e => (e.1, e.2, true)) ++
      ((generalInitialSurvivors (s T).active).map fun a => (a, (s T).z, false))
  have hentries : (entries.map Prod.fst).Perm
      (Finset.univ.toList.map (dyadicTerm ε ℓ J)) := by
    simpa [entries, dyadicTerms, List.map_map, Function.comp_def] using hist.initialPartition hI
  obtain ⟨payload, hp, hperm⟩ :=
    endpointPayloads (dyadicTerm ε ℓ J) (dyadicTerm_injective ε ℓ J) entries hentries
  let revoked : Fin N → ℕ → Bool := fun j k =>
    if h : k < J j then (payload ⟨j, ⟨k, h⟩⟩).2 else false
  have hrevoked (i : DyadicLevel J) : revoked i.1 i.2.val = (payload i).2 := by
    obtain ⟨j, k⟩ := i
    simp [revoked, k.isLt]
  have hendpoint (i : DyadicLevel J) :
      ((dyadicTerm ε ℓ J i, (payload i).1) ∈ generalInitialRemoved removed ∧ (payload i).2 = true) ∨
      (dyadicTerm ε ℓ J i ∈ generalInitialSurvivors (s T).active ∧
        (payload i).1 = (s T).z ∧ (payload i).2 = false) := by
    have hm := List.mem_append.mp (show (dyadicTerm ε ℓ J i, payload i) ∈ entries from hp i)
    rcases hm with hm | hm
    · obtain ⟨⟨a, z⟩, ha, he⟩ := List.mem_map.mp hm
      have hparts : a = dyadicTerm ε ℓ J i ∧ z = (payload i).1 ∧ true = (payload i).2 :=
        Prod.mk.inj he |>.imp id (fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)
      obtain ⟨rfl, rfl, hf⟩ := hparts
      exact Or.inl ⟨ha, hf.symm⟩
    · obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
      have hterm : a = dyadicTerm ε ℓ J i := congrArg Prod.fst he
      exact Or.inr ⟨hterm ▸ ha,
        (congrArg (fun e => e.2.1) he).symm, (congrArg (fun e => e.2.2) he).symm⟩
  have hsum {R : Type} [AddCommMonoid R] (f : Term N × (Vec N × Bool) → R) :
      (entries.map f).sum = ∑ i : DyadicLevel J, f (dyadicTerm ε ℓ J i, payload i) := by
    rw [(hperm.map f).sum_eq, List.map_map]
    have htotal := List.sum_toFinset (fun i : DyadicLevel J => f (dyadicTerm ε ℓ J i, payload i))
      (Finset.nodup_toList Finset.univ)
    simp only [Finset.toList_toFinset] at htotal
    exact htotal.symm
  refine ⟨fun i => (payload i).1, revoked, ?_, ?_, ?_, ?_⟩
  · intro i
    change |(payload i).1 i.1| ≤ _
    rcases hendpoint i with ⟨hm, _⟩ | ⟨hm, hz, _⟩
    · have hu := (hist.thresholds _ _ (List.mem_filter.mp hm).1).2
      rw [dyadicTerm_residual] at hu
      exact hu.le
    · have hu := hist.interior _ (List.mem_filter.mp hm).1
      rw [dyadicTerm_residual] at hu
      rw [hz]
      exact hu.le.trans (by
        change 2 ^ i.2.val * dyadicFloor J i.1 ≤ 3 * (2 ^ i.2.val * dyadicFloor J i.1)
        have hh : 0 < 2 ^ i.2.val * dyadicFloor J i.1 :=
          mul_pos (by positivity) (dyadicFloor_pos J i.1)
        linarith)
  · intro i hr
    rcases hendpoint i with ⟨hm, _⟩ | ⟨_, _, hf⟩
    · have hl := (hist.thresholds _ _ (List.mem_filter.mp hm).1).1
      rwa [dyadicTerm_residual] at hl
    · rw [hrevoked, hf] at hr
      contradiction
  · have hmatrix := hsum (fun e => if e.2.2 then (0 : Mat N) else e.1.curvature)
    have hcurv : (List.map Term.curvature (generalInitialSurvivors (s T).active)).sum =
        ∑ i : DyadicLevel J, if revoked i.1 i.2.val then 0 else (dyadicTerm ε ℓ J i).curvature := by
      simpa [entries, List.map_map, Function.comp_def, hrevoked] using hmatrix
    rw [hcurv, dyadicSurvivorMatrix]
  · intro f
    simpa [entries, List.map_map, Function.comp_def] using
      hsum (fun e => f e.1 e.2.1)

/-- The internal bound for the dyadic initialization and every unit-bounded ambient input rule. -/
theorem generalInternalBound (A : Matrix (Fin d) (Fin N) ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1) {ℓ : Vec N} (hℓ : ∀ j, 0 < ℓ j) (J : Fin N → ℕ)
    (hcolumn : ∀ j, norm₂ (fun i => A i j) ≤ ℓ j)
    (ambient : ℕ → Vec N → Vec d) (hnorm : ∀ t z, norm₂ (ambient t z) ≤ 1)
    (T : ℕ) (v : Vec N) (hv : ∀ j, |v j| ≤ 1) :
    let B := dyadicBase ε ℓ
    let feed := fun t z => A.transpose.mulVec (ambient t z)
    let s := generalStateAfter (generalInitial B (dyadicTerms ε ℓ J)) ε (dyadicSkip ℓ J) feed
    let r := fun t => excess (feed t (s t).z) (s t).z v
    let displacement := v - (s T).z
    2 * (∑ t ∈ Finset.range T, r t) - ε * (∑ t ∈ Finset.range T, |r t|) +
      dotProduct displacement (B.mulVec displacement) ≤
      192 / ε * coefficientCost ℓ (dyadicFloor J) v := by
  let B := dyadicBase ε ℓ
  let I := dyadicTerms ε ℓ J
  let ζ := dyadicSkip ℓ J
  let feed := fun t z => A.transpose.mulVec (ambient t z)
  let s := generalStateAfter (generalInitial B I) ε ζ feed
  let q := fun t => feed t (s t).z
  let L := ∑ j, ℓ j * dyadicFloor J j
  have hL : 0 ≤ L := Finset.sum_nonneg fun j _ => mul_nonneg (hℓ j).le (dyadicFloor_pos J j).le
  have hB := dyadicBase_posDef hε hℓ
  have hI := dyadicTerms_valid hε hℓ J
  have hζ := dyadicSkip_nonneg hℓ J
  obtain ⟨removed, hist⟩ := generalStateAfter_history (feed := feed) hB hI hε hζ T
  obtain ⟨location, revoked, hlocation, hhit, hmatrix, hsum⟩ := dyadicInitialEndpoints hist hI
  let x (j : Fin N) (k : ℕ) : ℝ :=
    if hk : k < J j then location ⟨j, ⟨k, hk⟩⟩ j else 0
  have hx (i : DyadicLevel J) : x i.1 i.2.val = location i i.1 := by
    obtain ⟨j, k⟩ := i
    simp [x, k.isLt]
  have hend (j : Fin N) (k : ℕ) (hk : k < J j) : |x j k| ≤ 3 * (2 ^ k * dyadicFloor J j) := by
    simpa only [x, dif_pos hk] using hlocation ⟨j, ⟨k, hk⟩⟩
  have hit (j : Fin N) (k : ℕ) (hk : k < J j) (hr : revoked j k = true) :
      2 ^ k * dyadicFloor J j ≤ |x j k| := by
    simpa only [x, dif_pos hk] using hhit ⟨j, ⟨k, hk⟩⟩ hr
  have hdiag (j : Fin N) : (A.transpose * A) j j ≤ ℓ j ^ 2 := by
    have hc := pow_le_pow_left₀ (norm₂_nonneg (fun i => A i j)) (hcolumn j) 2
    rw [norm₂_sq, dotProduct] at hc
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using hc
  have hcost := dyadicCostBound hε hε' hℓ J v hv x revoked hend hit (A.transpose * A) hdiag
  have hreg : generalInitialCost removed (s T).active (s T).z v =
      ∑ i : DyadicLevel J, (16/ε * ℓ i.1) *
        ((2*x i.1 i.2.val*v i.1 - (x i.1 i.2.val)^2) / (2^i.2.val*dyadicFloor J i.1)) := by
    rw [generalInitialCost, hsum (fun a z => generalInitialResidual a z v)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx, ← dyadicTerm_signed ε ℓ J i v (location i)]
    have heq := generalInitialResidual_eq (a := dyadicTerm ε ℓ J i) rfl (location i) v
    linarith only [heq]
  have htrace := weightedSurvivorTraceOnRun A hB hI hε hζ ambient hnorm T
  dsimp only at htrace hcost
  change (1 + ε ^ 2 / 48) * ((generalAddedSurvivors (s T).active).map
      fun a => a.measuredSquare ε).sum ≤
    ((1 + ε ^ 2 / 48) * (2 + ε ^ 2 / 48) / (ε ^ 2 / 48)) *
      (A.transpose * A * (B + ((generalInitialSurvivors (s T).active).map
        Term.curvature).sum)⁻¹).trace at htrace
  rw [hmatrix] at htrace
  have hskip := (generalSkipBudget_le L hL s q T).trans
    (mul_le_of_le_one_right (div_nonneg hL (by norm_num)) (by
      have hnonneg : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
      linarith only [hnonneg]))
  change generalSkippedSum ζ s q T ≤ L / 8 at hskip
  have hlifetime := generalLifetimeOnRun (feed := feed) hB hI hε hε' hζ T v hist
  dsimp only at hlifetime
  rw [hreg] at hlifetime
  dsimp only
  linarith only [hlifetime, htrace, hskip, hcost]

end Curvature

end
end


