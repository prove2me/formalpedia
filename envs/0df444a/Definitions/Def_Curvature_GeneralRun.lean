-- Prove2me | Definitions.Def_Curvature_GeneralRun
-- name    : Curvature_GeneralRun
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:10:19.988714+00:00
-- url     : https://prove2.me/theorems/91709218-a414-4d9a-a19f-1ea865ac85ed
-- title:
--   Runs of the revocation update from a general initial regularizer
-- statement:
--   This file extends the update of Algorithm 1 to an internal space $\mathbb R^N$ with a general initial regularizer, an input rule and creation thresholds. The initial state has iterate $0$, regularizer $\Psi_1(x)=\frac12x^\top Bx+\sum_a\frac{\gamma_a}{2}\langle q_a,x\rangle^2$ and Hessian $B+\sum_a\gamma_aq_aq_a^\top$, for a matrix $B$ and a finite list of initial quadratic regularization terms with creation round $0$, value $0$, coefficient $\gamma_a\ge0$ and threshold $h_a>0$.
--
--   In round $t$, the input $\widetilde g_t$ is a function of the round and the current internal iterate $z_t$, so it may be corrected using $z_t$. The iterate moves and revokes terms as in Algorithm 1. Let $H_t^-$ be the Hessian after the movement and $s_t^2\coloneqq\widetilde g_t^\top(H_t^-)^{-1}\widetilde g_t$. A new term, with the direction, value, coefficient and threshold of Algorithm 1, is created only if $s_t^2$ exceeds the creation threshold $\zeta_t$ of the round.
--
--   For a positive definite $B$, a parameter $\varepsilon>0$ and thresholds $\zeta_t\ge0$, the file records the history of a run: the created terms, the revoked terms with their revocation points, the surviving initial and created terms, and the identity that expresses the final regularizer as the initial regularizer plus the created terms minus the revoked divergences. Under the same conditions, it shows that the per-round stability of the objective formed by the regularizer and the past inputs lies in $[0,s_t^2/2]$, and that $0\le\langle\widetilde g_t,z_t-z_{t+1}\rangle\le s_t^2$. These runs give the core update of Algorithm 4 and its analysis in Section 3.2 and Appendices B.1–B.3.
-- source:
--   arXiv:2611.27572v1, Algorithm 3, p. 34; Appendices B.1–B.3, pp. 33–37. https://arxiv.org/html/2611.27572v1#algorithm3

import Definitions.Def_Curvature_BallState
import Definitions.Def_Curvature_Movement

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def BallState.objective (s : BallState d) (linear x : Vec d) : ℝ :=
  s.regularizer x + dotProduct linear x

def QuadraticAt (F : Vec d → ℝ) (H : Mat d) (z grad : Vec d) : Prop :=
  ∀ v, F (z + v) = F z + dotProduct grad v + dotProduct v (H.mulVec v) / 2

private theorem symmetric_pair {H : Mat d} (hs : H.IsSymm) (x y : Vec d) :
    dotProduct x (H.mulVec y) = dotProduct y (H.mulVec x) := by
  simpa only [hs.eq] using Matrix.dotProduct_transpose_mulVec H x y

theorem QuadraticAt.reanchor {F : Vec d → ℝ} {H : Mat d} {z grad : Vec d}
    (h : QuadraticAt F H z grad) (hs : H.IsSymm) (v : Vec d) :
    QuadraticAt F H (z + v) (grad + H.mulVec v) := by
  intro w
  rw [add_assoc, h (v + w), h v]
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [symmetric_pair hs v w, dotProduct_comm (H.mulVec v) w]
  ring

theorem Term.divergence_eq_curvature (a : Term d) (z v : Vec d) :
    a.divergence (z + v) z = dotProduct v (a.curvature.mulVec v) / 2 := by
  have hmul : a.curvature.mulVec v = (a.γ * dotProduct a.q v) • a.q := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Term.curvature, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hmul, dotProduct_smul, dotProduct_comm v a.q]
  simp [Term.divergence, smul_eq_mul]
  ring

private theorem divergence_sum (terms : List (Term d)) (z v : Vec d) :
    (terms.map fun a => a.divergence (z + v) z).sum =
      dotProduct v ((terms.map Term.curvature).sum.mulVec v) / 2 := by
  induction terms with
  | nil => simp
  | cons a terms ih =>
    simp only [List.map_cons, List.sum_cons, ih, a.divergence_eq_curvature,
      Matrix.add_mulVec, dotProduct_add]
    ring

theorem revokeAt_objective_eq (s : BallState d) (linear z : Vec d) :
    (revokeAt s z).objective linear z = s.objective linear z := by
  simp [revokeAt, BallState.objective, Term.divergence]

theorem QuadraticAt.revokeAt {s : BallState d} {linear z grad : Vec d}
    (h : QuadraticAt (s.objective linear) s.hessian z grad) :
    QuadraticAt ((Curvature.revokeAt s z).objective linear) (Curvature.revokeAt s z).hessian
      z grad := by
  intro v
  rw [revokeAt_objective_eq]
  let removed := (s.active.partition (fun a => decide (a.h ≤ |a.residual z|))).1
  change s.regularizer (z + v) - (removed.map fun a => a.divergence (z + v) z).sum +
      dotProduct linear (z + v) = _ + dotProduct v ((s.hessian -
        (removed.map Term.curvature).sum).mulVec v) / 2
  rw [divergence_sum, Matrix.sub_mulVec, dotProduct_sub]
  have h' := h v
  unfold BallState.objective at h' ⊢
  linarith


theorem QuadraticAt.addLinear {s : BallState d} {linear grad : Vec d}
    (h : QuadraticAt (s.objective linear) s.hessian s.z grad) (q : Vec d) :
    QuadraticAt (s.objective (linear + q)) s.hessian s.z (grad + q) := by
  intro v
  have h' := h v
  unfold BallState.objective at h' ⊢
  simp only [dotProduct_add, add_dotProduct] at h' ⊢
  linarith

theorem QuadraticAt.addCentered {s : BallState d} {linear grad : Vec d}
    (h : QuadraticAt (s.objective linear) s.hessian s.z grad) (a : Term d)
    (hm : a.m = dotProduct a.q s.z) :
    let s' := {s with regularizer := fun x => s.regularizer x + a.value x,
                       hessian := s.hessian + a.curvature, active := a :: s.active}
    QuadraticAt (s'.objective linear) s'.hessian s'.z grad := by
  dsimp only
  intro v
  have ha : a.value (s.z + v) = dotProduct v (a.curvature.mulVec v) / 2 := by
    rw [← a.divergence_eq_curvature s.z v]
    simp [Term.value, Term.divergence, Term.residual, hm, dotProduct_add]
  have h' := h v
  unfold BallState.objective at h' ⊢
  have hz : a.value s.z = 0 := by simp [Term.value, Term.residual, hm]
  dsimp only
  rw [ha, hz, Matrix.add_mulVec, dotProduct_add]
  simp only [dotProduct_add] at h' ⊢
  linarith

theorem inverseDirection_mulVec {H : Mat d} (hH : H.PosDef) (q : Vec d) :
    H.mulVec (H⁻¹.mulVec q) = q := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (H.isUnit_iff_isUnit_det.mp hH.isUnit),
    Matrix.one_mulVec]

theorem substep_energy {s : BallState d} {linear q : Vec d} {α : ℝ}
    (h : QuadraticAt (s.objective linear) s.hessian s.z (α • q))
    (hH : s.hessian.PosDef) (t : ℝ) :
    let v := s.hessian⁻¹.mulVec q
    let s' := revokeAt s (s.z - t • v)
    QuadraticAt (s'.objective linear) s'.hessian s'.z ((α - t) • q) ∧
      s.objective linear s.z - s'.objective linear s'.z =
        (α ^ 2 - (α - t) ^ 2) / 2 * dotProduct q v ∧
      dotProduct q (s.z - s'.z) = t * dotProduct q v := by
  let v := s.hessian⁻¹.mulVec q
  have hv : s.hessian.mulVec v = q := inverseDirection_mulVec hH q
  have hu := h.reanchor (Matrix.isHermitian_iff_isSymm.mp hH.isHermitian) (-(t • v))
  rw [← sub_eq_add_neg, Matrix.mulVec_neg, Matrix.mulVec_smul, hv, ← sub_eq_add_neg,
    ← sub_smul] at hu
  refine ⟨hu.revokeAt, ?_, ?_⟩
  · change s.objective linear s.z - (revokeAt s (s.z - t • v)).objective linear
        (s.z - t • v) = _
    rw [revokeAt_objective_eq, sub_eq_add_neg s.z, h]
    simp only [Matrix.mulVec_neg, Matrix.mulVec_smul, hv, neg_dotProduct, dotProduct_neg,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm v q]
    ring
  · change dotProduct q (s.z - (s.z - t • v)) = _
    rw [sub_sub_cancel, dotProduct_smul, smul_eq_mul]


theorem HessianInvariant.removed_posSemidef {B : Mat d} {s : BallState d}
    (h : HessianInvariant B s) (z : Vec d) :
    (s.hessian - (Curvature.revokeAt s z).hessian).PosSemidef := by
  simp only [Curvature.revokeAt, sub_sub_cancel, List.partition_eq_filter_filter]
  apply activeCurvature_posSemidef
  exact fun a ha => h.gamma_nonneg a (List.mem_filter.mp ha).1

structure MoveLoopEnergy (s out : BallState d) (linear q : Vec d) (α : ℝ) : Prop where
  posDef : out.hessian.PosDef
  removed : (s.hessian - out.hessian).PosSemidef
  centered : QuadraticAt (out.objective linear) out.hessian out.z 0
  decrease : s.objective linear s.z - out.objective linear out.z ∈
    Set.Icc 0 (α ^ 2 / 2 * dotProduct q (out.hessian⁻¹.mulVec q))
  displacement : dotProduct q (s.z - out.z) ∈
    Set.Icc 0 (α * dotProduct q (out.hessian⁻¹.mulVec q))

private theorem moveLoopEnergy_zero {s : BallState d} {linear q : Vec d}
    (h : QuadraticAt (s.objective linear) s.hessian s.z ((0 : ℝ) • q)) (hH : s.hessian.PosDef) :
    MoveLoopEnergy s s linear q 0 := by
  refine ⟨hH, ?_, ?_, ?_, ?_⟩
  · simpa using (Matrix.PosSemidef.zero : (0 : Mat d).PosSemidef)
  · simpa using h
  · simp
  · simp

theorem moveLoop_energy {B : Mat d} (hB : B.PosDef) {linear q : Vec d}
    (fuel : ℕ) {α : ℝ} {s out : BallState d} (hα : 0 ≤ α) (hs : HessianInvariant B s)
    (h : QuadraticAt (s.objective linear) s.hessian s.z (α • q))
    (run : moveLoop q fuel α s = some out) : MoveLoopEnergy s out linear q α := by
  induction fuel generalizing α s with
  | zero =>
    by_cases hz : α ≤ 0
    · have := le_antisymm hz hα
      subst α
      rw [moveLoop_of_nonpos _ _ le_rfl, Option.some.injEq] at run
      subst out
      exact moveLoopEnergy_zero h (hs.posDef hB)
    · simp [moveLoop, hz] at run
  | succ fuel ih =>
    rcases hα.eq_or_lt with hz | hα
    · subst α
      rw [moveLoop_of_nonpos _ _ le_rfl, Option.some.injEq] at run
      subst out
      exact moveLoopEnergy_zero h (hs.posDef hB)
    let v := s.hessian⁻¹.mulVec q
    let t := movementStep α (movementMax s v)
    let mid := revokeAt s (s.z - t • v)
    have ht : 0 ≤ t := (movementStep_pos hα (movementMax_nonneg s v)).le
    have hres : 0 ≤ α - t := sub_nonneg.mpr (movementStep_le _ _)
    obtain ⟨hexp, hdrop, hdisp⟩ := substep_energy h (hs.posDef hB) t
    have hrec := moveLoop_positive_step q fuel hα s (hs.inverseDirection hB q)
    change moveLoop q (fuel + 1) α s = moveLoop q fuel (α - t) mid at hrec
    rw [hrec] at run
    have hm : MoveLoopEnergy mid out linear q (α - t) := ih hres (hs.revokeAt _) hexp run
    have hdiff : (s.hessian - out.hessian).PosSemidef := by
      have hd : (s.hessian - mid.hessian).PosSemidef := hs.removed_posSemidef _
      simpa only [sub_add_sub_cancel] using hd.add hm.removed
    have horder := inverseQuadratic_mono hm.posDef (hs.posDef hB) hdiff q
    let V := dotProduct q (out.hessian⁻¹.mulVec q)
    let U := dotProduct q v
    change U ≤ V at horder
    have hU : 0 ≤ U := by simpa [U, v] using
      (hs.posDef hB).inv.posSemidef.dotProduct_mulVec_nonneg q
    have hw : 0 ≤ (α ^ 2 - (α - t) ^ 2) / 2 := by
      nlinarith [mul_nonneg ht (show 0 ≤ α + (α - t) by linarith)]
    change s.objective linear s.z - mid.objective linear mid.z = _ * U at hdrop
    change dotProduct q (s.z - mid.z) = t * U at hdisp
    refine ⟨hm.posDef, hdiff, hm.centered, ?_, ?_⟩
    · obtain ⟨hm₀, hm₁⟩ := hm.decrease
      change _ ≤ (α - t) ^ 2 / 2 * V at hm₁
      change 0 ≤ _ ∧ _ ≤ α ^ 2 / 2 * V
      exact ⟨by linarith [mul_nonneg hw hU], by
        nlinarith only [hm₁, hdrop, mul_le_mul_of_nonneg_left horder hw]⟩
    · obtain ⟨hm₀, hm₁⟩ := hm.displacement
      change _ ≤ (α - t) * V at hm₁
      have hsum : dotProduct q (s.z - out.z) =
          dotProduct q (s.z - mid.z) + dotProduct q (mid.z - out.z) := by
        simp only [dotProduct_sub]; ring
      change 0 ≤ _ ∧ _ ≤ α * V
      exact ⟨by linarith [mul_nonneg ht hU], by
        nlinarith only [hsum, hdisp, hm₁, mul_le_mul_of_nonneg_left horder ht]⟩

theorem ftrlObjective_eq_objective (s : ℕ → BallState d) (q : ℕ → Vec d) (t : ℕ) :
    ftrlObjective s q t = (s t).objective (∑ j ∈ Finset.range t, q j) := by
  funext x
  simp only [ftrlObjective, BallState.objective, sum_dotProduct]


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

structure GeneralInitialTerms (terms : List (Term d)) : Prop where
  initialRound : ∀ a ∈ terms, a.round = 0
  center : ∀ a ∈ terms, a.m = 0
  coefficient : ∀ a ∈ terms, 0 ≤ a.γ
  threshold : ∀ a ∈ terms, 0 < a.h

def generalInitial (B : Mat d) (terms : List (Term d)) : BallState d :=
  { z := 0
    regularizer := fun x => dotProduct x (B.mulVec x) / 2 + (terms.map fun a => a.value x).sum
    hessian := B + (terms.map Term.curvature).sum
    active := terms }

def generalMove (s : BallState d) (q : Vec d) : BallState d :=
  (moveLoop q (s.active.length + 1) 1 s).getD s

def generalSquare (s : BallState d) (q : Vec d) : ℝ :=
  dotProduct q ((generalMove s q).hessian⁻¹.mulVec q)

def generalStep (ε ζ : ℝ) (round : ℕ) (s : BallState d) (q : Vec d) : BallState d :=
  let moved := generalMove s q
  if ζ < generalSquare s q then moved.addTerm (createdTerm ε round q moved) else moved

def generalStateAfter (initial : BallState d) (ε : ℝ) (ζ : ℕ → ℝ)
    (feed : ℕ → Vec d → Vec d) : ℕ → BallState d
  | 0 => initial
  | t + 1 =>
    let s := generalStateAfter initial ε ζ feed t
    generalStep ε (ζ t) (t + 1) s (feed t s.z)

theorem generalMove_spec {B : Mat d} (hB : B.PosDef) {s : BallState d}
    (hH : HessianInvariant B s) (hI : ActiveInterior s) (q : Vec d) :
    moveLoop q (s.active.length + 1) 1 s = some (generalMove s q) ∧
      HessianInvariant B (generalMove s q) ∧ ActiveInterior (generalMove s q) := by
  obtain ⟨m, hm, hmH, hmI⟩ := moveLoop_succeeds q (HessianInvariant B)
    (fun _ h => h.det_ne_zero hB) (fun _ h => h.revokeAt)
    (s.active.length + 1) 1 s hH hI (Nat.lt_succ_self _)
  simpa [generalMove, hm] using And.intro hm (And.intro hmH hmI)

theorem generalInitial_invariant {B : Mat d} {I : List (Term d)} (hI : GeneralInitialTerms I) :
    HessianInvariant B (generalInitial B I) ∧ ActiveInterior (generalInitial B I) := by
  refine ⟨⟨rfl, hI.coefficient⟩, ?_⟩
  intro a ha
  simpa [generalInitial, Term.residual, hI.center a ha] using hI.threshold a ha

theorem generalStateAfter_invariant {B : Mat d} (hB : B.PosDef) {I : List (Term d)}
    (hI : GeneralInitialTerms I) {ε : ℝ} (hε : 0 < ε) {ζ : ℕ → ℝ} (hζ : ∀ i, 0 ≤ ζ i)
    (feed : ℕ → Vec d → Vec d) (t : ℕ) :
    let s := generalStateAfter (generalInitial B I) ε ζ feed t
    HessianInvariant B s ∧ ActiveInterior s := by
  induction t with
  | zero => exact generalInitial_invariant hI
  | succ t ih =>
    let s := generalStateAfter (generalInitial B I) ε ζ feed t
    let q := feed t s.z
    obtain ⟨_, hH, hInterior⟩ := generalMove_spec hB ih.1 ih.2 q
    change HessianInvariant B (generalStep ε (ζ t) (t+1) s q) ∧ ActiveInterior (generalStep ε (ζ t) (t+1) s q)
    unfold generalStep
    split
    · rename_i h
      have hv : 0 < generalSquare s q := (hζ t).trans_lt h
      let a := createdTerm ε (t+1) q (generalMove s q)
      have hγ : 0 ≤ a.γ := div_nonneg (sq_nonneg ε) (mul_nonneg (by norm_num) hv.le)
      have hh : 0 < a.h := div_pos (mul_pos (by norm_num) hv) hε
      refine ⟨hH.add a hγ, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa [BallState.addTerm, Term.residual, a, createdTerm] using hh
      · exact hInterior b hb
    · exact ⟨hH, hInterior⟩

theorem generalStep_z (ε ζ : ℝ) (round : ℕ) (s : BallState d) (q : Vec d) :
    (generalStep ε ζ round s q).z = (generalMove s q).z := by
  unfold generalStep
  split <;> rfl

theorem generalStep_objective (ε ζ : ℝ) (round : ℕ) (s : BallState d) (q linear : Vec d) :
    let o := generalStep ε ζ round s q
    let m := generalMove s q
    o.objective linear o.z = m.objective linear m.z := by
  unfold generalStep
  split <;> simp [BallState.addTerm, BallState.objective, Term.value, Term.residual, createdTerm]

theorem generalDivergenceSum (terms : List (Term d)) (z v : Vec d) :
    (terms.map fun a => a.divergence (z + v) z).sum =
      dotProduct v ((terms.map Term.curvature).sum.mulVec v) / 2 := by
  induction terms with
  | nil => simp
  | cons a terms ih =>
    simp only [List.map_cons, List.sum_cons, ih, a.divergence_eq_curvature,
      Matrix.add_mulVec, dotProduct_add]
    ring

theorem generalInitial_value_zero {I : List (Term d)} (hI : GeneralInitialTerms I)
    (B : Mat d) : (generalInitial B I).regularizer 0 = 0 := by
  have hz : (I.map fun a => a.value 0).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      simp [Term.value, Term.residual, hI.center _ ha]
  simpa [generalInitial] using hz

theorem generalInitial_centered {I : List (Term d)} (hI : GeneralInitialTerms I) (B : Mat d) :
    let s := generalInitial B I
    QuadraticAt (s.objective 0) s.hessian s.z 0 := by
  dsimp only
  intro v
  have hmap : I.map (fun a => a.value v) = I.map (fun a => a.divergence (0 + v) 0) := by
    apply List.map_congr_left
    intro a ha
    simp [Term.value, Term.residual, Term.divergence, hI.center a ha]
  have hsum := generalDivergenceSum I 0 v
  have hzero := generalInitial_value_zero hI B
  change (generalInitial B I).objective 0 (0 + v) = (generalInitial B I).objective 0 0 + dotProduct 0 v + _
  simp only [BallState.objective, zero_dotProduct, add_zero, zero_add, hzero]
  change dotProduct v (B.mulVec v) / 2 + _ = dotProduct v ((B + _).mulVec v) / 2
  rw [hmap, hsum, Matrix.add_mulVec, dotProduct_add]
  ring

section Run
variable {B : Mat d} {I : List (Term d)} {ε : ℝ} {ζ : ℕ → ℝ}
    {feed : ℕ → Vec d → Vec d}
local notation "s₀" => generalInitial B I
local notation "s" => generalStateAfter s₀ ε ζ feed
local notation "q" => (fun i => feed i (BallState.z (s i)))

theorem generalStateAfter_centered (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hζ : ∀ i, 0 ≤ ζ i) (t : ℕ) :
    QuadraticAt (ftrlObjective s q t) (s t).hessian (s t).z 0 := by
  rw [ftrlObjective_eq_objective]
  induction t with
  | zero => simpa [generalStateAfter] using generalInitial_centered hI B
  | succ t ih =>
    let linear := ∑ i ∈ Finset.range t, q i
    obtain ⟨hH, hAct⟩ := generalStateAfter_invariant hB hI hε hζ feed t
    have hm := (generalMove_spec hB hH hAct (q t)).1
    have hstart : QuadraticAt ((s t).objective (linear + q t)) (s t).hessian (s t).z
        ((1 : ℝ) • q t) := by simpa using ih.addLinear (q t)
    have he := moveLoop_energy hB _ zero_le_one hH hstart hm
    rw [Finset.sum_range_succ]
    change QuadraticAt ((generalStep ε (ζ t) (t+1) (s t) (q t)).objective _) _ _ _
    by_cases hadd : ζ t < generalSquare (s t) (q t)
    · simp only [generalStateAfter, generalStep, if_pos hadd]
      exact
        he.centered.addCentered (createdTerm ε (t+1) (q t) (generalMove (s t) (q t))) rfl
    · simpa only [generalStateAfter, generalStep, if_neg hadd] using he.centered

theorem generalRound_energy (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hζ : ∀ i, 0 ≤ ζ i) (t : ℕ) :
    roundStability s q t ∈ Set.Icc 0 (generalSquare (s t) (q t) / 2) ∧
      dotProduct (q t) ((s t).z - (s (t+1)).z) ∈ Set.Icc 0 (generalSquare (s t) (q t)) := by
  let linear := ∑ i ∈ Finset.range t, q i
  obtain ⟨hH, hAct⟩ := generalStateAfter_invariant hB hI hε hζ feed t
  have hm := (generalMove_spec hB hH hAct (q t)).1
  have hc := generalStateAfter_centered (feed := feed) hB hI hε hζ t
  rw [ftrlObjective_eq_objective] at hc
  have hstart : QuadraticAt ((s t).objective (linear + q t)) (s t).hessian (s t).z
      ((1 : ℝ) • q t) := by simpa using hc.addLinear (q t)
  have he := moveLoop_energy hB _ zero_le_one hH hstart hm
  have hst : roundStability s q t = (s t).objective (linear + q t) (s t).z -
      (generalMove (s t) (q t)).objective (linear + q t) (generalMove (s t) (q t)).z := by
    rw [roundStability, ftrlObjective_eq_objective, ftrlObjective_eq_objective, Finset.sum_range_succ]
    change _ - (generalStep ε (ζ t) (t+1) (s t) (q t)).objective _
      (generalStep ε (ζ t) (t+1) (s t) (q t)).z = _
    rw [generalStep_objective]
    simp [BallState.objective, linear, add_dotProduct, add_assoc]
  rw [hst]
  change _ ∧ dotProduct _ (_ - (generalStep ε (ζ t) (t+1) (s t) (q t)).z) ∈ _
  rw [generalStep_z]
  exact ⟨by simpa [generalSquare, div_eq_mul_inv, mul_comm] using he.decrease,
    by simpa [generalSquare] using he.displacement⟩

theorem generalStateAfter_gap (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hζ : ∀ i, 0 ≤ ζ i) (t : ℕ) (u : Vec d) :
    let v := u - (s t).z
    ftrlObjective s q t u - ftrlObjective s q t (s t).z =
      dotProduct v (B.mulVec v) / 2 + ((s t).active.map fun a => a.divergence u (s t).z).sum := by
  let v := u - (s t).z
  have hv : (s t).z + v = u := add_sub_cancel ..
  have hH := (generalStateAfter_invariant hB hI hε hζ feed t).1
  have hexp := generalStateAfter_centered (feed := feed) hB hI hε hζ t v
  have hsum := generalDivergenceSum (s t).active (s t).z v
  rw [hv, zero_dotProduct, add_zero, hH.decomposition, Matrix.add_mulVec, dotProduct_add] at hexp
  rw [hv] at hsum
  change _ = dotProduct v _ / 2 + _
  linarith

end Run
end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def generalAdditions (ε : ℝ) (ζ : ℕ → ℝ) (s : ℕ → BallState d) (q : ℕ → Vec d) :
    ℕ → List (Term d)
  | 0 => []
  | t + 1 =>
    let previous := generalAdditions ε ζ s q t
    if ζ t < generalSquare (s t) (q t) then
      createdTerm ε (t+1) (q t) (generalMove (s t) (q t)) :: previous
    else previous

theorem generalAdditions_origin {ε : ℝ} {ζ : ℕ → ℝ} {s : ℕ → BallState d} {q : ℕ → Vec d}
    {t : ℕ} {a : Term d} (ha : a ∈ generalAdditions ε ζ s q t) :
    ∃ i < t, ζ i < generalSquare (s i) (q i) ∧
      a = createdTerm ε (i+1) (q i) (generalMove (s i) (q i)) := by
  induction t with
  | zero => simp [generalAdditions] at ha
  | succ t ih =>
    simp only [generalAdditions] at ha
    split at ha
    · rename_i hadd
      rcases List.mem_cons.mp ha with he | ha
      · exact ⟨t, Nat.lt_succ_self _, hadd, he⟩
      · obtain ⟨i, hi, ho⟩ := ih ha
        exact ⟨i, Nat.lt_succ_of_lt hi, ho⟩
    · obtain ⟨i, hi, ho⟩ := ih ha
      exact ⟨i, Nat.lt_succ_of_lt hi, ho⟩

theorem generalAdditions_positive_round {ε : ℝ} {ζ : ℕ → ℝ} {s : ℕ → BallState d}
    {q : ℕ → Vec d} {t : ℕ} {a : Term d} (ha : a ∈ generalAdditions ε ζ s q t) :
    a.round ≠ 0 := by
  obtain ⟨i, _, _, rfl⟩ := generalAdditions_origin ha
  exact Nat.succ_ne_zero _

theorem generalAdditions_sum (ε : ℝ) (ζ : ℕ → ℝ) (s : ℕ → BallState d) (q : ℕ → Vec d)
    (t : ℕ) (f : ℕ → ℝ) :
    ((generalAdditions ε ζ s q t).map fun a => f (a.round-1)).sum =
      ∑ i ∈ Finset.range t, if ζ i < generalSquare (s i) (q i) then f i else 0 := by
  induction t with
  | zero => simp [generalAdditions]
  | succ t ih =>
    rw [Finset.sum_range_succ, generalAdditions]
    split <;> simp [createdTerm, ih, add_comm]

structure GeneralRunHistory (I : List (Term d)) (ε : ℝ) (ζ : ℕ → ℝ)
    (s : ℕ → BallState d) (q : ℕ → Vec d) (T : ℕ) (removed : List (Term d × Vec d)) : Prop where
  partition : ((removed.map Prod.fst) ++ (s T).active).Perm (generalAdditions ε ζ s q T ++ I)
  regularizer : ∀ u, (s T).regularizer u = (s 0).regularizer u +
    ((generalAdditions ε ζ s q T).map fun a => a.value u).sum -
    (removed.map fun e => e.1.divergence u e.2).sum
  thresholds : ∀ a z, (a, z) ∈ removed → a.h ≤ |a.residual z| ∧ |a.residual z| < 3 * a.h
  interior : ActiveInterior (s T)

section Run
variable {B : Mat d} {I : List (Term d)} {ε : ℝ} {ζ : ℕ → ℝ} {feed : ℕ → Vec d → Vec d}
local notation "s" => generalStateAfter (generalInitial B I) ε ζ feed
local notation "q" => (fun i => feed i (BallState.z (s i)))

theorem generalStateAfter_history (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hζ : ∀ i, 0 ≤ ζ i) (T : ℕ) :
    ∃ removed, GeneralRunHistory I ε ζ s q T removed := by
  induction T with
  | zero =>
    refine ⟨[], ?_⟩
    constructor
    · simp [generalAdditions, generalStateAfter, generalInitial]
    · simp [generalAdditions]
    · simp
    · exact (generalInitial_invariant hI).2
  | succ T ih =>
    obtain ⟨old, hist⟩ := ih
    obtain ⟨hH, hAct⟩ := generalStateAfter_invariant hB hI hε hζ feed T
    let m := generalMove (s T) (q T)
    have hm := (generalMove_spec hB hH hAct (q T)).1
    obtain ⟨batch, hs⟩ := moveLoop_history _ _ _ _ _ hAct hm
    have hpart : (((old.map Prod.fst) ++ batch.map Prod.fst) ++ m.active).Perm
        (generalAdditions ε ζ s q T ++ I) := by
      rw [List.append_assoc]
      exact (hs.partition.append_left _).trans hist.partition
    refine ⟨old ++ batch, ?_⟩
    constructor
    · simp only [generalStateAfter, generalAdditions, generalStep, List.map_append]
      split
      · exact List.perm_middle.trans (hpart.cons _)
      · exact hpart
    · intro u
      have hr := hs.regularizer u
      simp only [generalStateAfter, generalAdditions, generalStep, List.map_append, List.sum_append]
      split <;> (try simp only [BallState.addTerm, List.map_cons, List.sum_cons]) <;>
        rw [hr, hist.regularizer] <;> simp only [generalStateAfter] <;> abel
    · intro a z ha
      exact (List.mem_append.mp ha).elim (hist.thresholds a z) (hs.thresholds a z)
    · exact (generalStateAfter_invariant hB hI hε hζ feed (T+1)).2

end Run

def generalInitialRemoved (removed : List (Term d × Vec d)) : List (Term d × Vec d) :=
  removed.filter fun e => decide (e.1.round = 0)

def generalInitialSurvivors (active : List (Term d)) : List (Term d) :=
  active.filter fun a => decide (a.round = 0)

def generalAddedSurvivors (active : List (Term d)) : List (Term d) :=
  active.filter fun a => decide (a.round ≠ 0)

theorem GeneralRunHistory.initialPartition {I : List (Term d)} {ε : ℝ} {ζ : ℕ → ℝ}
    {s : ℕ → BallState d} {q : ℕ → Vec d} {T : ℕ} {removed : List (Term d × Vec d)}
    (hist : GeneralRunHistory I ε ζ s q T removed) (hI : GeneralInitialTerms I) :
    (((generalInitialRemoved removed).map Prod.fst) ++ generalInitialSurvivors (s T).active).Perm I := by
  have h := hist.partition.filter (fun a => decide (a.round = 0))
  have hadd : (generalAdditions ε ζ s q T).filter (fun a => decide (a.round = 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    simp [generalAdditions_positive_round ha]
  have hinit : I.filter (fun a => decide (a.round = 0)) = I := by
    apply List.filter_eq_self.mpr
    intro a ha
    simp [hI.initialRound a ha]
  simpa only [List.filter_append, List.filter_map, Function.comp_def, hadd, hinit, List.nil_append,
    generalInitialSurvivors, generalInitialRemoved] using h

end Curvature

end
end


