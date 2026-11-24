-- Prove2me | Definitions.Def_Curvature_Movement
-- name    : Curvature_Movement
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:09:06.943374+00:00
-- url     : https://prove2.me/theorems/78900b07-da54-4680-8129-f952138b2a5c
-- title:
--   Movement steps, revocation records and created terms in Algorithm 1
-- statement:
--   This file isolates the quantities that control the movement of the iterate within one round of Algorithm 1 and the quadratic regularization term created at its end. For a state with active family $\mathcal Q$ and a direction $v$, the movement rate is $L(v)\coloneqq\max_{a\in\mathcal Q}|\langle q_a,v\rangle|/h_a$, with $L(v)=0$ for an empty family. With remaining weight $\alpha>0$, a partial step has weight $\alpha$ if $L(v)=0$ and $\min\{\alpha,2/L(v)\}$ otherwise. A state is interior if every active term satisfies $|\rho_a(z)|<h_a$ at the iterate $z$, where $\rho_a(x)\coloneqq\langle q_a,x\rangle-m_a$.
--
--   A revocation record lists the revoked terms with their revocation points $z$. It expresses the new regularizer and Hessian as the old ones minus the revoked divergences $\frac{\gamma_a}{2}\langle q_a,x-z\rangle^2$ and curvatures $\gamma_aq_aq_a^\top$, and it records $h_a\le|\rho_a(z)|<3h_a$ for each revoked term. The file shows that the movement from an interior state finishes within one more step than the number of active terms, provided that the Hessian is invertible at the start of the movement and remains invertible after each revocation. The runs in Theorem 2 satisfy this condition.
--
--   The created term is defined from the input $q$ and the state at the end of the movement, with iterate $z$ and Hessian $H$. Fix $\varepsilon>0$. When $s^2\coloneqq q^\top H^{-1}q>0$, Algorithm 1 adds a term with direction $q$ and sets $m=\langle q,z\rangle$, the value of the linear form at the end of the movement. The term has coefficient $\gamma=\varepsilon^2/(48s^2)$ and threshold $h=8s^2/\varepsilon$, so that $\varepsilon h/8=s^2$. Sections 3.2 and 3.4 and Appendix B.2 use these objects to bound the movement and each term over its lifetime.
-- source:
--   arXiv:2611.27572v1, Algorithm 2, p. 7; Sections 3.2 and 3.4, pp. 7–8 and 10–11; Appendix B.2, pp. 34–35. https://arxiv.org/html/2611.27572v1#algorithm2

import Definitions.Def_Curvature_BallState
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def ActiveInterior (s : BallState d) : Prop :=
  ∀ a ∈ s.active, |a.residual s.z| < a.h

theorem revokeAt_active_mem (s : BallState d) (z : Vec d) (a : Term d) :
    a ∈ (revokeAt s z).active ↔ a ∈ s.active ∧ |a.residual z| < a.h := by
  simp [revokeAt]

theorem revokeAt_activeInterior (s : BallState d) (z : Vec d) :
    ActiveInterior (revokeAt s z) := fun a ha => ((revokeAt_active_mem s z a).mp ha).2

def movementMax (s : BallState d) (v : Vec d) : ℝ :=
  s.active.foldl (fun m a => max m (|dotProduct a.q v| / a.h)) 0

def movementStep (α L : ℝ) : ℝ := if L = 0 then α else min α (2 / L)

private theorem foldlMax_spec {β : Type*} (f : β → ℝ) (l : List β) (m : ℝ) :
    let M := l.foldl (fun acc x => max acc (f x)) m
    m ≤ M ∧ (∀ x ∈ l, f x ≤ M) ∧ (m < M → ∃ x ∈ l, f x = M) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    dsimp only [List.foldl_cons]
    obtain ⟨hbound, hall, hattain⟩ := ih (max m (f a))
    refine ⟨(le_max_left _ _).trans hbound, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (le_max_right _ _).trans hbound
      · exact hall x hx
    · intro h
      rcases hbound.eq_or_lt with hEq | hLt
      · have hma : m < f a := by
          rw [← hEq, lt_max_iff] at h
          exact h.resolve_left (lt_irrefl _)
        exact ⟨a, List.mem_cons_self, (max_eq_right hma.le).symm.trans hEq⟩
      · obtain ⟨x, hx, hM⟩ := hattain hLt
        exact ⟨x, List.mem_cons_of_mem _ hx, hM⟩

theorem movementMax_nonneg (s : BallState d) (v : Vec d) :
    0 ≤ movementMax s v :=
  (foldlMax_spec (fun a : Term d => |dotProduct a.q v| / a.h) s.active 0).1

theorem le_movementMax {s : BallState d} (v : Vec d) {a : Term d} (ha : a ∈ s.active) :
    |dotProduct a.q v| / a.h ≤ movementMax s v :=
  (foldlMax_spec (fun a : Term d => |dotProduct a.q v| / a.h) s.active 0).2.1 a ha

theorem movementMax_attained {s : BallState d} {v : Vec d} (h : 0 < movementMax s v) :
    ∃ a ∈ s.active, |dotProduct a.q v| / a.h = movementMax s v :=
  (foldlMax_spec _ s.active 0).2.2 h

theorem movementStep_pos {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) :
    0 < movementStep α L := by
  unfold movementStep
  split_ifs with h
  · exact hα
  · exact lt_min hα (div_pos (by norm_num) (lt_of_le_of_ne hL (Ne.symm h)))

theorem movementStep_le (α L : ℝ) : movementStep α L ≤ α := by
  by_cases h : L = 0 <;> simp [movementStep, h]

theorem Term.residual_after_step (a : Term d) (z v : Vec d) (step : ℝ) :
    a.residual (z - step • v) = a.residual z - step * dotProduct a.q v := by
  simp only [Term.residual, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

theorem movementStep_displacement_le {s : BallState d} (hs : ActiveInterior s)
    {α : ℝ} (hα : 0 < α) (v : Vec d) {a : Term d} (ha : a ∈ s.active) :
    |movementStep α (movementMax s v) * dotProduct a.q v| ≤ 2 * a.h := by
  have hh := (abs_nonneg _).trans_lt (hs a ha)
  have hdot := (div_le_iff₀ hh).mp (le_movementMax v ha)
  have hL := movementMax_nonneg s v
  have hstep := movementStep_pos hα hL
  rw [abs_mul, abs_of_pos hstep]
  by_cases h : movementMax s v = 0
  · rw [h, zero_mul] at hdot
    rw [le_antisymm hdot (abs_nonneg _), mul_zero]
    linarith
  · have hLpos := lt_of_le_of_ne hL (Ne.symm h)
    have hcap : movementStep α (movementMax s v) * movementMax s v ≤ 2 := by
      apply (le_div_iff₀ hLpos).mp
      simp [movementStep, h]
    calc
      _ ≤ movementStep α (movementMax s v) * (movementMax s v * a.h) :=
        mul_le_mul_of_nonneg_left hdot hstep.le
      _ = (movementStep α (movementMax s v) * movementMax s v) * a.h := (mul_assoc ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hcap hh.le

theorem movementStep_residual_lt {s : BallState d} (hs : ActiveInterior s)
    {α : ℝ} (hα : 0 < α) (v : Vec d) {a : Term d} (ha : a ∈ s.active) :
    |a.residual (s.z - movementStep α (movementMax s v) • v)| < 3 * a.h := by
  rw [Term.residual_after_step]
  have htriangle := abs_sub (a.residual s.z) (movementStep α (movementMax s v) * dotProduct a.q v)
  have hbefore := hs a ha
  have hstep := movementStep_displacement_le hs hα v ha
  linarith

theorem nonfinal_revokeAt_length_lt {s : BallState d} (hs : ActiveInterior s)
    {α : ℝ} (v : Vec d) (hn : movementStep α (movementMax s v) < α) :
    (revokeAt s (s.z - movementStep α (movementMax s v) • v)).active.length <
      s.active.length := by
  let L := movementMax s v
  have hL : 0 < L := lt_of_le_of_ne (movementMax_nonneg s v) (by
    intro h
    simp [movementStep, ← h, L] at hn)
  have hne := hL.ne'
  have hstep : movementStep α L = 2 / L := by
    unfold movementStep at *
    change (if L = 0 then α else min α (2 / L)) < α at hn
    rw [if_neg hne, min_lt_iff] at hn
    rw [if_neg hne, min_eq_right (hn.resolve_left (lt_irrefl _)).le]
  obtain ⟨a, ha, hmax⟩ := movementMax_attained hL
  have hh := (abs_nonneg _).trans_lt (hs a ha)
  have habs : |dotProduct a.q v| = L * a.h := (div_eq_iff hh.ne').mp hmax
  have hdisp : |movementStep α L * dotProduct a.q v| = 2 * a.h := by
    rw [hstep, abs_mul, abs_of_pos (div_pos (by norm_num) hL), habs, ← mul_assoc,
      div_mul_cancel₀ _ hne]
  have hpost : a.h < |a.residual (s.z - movementStep α L • v)| := by
    rw [Term.residual_after_step]
    have htriangle := abs_sub (a.residual s.z) (a.residual s.z -
      movementStep α L * dotProduct a.q v)
    rw [sub_sub_cancel] at htriangle
    linarith [hs a ha]
  simp only [revokeAt, List.partition_eq_filter_filter]
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨a, ha, by simpa using hpost.le⟩

theorem moveLoop_of_nonpos (q : Vec d) (fuel : ℕ) {α : ℝ} (hα : α ≤ 0)
    (s : BallState d) : moveLoop q fuel α s = some s := by
  cases fuel <;> simp [moveLoop, hα]

theorem moveLoop_positive_step (q : Vec d) (fuel : ℕ) {α : ℝ} (hα : 0 < α)
    (s : BallState d) {v : Vec d} (hv : inverseDirection s.hessian q = some v) :
    let step := movementStep α (movementMax s v)
    moveLoop q (fuel + 1) α s = moveLoop q fuel (α - step) (revokeAt s (s.z - step • v)) := by
  by_cases h : movementMax s v = 0 <;>
    unfold movementMax at h <;> simp [moveLoop, not_le.mpr hα, hv, movementStep, movementMax, h]

theorem moveLoop_succeeds (q : Vec d) (P : BallState d → Prop)
    (hinv : ∀ s, P s → s.hessian.det ≠ 0)
    (hrev : ∀ s, P s → ∀ z, P (revokeAt s z))
    (fuel : ℕ) (α : ℝ) (s : BallState d) (hs : P s) (hi : ActiveInterior s)
    (hfuel : s.active.length < fuel) :
    ∃ s', moveLoop q fuel α s = some s' ∧ P s' ∧ ActiveInterior s' := by
  induction fuel generalizing α s with
  | zero => omega
  | succ fuel ih =>
    by_cases hα : α ≤ 0
    · exact ⟨s, moveLoop_of_nonpos q _ hα s, hs, hi⟩
    let v := s.hessian⁻¹.mulVec q
    have hv : inverseDirection s.hessian q = some v := by
      simp [inverseDirection, hinv s hs, v]
    let step := movementStep α (movementMax s v)
    let z' := s.z - step • v
    have hstep := moveLoop_positive_step q fuel (lt_of_not_ge hα) s hv
    change moveLoop q (fuel + 1) α s = moveLoop q fuel (α - step) (revokeAt s z') at hstep
    rw [hstep]
    have hs' := hrev s hs z'
    have hi' := revokeAt_activeInterior s z'
    by_cases hfinal : α - step ≤ 0
    · exact ⟨_, moveLoop_of_nonpos q _ hfinal _, hs', hi'⟩
    · have hlt : (revokeAt s z').active.length < s.active.length :=
        nonfinal_revokeAt_length_lt hi v (by change step < α; linarith)
      exact ih _ _ hs' hi' (by omega)

def createdTerm (ε : ℝ) (round : ℕ) (q : Vec d) (moved : BallState d) : Term d :=
  let sSq := dotProduct q (moved.hessian⁻¹.mulVec q)
  ⟨round, q, dotProduct q moved.z, ε ^ 2 / (48 * sSq), 8 * sSq / ε⟩

def BallState.addTerm (s : BallState d) (a : Term d) : BallState d :=
  {s with regularizer := fun x => s.regularizer x + a.value x,
          hessian := s.hessian + a.curvature, active := a :: s.active}


end Curvature

end
end

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}

theorem inv_rankOne_add (H : Mat d) (hH : H.PosDef) (q : Vec d) (γ : ℝ)
    (hden : 1 + γ * dotProduct q (H⁻¹.mulVec q) ≠ 0) :
    let w := H⁻¹.mulVec q
    (H + γ • Matrix.vecMulVec q q)⁻¹ =
      H⁻¹ - (γ / (1 + γ * dotProduct q w)) • Matrix.vecMulVec w w := by
  let w := H⁻¹.mulVec q
  let s := dotProduct q w
  let c := γ / (1 + γ * s)
  have hcancel : H * H⁻¹ = 1 :=
    H.mul_nonsing_inv (H.isUnit_iff_isUnit_det.mp hH.isUnit)
  have hHw : H.mulVec w = q := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  have hsymm : (H⁻¹).transpose = H⁻¹ :=
    Matrix.isHermitian_iff_isSymm.mp hH.inv.isHermitian
  have hqinv : Matrix.vecMul q H⁻¹ = w := by
    simpa only [hsymm] using Matrix.vecMul_transpose H⁻¹ q
  have hscalar : γ - c - γ * (c * s) = 0 := by
    dsimp [c]
    field_simp [show 1 + γ * s ≠ 0 from hden]
    ring
  have hprod : (γ • Matrix.vecMulVec q q) * (c • Matrix.vecMulVec w w) =
      (γ * (c * s)) • Matrix.vecMulVec q w := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_smul]
    change γ • (c • (s • Matrix.vecMulVec q w)) = _
    rw [smul_smul c s, smul_smul]
  change (H + γ • Matrix.vecMulVec q q)⁻¹ = H⁻¹ - c • Matrix.vecMulVec w w
  apply Matrix.inv_eq_right_inv
  calc
    (H + γ • Matrix.vecMulVec q q) * (H⁻¹ - c • Matrix.vecMulVec w w) =
        1 - c • Matrix.vecMulVec q w + γ • Matrix.vecMulVec q w -
          (γ * (c * s)) • Matrix.vecMulVec q w := by
      rw [mul_sub, add_mul, add_mul, hcancel, hprod]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, hHw,
        Matrix.vecMulVec_mul, hqinv]
      abel
    _ = 1 + (γ - c - γ * (c * s)) • Matrix.vecMulVec q w := by
      rw [sub_smul, sub_smul]
      abel
    _ = 1 := by rw [hscalar, zero_smul, add_zero]


end Curvature

end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

structure RevocationHistory (s s' : BallState d) (removed : List (Term d × Vec d)) : Prop where
  survivors : s'.active.Sublist s.active
  partition : ((removed.map Prod.fst) ++ s'.active).Perm s.active
  regularizer : ∀ x, s'.regularizer x =
    s.regularizer x - (removed.map fun (a, z) => a.divergence x z).sum
  hessian : s'.hessian = s.hessian - (removed.map fun (a, _) => a.curvature).sum
  thresholds : ∀ a z, (a, z) ∈ removed → a.h ≤ |a.residual z| ∧ |a.residual z| < 3 * a.h
  interior : ActiveInterior s'

theorem RevocationHistory.nil (s : BallState d) (hs : ActiveInterior s) :
    RevocationHistory s s [] := by
  constructor <;> simp [hs]

theorem RevocationHistory.append {s m t : BallState d} {r₁ r₂ : List (Term d × Vec d)}
    (h₁ : RevocationHistory s m r₁) (h₂ : RevocationHistory m t r₂) :
    RevocationHistory s t (r₁ ++ r₂) := by
  constructor
  · exact h₂.survivors.trans h₁.survivors
  · simpa only [List.map_append, List.append_assoc] using
      (h₂.partition.append_left (r₁.map Prod.fst)).trans h₁.partition
  · intro x
    rw [h₂.regularizer, h₁.regularizer, List.map_append, List.sum_append]
    abel
  · rw [h₂.hessian, h₁.hessian, List.map_append, List.sum_append]
    abel
  · intro a z hmem
    exact (List.mem_append.mp hmem).elim (h₁.thresholds a z) (h₂.thresholds a z)
  · exact h₂.interior

theorem movementStep_history {s : BallState d} (hs : ActiveInterior s)
    {α : ℝ} (hα : 0 < α) (v : Vec d) :
    let z := s.z - movementStep α (movementMax s v) • v
    let removed := (s.active.filter fun a => decide (a.h ≤ |a.residual z|)).map fun a => (a, z)
    RevocationHistory s (revokeAt s z) removed := by
  let z := s.z - movementStep α (movementMax s v) • v
  let p := fun a : Term d => decide (a.h ≤ |a.residual z|)
  constructor
  · simp [revokeAt]
  · simpa [revokeAt, List.map_map, Function.comp_def, p, z] using List.filter_append_perm p s.active
  · intro x
    simp [revokeAt, List.map_map, Function.comp_def]
  · simp [revokeAt, List.map_map, Function.comp_def]
  · intro a y hmem
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp hmem
    cases heq
    obtain ⟨ha, hhit⟩ := List.mem_filter.mp hb
    exact ⟨of_decide_eq_true hhit, movementStep_residual_lt hs hα v ha⟩
  · exact revokeAt_activeInterior _ _

theorem moveLoop_history (q : Vec d) (fuel : ℕ) (α : ℝ) (s t : BallState d)
    (hs : ActiveInterior s) (hrun : moveLoop q fuel α s = some t) :
    ∃ removed, RevocationHistory s t removed := by
  induction fuel generalizing α s with
  | zero =>
    by_cases h : α ≤ 0
    · have heq : s = t := by simpa [moveLoop, h] using hrun
      subst t
      exact ⟨[], .nil s hs⟩
    · simp [moveLoop, h] at hrun
  | succ fuel ih =>
    by_cases h : α ≤ 0
    · have heq : s = t := by simpa [moveLoop_of_nonpos q _ h s] using hrun
      subst t
      exact ⟨[], .nil s hs⟩
    have hα := lt_of_not_ge h
    cases hv : inverseDirection s.hessian q with
    | none => simp [moveLoop, h, hv] at hrun
    | some v =>
      rw [moveLoop_positive_step q fuel hα s hv] at hrun
      have hhead := movementStep_history hs hα v
      obtain ⟨rest, hrest⟩ := ih _ _ hhead.interior hrun
      exact ⟨_, hhead.append hrest⟩


end Curvature

end
end

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}

theorem Term.curvature_eq_smul_vecMulVec (a : Term d) :
    a.curvature = a.γ • Matrix.vecMulVec a.q a.q := by
  ext i j
  simp [Term.curvature, Matrix.vecMulVec, mul_assoc]


end Curvature

end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def Term.measuredSquare (a : Term d) (ε : ℝ) : ℝ := a.h * ε / 8

theorem createdTerm_measuredSquare {ε : ℝ} (hε : 0 < ε)
    (round : ℕ) (q : Vec d) (moved : BallState d) :
    (createdTerm ε round q moved).measuredSquare ε =
      dotProduct q (moved.hessian⁻¹.mulVec q) := by
  unfold Term.measuredSquare createdTerm
  dsimp only
  field_simp [hε.ne']


theorem activeCurvature_sublist_difference_posSemidef {older active : List (Term d)}
    (hsub : older.Sublist active) (hγ : ∀ a ∈ active, 0 ≤ a.γ) :
    ((active.map Term.curvature).sum - (older.map Term.curvature).sum).PosSemidef := by
  induction hsub with
  | slnil => simp [Matrix.PosSemidef.zero]
  | @cons older active a hsub ih =>
    have htail := ih fun b hb => hγ b (List.mem_cons_of_mem _ hb)
    have hhead := a.curvature_posSemidef (hγ a List.mem_cons_self)
    simp only [List.map_cons, List.sum_cons]
    rw [add_sub_assoc]
    exact hhead.add htail
  | @cons_cons older active a hsub ih =>
    simp only [List.map_cons, List.sum_cons, add_sub_add_left_eq_sub]
    exact ih fun b hb => hγ b (List.mem_cons_of_mem _ hb)


end Curvature

end
end


