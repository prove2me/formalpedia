-- Prove2me | Definitions.Def_Curvature_BallState
-- name    : Curvature_BallState
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:08:25.63873+00:00
-- url     : https://prove2.me/theorems/fadcbace-b323-4e0f-821d-9a5caee5652d
-- title:
--   Quadratic regularization terms and one round of Algorithm 1 on the Euclidean unit ball
-- statement:
--   This file defines the state of Algorithm 1 of the paper and one round of its update on the Euclidean unit ball $\mathbb B_2^d$. Points and inputs are vectors in $\mathbb R^d$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\lVert\cdot\rVert_2$, and $\Pi(z)$ denotes the Euclidean projection of $z$ onto $\mathbb B_2^d$.
--
--   A **quadratic regularization term** is given by a creation round, a direction $q\in\mathbb R^d$ and three real parameters (a scalar $m$, a coefficient $\gamma$ and a threshold $h$). When Algorithm 1 adds a term, $m$ is the value of the linear form $x\mapsto\langle q,x\rangle$ at the current iterate. Its residual at $x$ is $\rho(x)\coloneqq\langle q,x\rangle-m$, the term is the function $x\mapsto\frac{\gamma}{2}\rho(x)^2$, and its curvature is the matrix $\gamma qq^\top$. For $\varepsilon>0$, the terms that Algorithm 1 creates have $\gamma>0$ and $h>0$. A state consists of an internal iterate $z$, a regularizer $\Psi$, its Hessian $H$ and the list $\mathcal Q$ of active terms. The initial state has $z=0$, $\Psi(x)=\frac12x^\top Bx$ and $H=B$ with $B=(10\lceil\sqrt d\,\rceil/\varepsilon)I_d$, and no active terms.
--
--   In a round with input $g$, the input is first corrected: if $z\notin\mathbb B_2^d$ and $\langle g,n\rangle<0$ for $n\coloneqq z-\Pi(z)$, the component of $g$ along $n$ is removed. Write $\widetilde g$ for the corrected input. If $\widetilde g=0$, the round returns the state unchanged. Otherwise the iterate moves in partial steps whose weights add up to $1$. Each partial step computes the direction $v\coloneqq H^{-1}\widetilde g$ with the current Hessian $H$ and the rate $L\coloneqq\max_{a\in\mathcal Q}|\langle q_a,v\rangle|/h_a$, with $L=0$ when $\mathcal Q$ is empty, and moves the iterate from $z$ to $z-\alpha v$. The weight $\alpha$ is the whole remaining weight if $L=0$, and the smaller of the remaining weight and $2/L$ if $L>0$. After each partial step, every active term with $|\rho_a(z)|\ge h_a$ at the new iterate $z$ is **revoked**: its curvature $\gamma_aq_aq_a^\top$ is subtracted from $H$, and $\frac{\gamma_a}{2}\langle q_a,x-z\rangle^2$ is subtracted from $\Psi(x)$. After the movement, if $s^2\coloneqq\widetilde g^\top H^{-1}\widetilde g>0$, a new term is added with direction $\widetilde g$, $m=\langle\widetilde g,z\rangle$ at the new iterate, coefficient $\varepsilon^2/(48s^2)$ and threshold $8s^2/\varepsilon$.
--
--   The run on an input sequence is defined round by round. It fails if a required matrix inverse does not exist or if the movement does not finish within one more step than the number of active terms. Theorem 2 shows that it never fails when $d\ge1$, $\varepsilon\in(0,1]$ and every input has norm at most $1$. The prediction of round $t$ is $\Pi(z_t)$. The file also defines the linearized excess loss $\langle g,w-u\rangle$, the objective formed by the regularizer and the past inputs, and the per-round stability that enters the regret identity of the follow-the-regularized-leader analysis. Sections 3.1–3.3 of the paper describe this procedure.
-- source:
--   arXiv:2611.27572v1, Algorithms 1 and 2, p. 7; Sections 3.1–3.3, pp. 5–10. https://arxiv.org/html/2611.27572v1#algorithm1

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
set_option autoImplicit false
noncomputable section
namespace Curvature

abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

variable {d : ℕ}

def norm₂ (x : Vec d) : ℝ := Real.sqrt (dotProduct x x)

def projectBall (z : Vec d) : Vec d :=
  if norm₂ z ≤ 1 then z else (norm₂ z)⁻¹ • z

def correctInput (z g : Vec d) : Vec d :=
  let n := z - projectBall z
  if n = 0 then g else g - (min 0 (dotProduct g n) / norm₂ n ^ 2) • n

structure Term (d : ℕ) where
  round : ℕ
  q : Vec d
  m : ℝ
  γ : ℝ
  h : ℝ

def Term.residual (a : Term d) (x : Vec d) : ℝ := dotProduct a.q x - a.m

def Term.value (a : Term d) (x : Vec d) : ℝ := a.γ / 2 * (a.residual x) ^ 2

def Term.divergence (a : Term d) (x atPoint : Vec d) : ℝ :=
  a.γ / 2 * (dotProduct a.q (x - atPoint)) ^ 2

def Term.curvature (a : Term d) : Mat d := fun i j => a.γ * a.q i * a.q j

structure BallState (d : ℕ) where
  z : Vec d
  regularizer : Vec d → ℝ
  hessian : Mat d
  active : List (Term d)

def dimensionFactor (d : ℕ) : ℝ := (⌈Real.sqrt (d : ℝ)⌉₊ : ℝ)

def initialState (d : ℕ) (ε : ℝ) : BallState d :=
  let b := (10 * dimensionFactor d / ε) • (1 : Mat d)
  { z := 0, regularizer := fun x => dotProduct x (b.mulVec x) / 2,
    hessian := b, active := [] }

def inverseDirection (h : Mat d) (q : Vec d) : Option (Vec d) :=
  if h.det = 0 then none else some (h⁻¹.mulVec q)

def revokeAt (s : BallState d) (z : Vec d) : BallState d :=
  let (removed, kept) := s.active.partition (fun a => decide (a.h ≤ |a.residual z|))
  { z := z
    regularizer := fun x => s.regularizer x - (removed.map fun a => a.divergence x z).sum
    hessian := s.hessian - (removed.map Term.curvature).sum
    active := kept }

def moveLoop (q : Vec d) : ℕ → ℝ → BallState d → Option (BallState d)
  | 0, α, s => if α ≤ 0 then some s else none
  | fuel + 1, α, s => do
    if α ≤ 0 then return s
    let v ← inverseDirection s.hessian q
    let L := s.active.foldl (fun m a => max m (|dotProduct a.q v| / a.h)) 0
    let step := if L = 0 then α else min α (2 / L)
    let s' := revokeAt s (s.z - step • v)
    moveLoop q fuel (α - step) s'

def roundUpdate (ε : ℝ) (round : ℕ) (s : BallState d) (g : Vec d) :
    Option (BallState d) := do
  let q := correctInput s.z g
  if q = 0 then return s
  let moved ← moveLoop q (s.active.length + 1) 1 s
  let v ← inverseDirection moved.hessian q
  let sSq := dotProduct q v
  if 0 < sSq then
    let a : Term d := ⟨round, q, dotProduct q moved.z, ε ^ 2 / (48 * sSq), 8 * sSq / ε⟩
    return { moved with regularizer := fun x => moved.regularizer x + a.value x,
                        hessian := moved.hessian + a.curvature, active := a :: moved.active }
  return moved

def stateAfter (ε : ℝ) (g : ℕ → Vec d) : ℕ → Option (BallState d)
  | 0 => some (initialState d ε)
  | t + 1 => do
    let s ← stateAfter ε g t
    roundUpdate ε (t + 1) s (g t)

def excess (g w u : Vec d) : ℝ := dotProduct g (w - u)

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

theorem Term.curvature_posSemidef (a : Term d) (hγ : 0 ≤ a.γ) :
    a.curvature.PosSemidef := by
  have heq : a.curvature = a.γ • Matrix.vecMulVec a.q (star a.q) := by
    ext i j
    simp [Term.curvature, Matrix.vecMulVec, mul_assoc]
  rw [heq]
  exact (Matrix.posSemidef_vecMulVec_self_star a.q).smul hγ


structure HessianInvariant (B : Mat d) (s : BallState d) : Prop where
  decomposition : s.hessian = B + (s.active.map Term.curvature).sum
  gamma_nonneg : ∀ a ∈ s.active, 0 ≤ a.γ


variable {B : Mat d} {s : BallState d}

theorem HessianInvariant.revokeAt (h : HessianInvariant B s) (z : Vec d) :
    HessianInvariant B (Curvature.revokeAt s z) := by
  let p := fun a : Term d => decide (a.h ≤ |a.residual z|)
  have hsum := ((List.filter_append_perm p s.active).map Term.curvature).sum_eq
  rw [List.map_append, List.sum_append] at hsum
  constructor
  · change s.hessian - ((s.active.partition p).1.map Term.curvature).sum =
        B + ((s.active.partition p).2.map Term.curvature).sum
    rw [List.partition_eq_filter_filter, h.decomposition, ← hsum]
    abel
  · intro a ha
    change a ∈ (s.active.partition p).2 at ha
    rw [List.partition_eq_filter_filter] at ha
    exact h.gamma_nonneg a (List.mem_filter.mp ha).1

theorem HessianInvariant.add (h : HessianInvariant B s) (a : Term d) (ha : 0 ≤ a.γ) :
    HessianInvariant B
      {s with regularizer := fun x => s.regularizer x + a.value x,
              hessian := s.hessian + a.curvature, active := a :: s.active} := by
  constructor
  · simp [h.decomposition, add_comm, add_assoc]
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact h.gamma_nonneg b hb

theorem activeCurvature_posSemidef (active : List (Term d))
    (hγ : ∀ a ∈ active, 0 ≤ a.γ) : (active.map Term.curvature).sum.PosSemidef := by
  induction active with
  | nil => exact Matrix.PosSemidef.zero
  | cons a tail ih =>
    exact (a.curvature_posSemidef (hγ _ List.mem_cons_self)).add
      (ih fun b hb => hγ b (List.mem_cons_of_mem _ hb))

theorem HessianInvariant.posDef (h : HessianInvariant B s) (hB : B.PosDef) :
    s.hessian.PosDef := by
  rw [h.decomposition]
  exact hB.add_posSemidef (activeCurvature_posSemidef _ h.gamma_nonneg)

theorem HessianInvariant.det_ne_zero (h : HessianInvariant B s) (hB : B.PosDef) :
    s.hessian.det ≠ 0 :=
  ((s.hessian.isUnit_iff_isUnit_det).mp (h.posDef hB).isUnit).ne_zero

theorem HessianInvariant.inverseDirection (h : HessianInvariant B s) (hB : B.PosDef)
    (q : Vec d) : Curvature.inverseDirection s.hessian q = some (s.hessian⁻¹.mulVec q) := by
  simp [Curvature.inverseDirection, h.det_ne_zero hB]

theorem HessianInvariant.inverseDirection_pos (h : HessianInvariant B s) (hB : B.PosDef)
    {q : Vec d} (hq : q ≠ 0) : 0 < dotProduct q (s.hessian⁻¹.mulVec q) := by
  simpa using (h.posDef hB).inv.dotProduct_mulVec_pos hq

end Curvature

end
end

section
set_option autoImplicit false
open Matrix
namespace Curvature

theorem inverseQuadratic_mono {d : ℕ} {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (B - A).PosSemidef) (q : Vec d) :
    dotProduct q (B⁻¹.mulVec q) ≤ dotProduct q (A⁻¹.mulVec q) := by
  let x := A⁻¹.mulVec q
  let y := B⁻¹.mulVec q
  have hx : A.mulVec x = q := by
    simp [x, mulVec_mulVec, A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA.isUnit)]
  have hy : B.mulVec y = q := by
    simp [y, mulVec_mulVec, B.mul_nonsing_inv (B.isUnit_iff_isUnit_det.mp hB.isUnit)]
  have hsym : A.transpose = A := by simpa [Matrix.IsHermitian] using hA.isHermitian.eq
  have hcross : dotProduct x (A.mulVec y) = dotProduct q y := by
    have ht := Matrix.vecMul_transpose A x
    rw [hsym, hx] at ht
    rw [dotProduct_mulVec, ht]
  have h₁ := hA.posSemidef.dotProduct_mulVec_nonneg (x - y)
  have h₂ := hAB.dotProduct_mulVec_nonneg y
  simp only [star_trivial, mulVec_sub, sub_dotProduct, dotProduct_sub, hx, hcross] at h₁
  simp only [star_trivial, sub_mulVec, dotProduct_sub, hy] at h₂
  change dotProduct q y ≤ dotProduct q x
  rw [dotProduct_comm x q, dotProduct_comm y q] at h₁
  rw [dotProduct_comm y q] at h₂
  linarith

end Curvature

end

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}

theorem norm₂_nonneg (x : Vec d) : 0 ≤ norm₂ x := Real.sqrt_nonneg _

private theorem dotProduct_self_nonneg (x : Vec d) : 0 ≤ dotProduct x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem norm₂_sq (x : Vec d) : norm₂ x ^ 2 = dotProduct x x :=
  Real.sq_sqrt (dotProduct_self_nonneg x)

theorem norm₂_smul (a : ℝ) (x : Vec d) : norm₂ (a • x) = |a| * norm₂ x := by
  unfold norm₂
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]


theorem signedExcess_mono (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 2) :
    Monotone (fun r : ℝ => 2 * r - ε * |r|) := by
  intro x y hxy
  have habs : |y| - |x| ≤ y - x := by
    have h := abs_add_le (y - x) x
    rw [sub_add_cancel, abs_of_nonneg (sub_nonneg.mpr hxy)] at h
    linarith only [h]
  have hmul := mul_le_mul_of_nonneg_left habs hε
  have hgap := mul_le_mul_of_nonneg_right hε' (sub_nonneg.mpr hxy)
  dsimp
  linarith only [hmul, hgap]


end Curvature

end

section
set_option autoImplicit false
namespace Curvature
variable {d : ℕ}

noncomputable def ftrlObjective (s : ℕ → BallState d) (q : ℕ → Vec d) (t : ℕ) (x : Vec d) : ℝ :=
  (s t).regularizer x + ∑ j ∈ Finset.range t, dotProduct (q j) x

noncomputable def roundStability (s : ℕ → BallState d) (q : ℕ → Vec d) (t : ℕ) : ℝ :=
  ftrlObjective s q t (s t).z + dotProduct (q t) (s t).z -
    ftrlObjective s q (t + 1) (s (t + 1)).z


end Curvature

end


