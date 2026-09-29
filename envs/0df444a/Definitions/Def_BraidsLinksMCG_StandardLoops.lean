-- Prove2me | Definitions.Def_BraidsLinksMCG_StandardLoops
-- name    : BraidsLinksMCG_StandardLoops
-- status  : Definition
-- author  : @cm_beta
-- created : 2026-09-21T22:01:21.331515+00:00
-- url     : https://prove2.me/theorems/55531781-105e-4948-90e5-53694516bff6
-- title:
--   The standard loops of the punctured plane
-- statement:
--   The standard loops of the punctured plane, as explicit paths.
--
--   For each puncture $j$ of $E^2 - Q_n$ this defines the loop $x_j$ that runs out from the base point $n+1$, encircles the $j$-th puncture once counterclockwise at radius $1/2$, and returns along the same route, together with its class `standardGen n j` in $\pi_1(E^2 - Q_n)$.
--
--   These are the loops that freely generate the fundamental group, and they are the objects on which Artin's automorphisms are written: the braid generator $\sigma_i$ acts by $x_i \mapsto x_i x_{i+1} x_i^{-1}$, $x_{i+1} \mapsto x_i$, fixing the rest. Without them named individually, statements about the braid group acting on $\pi_1$ of the punctured plane can only be phrased up to an unspecified isomorphism, which loses exactly the information such statements are for.
--
--   The construction is arranged to keep the side conditions short. The approach is a single parabola
--
--   $$t \;\longmapsto\; (1-t)(n+1) + t\bigl((j+1) + \tfrac12\bigr) \;+\; i\,t(1-t),$$
--
--   whose imaginary part vanishes only at $t = 0$ and $t = 1$. Both endpoints are safely off the puncture set for different reasons: the base point $n+1$ lies strictly to the right of every puncture, since the punctures are $1, \ldots, n$; and the meeting point $(j+1) + \tfrac12$ is a half-integer, hence not an integer. Everywhere in between the path is off the real axis, where no puncture lives. A piecewise approach --- rise, travel, descend --- would need three segments and three separate arguments; the parabola needs one.
--
--   The circle $t \mapsto (j+1) + \tfrac12 e^{2\pi i t}$ needs no case analysis at all: a point at distance exactly $1/2$ from the $j$-th puncture is at distance at least $1/2$ from every other, since distinct punctures are at distance at least $1$.
--
--   Four avoidance lemmas are provided and are reusable on their own: a point off the real axis is never a puncture; a real point that is not of the form $k+1$ is never a puncture; half-integers are never of that form; and the radius-$1/2$ circle about one puncture misses them all.
--
--   This is a definition module, so it asserts nothing. In particular it does not claim that the classes `standardGen n j` generate $\pi_1(E^2 - Q_n)$, still less that they generate it freely; that is the content of `BraidsLinksMCG.puncturedPlaneGroup_equiv_free`, which is reduced to a single van Kampen application.
-- source:
--   Classical; the free generators of the fundamental group of a punctured plane, as used in Artin, Theory of braids, Ann. of Math. 48 (1947), and Birman, Braids, Links and Mapping Class Groups, Chapter 1, equation (1-14).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

/-!
# The standard loops of the punctured plane

For each puncture `j` of `E² - Q_n`, the loop that runs out from the base point `n+1`
along a parabola, encircles the `j`-th puncture once counterclockwise at radius `1/2`,
and returns. These are the loops that freely generate `π₁(E² - Q_n)`, and the ones on
which Artin's automorphisms are written.

The parabolic approach is chosen so that its imaginary part vanishes only at the two
endpoints, both of which are safely off the puncture set: the base point `n+1` lies to
the right of every puncture, and the meeting point `(j+1) + 1/2` is a half-integer.
That avoids splitting the approach into several straight segments.
-/

noncomputable section

namespace BraidsLinksMCG

variable {n : ℕ}

/-- A point off the real axis is never a puncture. -/
lemma not_puncture_of_im_ne (z : ℂ) (hz : z.im ≠ 0) (j : Fin n) :
    z ≠ ((j : ℕ) + 1 : ℂ) := by
  intro h
  apply hz
  rw [h]
  simp

/-- A real point strictly between consecutive integers is never a puncture. -/
lemma not_puncture_of_half (c : ℝ) (hc : ∀ k : ℕ, c ≠ (k : ℝ) + 1) (j : Fin n) :
    (c : ℂ) ≠ ((j : ℕ) + 1 : ℂ) := by
  intro h
  refine hc (j : ℕ) ?_
  have := congrArg Complex.re h
  simpa using this

/-- Half-integers are not of the form `k+1`. -/
lemma half_ne (m : ℕ) (k : ℕ) : ((m : ℝ) + 1 / 2) ≠ (k : ℝ) + 1 := by
  intro h
  have h2 : (2 : ℝ) * m + 1 = 2 * k + 2 := by linarith
  have h3 : (2 * m + 1 : ℕ) = (2 * k + 2 : ℕ) := by exact_mod_cast h2
  omega

/-- Points on the circle of radius `1/2` about a puncture avoid every puncture. -/
lemma not_puncture_of_circle (j : Fin n) (θ : ℝ) (k : Fin n) :
    (((j : ℕ) + 1 : ℂ) + (1/2 : ℂ) * Complex.exp (θ * Complex.I)) ≠ ((k : ℕ) + 1 : ℂ) := by
  intro h
  have hd : (1/2 : ℂ) * Complex.exp (θ * Complex.I)
      = (((k : ℕ) : ℝ) - ((j : ℕ) : ℝ) : ℝ) := by
    push_cast
    linear_combination h
  have h1 : ‖(1/2 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1/2 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    norm_num
  rw [hd, Complex.norm_real] at h1
  rcases eq_or_ne (k : ℕ) (j : ℕ) with hkj | hkj
  · rw [hkj] at h1
    simp at h1
  · have h2 : (1 : ℝ) ≤ |((k : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rcases Nat.lt_or_ge (k : ℕ) (j : ℕ) with hlt | hge
      · have hr : ((k : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hlt2 : (j : ℕ) < (k : ℕ) := lt_of_le_of_ne hge (fun hc => hkj hc.symm)
        have hr : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hlt2
        rw [abs_of_nonneg (by linarith)]
        linarith
    rw [Real.norm_eq_abs] at h1
    linarith

/-- The approach path: a parabola from the base point `n+1` to `(j+1) + 1/2`,
bulging into the upper half plane so it meets the real axis only at its endpoints. -/
noncomputable def approachFun (n : ℕ) (j : Fin n) (t : ℝ) : ℂ :=
  (((1 - t) * ((n : ℝ) + 1) + t * (((j : ℕ) : ℝ) + 1 + 1/2) : ℝ) : ℂ)
    + ((t * (1 - t) : ℝ) : ℂ) * Complex.I

lemma approachFun_im (n : ℕ) (j : Fin n) (t : ℝ) :
    (approachFun n j t).im = t * (1 - t) := by
  simp [approachFun]

lemma approachFun_safe (n : ℕ) (j : Fin n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : Fin n) :
    approachFun n j t ≠ ((k : ℕ) + 1 : ℂ) := by
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · -- t = 0 : the base point `n+1`, which exceeds every puncture
    subst_vars
    intro hc
    have := congrArg Complex.re hc
    simp [approachFun] at this
    have hk := k.isLt
    have : ((k : ℕ) : ℝ) = (n : ℝ) := by linarith
    have : (k : ℕ) = n := by exact_mod_cast this
    omega
  · rcases eq_or_lt_of_le ht1 with h1 | h1
    · -- t = 1 : the half-integer `(j+1) + 1/2`
      subst_vars
      intro hc
      have := congrArg Complex.re hc
      simp [approachFun] at this
      exact half_ne ((j : ℕ) + 1) (k : ℕ) (by push_cast at this ⊢; linarith)
    · -- strictly inside : off the real axis
      refine not_puncture_of_im_ne _ ?_ k
      rw [approachFun_im]
      have : 0 < t * (1 - t) := mul_pos h0 (by linarith)
      linarith

lemma continuous_approachFun (n : ℕ) (j : Fin n) : Continuous (approachFun n j) := by
  unfold approachFun
  fun_prop

/-- The circle of radius `1/2` traversed once counterclockwise about puncture `j`. -/
noncomputable def circleFun (n : ℕ) (j : Fin n) (t : ℝ) : ℂ :=
  ((j : ℕ) + 1 : ℂ) + (1/2 : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

lemma circleFun_safe (n : ℕ) (j : Fin n) (t : ℝ) (k : Fin n) :
    circleFun n j t ≠ ((k : ℕ) + 1 : ℂ) :=
  not_puncture_of_circle j (2 * Real.pi * t) k

lemma continuous_circleFun (n : ℕ) (j : Fin n) : Continuous (circleFun n j) := by
  unfold circleFun
  fun_prop

/-- The point `(j+1) + 1/2`, where the approach meets the circle. -/
noncomputable def halfPt (n : ℕ) (j : Fin n) : PuncturedPlane n :=
  ⟨((((j : ℕ) : ℝ) + 1 + 1/2 : ℝ) : ℂ), fun k => by
    refine not_puncture_of_half _ (fun m => ?_) k
    have h := half_ne ((j : ℕ) + 1) m
    push_cast at h ⊢
    exact h ⟩

noncomputable def approachPath (n : ℕ) (j : Fin n) :
    Path (basePunctured n) (halfPt n j) where
  toFun t := ⟨approachFun n j (t : ℝ), fun k => approachFun_safe n j _ t.2.1 t.2.2 k⟩
  continuous_toFun :=
    Continuous.subtype_mk ((continuous_approachFun n j).comp continuous_subtype_val) _
  source' := by
    apply Subtype.ext
    show approachFun n j ((0 : unitInterval) : ℝ) = _
    simp [approachFun, basePunctured]
  target' := by
    apply Subtype.ext
    show approachFun n j ((1 : unitInterval) : ℝ) = _
    simp [approachFun, halfPt]

noncomputable def circlePath (n : ℕ) (j : Fin n) :
    Path (halfPt n j) (halfPt n j) where
  toFun t := ⟨circleFun n j (t : ℝ), fun k => circleFun_safe n j _ k⟩
  continuous_toFun :=
    Continuous.subtype_mk ((continuous_circleFun n j).comp continuous_subtype_val) _
  source' := by
    apply Subtype.ext
    show circleFun n j ((0 : unitInterval) : ℝ) = _
    simp [circleFun, halfPt]
  target' := by
    apply Subtype.ext
    show circleFun n j ((1 : unitInterval) : ℝ) = _
    simp only [circleFun, Set.Icc.coe_one, mul_one]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
    simp [halfPt]

/-- The `j`-th standard loop of the punctured plane: out along a parabola, once
counterclockwise around the `j`-th puncture, and back. -/
noncomputable def standardLoop (n : ℕ) (j : Fin n) :
    Path (basePunctured n) (basePunctured n) :=
  (approachPath n j).trans ((circlePath n j).trans (approachPath n j).symm)

/-- The class of the `j`-th standard loop in `π₁(E² - Q_n)`. -/
noncomputable def standardGen (n : ℕ) (j : Fin n) : PuncturedPlaneGroup n :=
  FundamentalGroup.fromPath ⟦standardLoop n j⟧

end BraidsLinksMCG



end


