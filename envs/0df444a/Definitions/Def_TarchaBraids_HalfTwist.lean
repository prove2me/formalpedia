-- Prove2me | Definitions.Def_TarchaBraids_HalfTwist
-- name    : TarchaBraids_HalfTwist
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-18T23:36:08.475925+00:00
-- url     : https://prove2.me/theorems/d52269d2-54da-440e-92d6-9b5e3394a215
-- title:
--   The elementary half-twist $\sigma_{i+1}$ as a loop in $B_{0,n}E^2$
-- statement:
--   This file makes the elementary braid generator explicit as a
--   loop of point configurations in the plane, so that the presentation theorem can name the images of
--   the abstract generators.
--
--   Fix $n$ and an index $i$ with $0 \le i \le n-2$. All $n$ points start at the base configuration
--   $(1, 2, \dots, n)$. During the time interval $[0,1]$ the two points $i+1$ and $i+2$ rotate
--   counterclockwise through the angle $\pi$ about their common midpoint $i + \tfrac{3}{2}$, at distance
--   $\tfrac12$ from it, while every other point stands still:
--   $$z_i(t) = i + \tfrac32 - \tfrac12\bigl(\cos \pi t + \mathrm{i}\sin \pi t\bigr), \qquad
--   z_{i+1}(t) = i + \tfrac32 + \tfrac12\bigl(\cos \pi t + \mathrm{i}\sin \pi t\bigr),$$
--   and $z_k(t) = k+1$ for $k \neq i, i+1$.
--
--   Three facts are proved here. At every time the $n$ points are pairwise distinct, so the motion stays
--   inside the ordered configuration space: the two moving points are antipodal on a circle of radius
--   $\tfrac12$, and their real parts lie in $[i+1, i+2]$, while every resting point is an integer
--   outside that interval. The motion is continuous in $t$. Finally, at $t = 0$ the configuration is the
--   base configuration, and at $t = 1$ it is the base configuration with the points of index $i$ and
--   $i+1$ interchanged, so after passing to the unordered configuration space $B_{0,n}E^2$ the path is a
--   loop based at the class of $(1,2,\dots,n)$.
--
--   Its homotopy class is an element of $\pi_1(B_{0,n}E^2, *)$: the geometric braid generator
--   $\sigma_{i+1}$ in the sense of Tarcha's Figura 3.16 and of Birman's Chapter 1.
-- source:
--   Alexsander Andrey Gomes Tarcha, *Um Estudo Introdutório da Teoria de Tranças*, Dissertação (Mestrado Profissional em Matemática), IGCE, UNESP, Rio Claro, 2023, orientadora Alice Kimie Miwa Libardi, Seção 3.2.1 e Figura 3.16, pp. 54–55 (geradores de Artin); cf. Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, 1974, Chapter 1, §1.2

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_ArtinEndo

/-!
# The elementary geometric braid `σ_i` as a loop in the configuration space

For the plane `E² = ℂ` with base configuration `(1, 2, …, n)`, the elementary braid `σ_{i+1}`
interchanges the two base points `i + 1` and `i + 2` by rotating them, through an angle `π`,
about their midpoint `i + 3/2`, all other points staying fixed. This file builds that loop in the
unordered configuration space `B_{0,n}E²` and the element of `π₁(B_{0,n}E², *)` it represents.
-/

namespace TarchaBraids

open BraidsLinksMCG

noncomputable section

/-- The point at distance `1/2` from the midpoint `c` in the direction of the angle `π t`,
with sign `s`: `c + s (cos (π t) + i sin (π t))/2`. -/
def twistPoint (c s t : ℝ) : ℂ :=
  ((c + s * Real.cos (Real.pi * t) / 2 : ℝ) : ℂ) +
    ((s * Real.sin (Real.pi * t) / 2 : ℝ) : ℂ) * Complex.I

/-- The position, at time `t`, of the `k`-th point of the elementary half-twist attached to the
braid generator `σ_{i+1}`: the points with indices `i` and `i + 1` rotate about their midpoint
`i + 3/2`, every other point `k` stays at `k + 1`. -/
def halfTwistFun (n : ℕ) (i : Fin (n - 1)) (t : ℝ) (k : Fin n) : ℂ :=
  if (k : ℕ) = (i : ℕ) then twistPoint ((i : ℕ) + 3 / 2) (-1) t
  else if (k : ℕ) = (i : ℕ) + 1 then twistPoint ((i : ℕ) + 3 / 2) 1 t
  else (((k : ℕ) + 1 : ℝ) : ℂ)

@[simp] lemma twistPoint_re (c s t : ℝ) :
    (twistPoint c s t).re = c + s * Real.cos (Real.pi * t) / 2 := by
  simp only [twistPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_self]

@[simp] lemma twistPoint_im (c s t : ℝ) :
    (twistPoint c s t).im = s * Real.sin (Real.pi * t) / 2 := by
  simp only [twistPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

lemma halfTwistFun_of_eq {n : ℕ} {i : Fin (n - 1)} {k : Fin n} (t : ℝ) (h : (k : ℕ) = (i : ℕ)) :
    halfTwistFun n i t k = twistPoint ((i : ℕ) + 3 / 2) (-1) t := by
  simp [halfTwistFun, h]

lemma halfTwistFun_of_eq_succ {n : ℕ} {i : Fin (n - 1)} {k : Fin n} (t : ℝ)
    (_h1 : (k : ℕ) ≠ (i : ℕ)) (h2 : (k : ℕ) = (i : ℕ) + 1) :
    halfTwistFun n i t k = twistPoint ((i : ℕ) + 3 / 2) 1 t := by
  simp [halfTwistFun, h2]

lemma halfTwistFun_of_fixed {n : ℕ} {i : Fin (n - 1)} {k : Fin n} (t : ℝ)
    (h1 : (k : ℕ) ≠ (i : ℕ)) (h2 : (k : ℕ) ≠ (i : ℕ) + 1) :
    halfTwistFun n i t k = (((k : ℕ) + 1 : ℝ) : ℂ) := by
  simp [halfTwistFun, h1, h2]

lemma twistPoint_ne_twistPoint (c t : ℝ) : twistPoint c (-1) t ≠ twistPoint c 1 t := by
  intro h
  have hsin : Real.sin (Real.pi * t) ^ 2 + Real.cos (Real.pi * t) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have h1 : c + (-1) * Real.cos (Real.pi * t) / 2 = c + 1 * Real.cos (Real.pi * t) / 2 := by
    simpa using congrArg Complex.re h
  have h2 : (-1) * Real.sin (Real.pi * t) / 2 = 1 * Real.sin (Real.pi * t) / 2 := by
    simpa using congrArg Complex.im h
  have hc : Real.cos (Real.pi * t) = 0 := by linarith
  have hs : Real.sin (Real.pi * t) = 0 := by linarith
  rw [hc, hs] at hsin
  norm_num at hsin

lemma twistPoint_ne_fixed {n : ℕ} {i : Fin (n - 1)} {k : Fin n} (s t : ℝ)
    (hs1 : -1 ≤ s) (hs2 : s ≤ 1) (h1 : (k : ℕ) ≠ (i : ℕ)) (h2 : (k : ℕ) ≠ (i : ℕ) + 1) :
    twistPoint ((i : ℕ) + 3 / 2) s t ≠ (((k : ℕ) + 1 : ℝ) : ℂ) := by
  intro h
  have hcos := Real.neg_one_le_cos (Real.pi * t)
  have hcos' := Real.cos_le_one (Real.pi * t)
  have hre : ((i : ℕ) : ℝ) + 3 / 2 + s * Real.cos (Real.pi * t) / 2 = ((k : ℕ) : ℝ) + 1 := by
    simpa using congrArg Complex.re h
  have hprod1 : -1 ≤ s * Real.cos (Real.pi * t) := by nlinarith
  have hprod2 : s * Real.cos (Real.pi * t) ≤ 1 := by nlinarith
  have hkl : ((i : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by linarith
  have hkh : ((k : ℕ) : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hkl' : (i : ℕ) ≤ (k : ℕ) := by exact_mod_cast hkl
  have hkh' : (k : ℕ) ≤ (i : ℕ) + 1 := by exact_mod_cast hkh
  omega

lemma halfTwistFun_injective (n : ℕ) (i : Fin (n - 1)) (t : ℝ) :
    Function.Injective (halfTwistFun n i t) := by
  intro k l hkl
  by_cases hk1 : (k : ℕ) = (i : ℕ)
  · by_cases hl1 : (l : ℕ) = (i : ℕ)
    · exact Fin.ext (hk1.trans hl1.symm)
    · by_cases hl2 : (l : ℕ) = (i : ℕ) + 1
      · rw [halfTwistFun_of_eq t hk1, halfTwistFun_of_eq_succ t hl1 hl2] at hkl
        exact absurd hkl (twistPoint_ne_twistPoint _ _)
      · rw [halfTwistFun_of_eq t hk1, halfTwistFun_of_fixed t hl1 hl2] at hkl
        exact absurd hkl (twistPoint_ne_fixed (-1) t (by norm_num) (by norm_num) hl1 hl2)
  · by_cases hk2 : (k : ℕ) = (i : ℕ) + 1
    · by_cases hl1 : (l : ℕ) = (i : ℕ)
      · rw [halfTwistFun_of_eq_succ t hk1 hk2, halfTwistFun_of_eq t hl1] at hkl
        exact absurd hkl.symm (twistPoint_ne_twistPoint _ _)
      · by_cases hl2 : (l : ℕ) = (i : ℕ) + 1
        · exact Fin.ext (hk2.trans hl2.symm)
        · rw [halfTwistFun_of_eq_succ t hk1 hk2, halfTwistFun_of_fixed t hl1 hl2] at hkl
          exact absurd hkl (twistPoint_ne_fixed 1 t (by norm_num) (by norm_num) hl1 hl2)
    · by_cases hl1 : (l : ℕ) = (i : ℕ)
      · rw [halfTwistFun_of_fixed t hk1 hk2, halfTwistFun_of_eq t hl1] at hkl
        exact absurd hkl.symm (twistPoint_ne_fixed (-1) t (by norm_num) (by norm_num) hk1 hk2)
      · by_cases hl2 : (l : ℕ) = (i : ℕ) + 1
        · rw [halfTwistFun_of_fixed t hk1 hk2, halfTwistFun_of_eq_succ t hl1 hl2] at hkl
          exact absurd hkl.symm (twistPoint_ne_fixed 1 t (by norm_num) (by norm_num) hk1 hk2)
        · rw [halfTwistFun_of_fixed t hk1 hk2, halfTwistFun_of_fixed t hl1 hl2] at hkl
          have : ((k : ℕ) : ℝ) + 1 = ((l : ℕ) : ℝ) + 1 := by exact_mod_cast hkl
          have hkl' : ((k : ℕ) : ℝ) = ((l : ℕ) : ℝ) := by linarith
          exact Fin.ext (by exact_mod_cast hkl')

/-- The ordered configuration reached at time `t` by the elementary half-twist `σ_{i+1}`. -/
def halfTwistConfig (n : ℕ) (i : Fin (n - 1)) (t : ℝ) : OrderedConfig n :=
  ⟨halfTwistFun n i t, halfTwistFun_injective n i t⟩

lemma continuous_halfTwistConfig (n : ℕ) (i : Fin (n - 1)) :
    Continuous (halfTwistConfig n i) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun k => ?_
  simp only [halfTwistFun, twistPoint]
  split_ifs
  · fun_prop
  · fun_prop
  · exact continuous_const

lemma halfTwistConfig_zero (n : ℕ) (i : Fin (n - 1)) :
    halfTwistConfig n i 0 = baseOrdered n := by
  apply Subtype.ext
  funext k
  by_cases hk1 : (k : ℕ) = (i : ℕ)
  · rw [show (halfTwistConfig n i 0).1 k = halfTwistFun n i 0 k from rfl,
      halfTwistFun_of_eq 0 hk1]
    simp only [twistPoint, mul_zero, Real.cos_zero, Real.sin_zero]
    simp only [baseOrdered, hk1]
    push_cast
    ring
  · by_cases hk2 : (k : ℕ) = (i : ℕ) + 1
    · rw [show (halfTwistConfig n i 0).1 k = halfTwistFun n i 0 k from rfl,
        halfTwistFun_of_eq_succ 0 hk1 hk2]
      simp only [twistPoint, mul_zero, Real.cos_zero, Real.sin_zero]
      simp only [baseOrdered, hk2]
      push_cast
      ring
    · rw [show (halfTwistConfig n i 0).1 k = halfTwistFun n i 0 k from rfl,
        halfTwistFun_of_fixed 0 hk1 hk2]
      simp only [baseOrdered]
      push_cast
      ring

lemma halfTwistConfig_one (n : ℕ) (i : Fin (n - 1)) :
    (baseOrdered n).1 =
      (halfTwistConfig n i 1).1 ∘ (Equiv.swap (strandIdx i) (strandIdxSucc i)) := by
  have hne : strandIdx i ≠ strandIdxSucc i := by
    intro h
    have := congrArg (fun x : Fin n => (x : ℕ)) h
    simp [strandIdx, strandIdxSucc] at this
  funext k
  simp only [Function.comp_apply]
  by_cases hk : k = strandIdx i
  · subst hk
    rw [Equiv.swap_apply_left]
    rw [show (halfTwistConfig n i 1).1 (strandIdxSucc i) = halfTwistFun n i 1 (strandIdxSucc i)
      from rfl, halfTwistFun_of_eq_succ 1 (by simp [strandIdxSucc]) (by simp [strandIdxSucc])]
    simp only [twistPoint, mul_one, Real.cos_pi, Real.sin_pi]
    simp only [baseOrdered, strandIdx]
    push_cast
    ring
  · by_cases hk' : k = strandIdxSucc i
    · subst hk'
      rw [Equiv.swap_apply_right]
      rw [show (halfTwistConfig n i 1).1 (strandIdx i) = halfTwistFun n i 1 (strandIdx i)
        from rfl, halfTwistFun_of_eq 1 (by simp [strandIdx])]
      simp only [twistPoint, mul_one, Real.cos_pi, Real.sin_pi]
      simp only [baseOrdered, strandIdxSucc]
      push_cast
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
      have h1 : (k : ℕ) ≠ (i : ℕ) := by
        intro h
        exact hk (Fin.ext (by simpa [strandIdx] using h))
      have h2 : (k : ℕ) ≠ (i : ℕ) + 1 := by
        intro h
        exact hk' (Fin.ext (by simpa [strandIdxSucc] using h))
      rw [show (halfTwistConfig n i 1).1 k = halfTwistFun n i 1 k from rfl,
        halfTwistFun_of_fixed 1 h1 h2]
      simp only [baseOrdered]
      push_cast
      ring

/-- The elementary half-twist `σ_{i+1}` as a loop in the unordered configuration space
`B_{0,n}E²`, based at the class of `(1, 2, …, n)`. -/
def halfTwistLoop (n : ℕ) (i : Fin (n - 1)) : Path (baseUnordered n) (baseUnordered n) where
  toFun t := configProj n (halfTwistConfig n i (t : ℝ))
  continuous_toFun :=
    (configProj n).continuous.comp ((continuous_halfTwistConfig n i).comp continuous_subtype_val)
  source' := by
    simp only [Set.Icc.coe_zero, halfTwistConfig_zero]
    rfl
  target' := by
    simp only [Set.Icc.coe_one]
    exact Quotient.sound ⟨Equiv.swap (strandIdx i) (strandIdxSucc i), halfTwistConfig_one n i⟩

/-- The class of the elementary half-twist in the geometric braid group `π₁(B_{0,n}E², *)`. -/
def halfTwistBraid (n : ℕ) (i : Fin (n - 1)) : GeomBraidGroup n :=
  FundamentalGroup.fromPath ⟦halfTwistLoop n i⟧

end

end TarchaBraids


