-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
-- name    : OAI_InformationTheory_PhotonNumber_Functions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:14:59.192437+00:00
-- url     : https://prove2.me/theorems/71cc2906-3e32-4926-baf8-f44c2abcf28e
-- title:
--   The functions $x/\sinh x$ and $x\coth x$, and inverting the complex sinc map on a quarter strip
-- statement:
--   This file studies the real functions $x/\sinh x$ and $x\coth x$, defines the parameter inverse $B(s)$ of $s = (x/\sinh x)^2$, and constructs explicit inverses of the complex sinc function $z\mapsto \sin z/z$ on a quarter strip, which give complex extensions of $B$.
--
--   1. **The real functions.** Put
--   $$
--   f(x) = \frac{x}{\sinh x}\ (x\ne0),\quad f(0)=1,\qquad b(x) = f(x)\cosh x,
--   $$
--   so $b(x) = x\coth x$ for $x\ne0$ and $b(0)=1$. Both are even; $f$ is continuous, $0<f(x)\le1$, $f$ is strictly decreasing on $[0,\infty)$ (as is $f^2$), $f(x)\to0$ as $x\to\infty$, and $f([0,\infty)) = (0,1]$. For $x>0$ one has $f(x) = 2xe^{-x}/(1-e^{-2x})$, $\sinh x < x\cosh x$, and for $x\ne0$, $f'(x) = (\sinh x - x\cosh x)/\sinh^2x$. The four-weight target is $T(m,x,y) = m\,f(x)f(y)/f(x+y)$, positive whenever $m>0$.
--
--   2. **The parameter inverse $B$.** For every $s\in(0,1]$ there is a unique $x\ge0$ with $f(x)^2 = s$. The parameter $\beta(s)$ is this $x$ and $B(s) = b(\beta(s))$. Thus $\beta(s)\ge0$ and $f(\beta(s))^2 = s$ for $s\in(0,1]$, $\beta(f(x)^2) = x$ for $x\ge0$, $\beta(1) = 0$ and $B(1) = 1$.
--
--   3. **Complex sinc.** Let $\operatorname{sinc}_{\mathbb C}(z) = \sin z/z$ for $z\ne0$ and $\operatorname{sinc}_{\mathbb C}(0) = 1$; it is analytic at every point of $\mathbb{C}$. With $z = p+iq$: $|\sin z|^2 = \sin^2p+\sinh^2q$, so $\sin z\ne0$ when $q>0$; explicit formulas for $\operatorname{Re}$ and $\operatorname{Im}$ of $\sin z/z$ hold, $\operatorname{Im}(\sin z/z)<0$ when $0<p<\pi$, $q>0$, and the function $z\cos z/\sin z$ has negative imaginary part when $p>0$, $q>0$, so that the derivative of $\sin z/z$ does not vanish there. Also $x^2/2\le\sinh x$ for $x\ge0$ and $\sin p - p\cos p>0$ for $0<p<\pi$.
--
--   4. **A covering lemma.** A covering map from a nonempty preconnected space onto a simply connected, locally path-connected space is bijective.
--
--   5. **The open sine map.** Let
--   $$
--   D = \{z: 0<\operatorname{Re}z<\pi,\ \operatorname{Im}z>0,\ \operatorname{Re}\operatorname{sinc}_{\mathbb C}(z)>0\},\qquad Q = \{w:\operatorname{Re}w>0,\ \operatorname{Im}w<0\},
--   $$
--   and let $S = \{z: 0\le\operatorname{Re}z\le\pi,\ \operatorname{Im}z\ge0\}$ be the closed half-strip. $D$ and $Q$ are open, $S$ is closed, $\operatorname{sinc}_{\mathbb C}$ maps $D$ into $Q$, a point of $S$ whose image lies in $Q$ lies in $D$, and $\operatorname{Im}z\le\pi+4M$ whenever $z\in S$ and $|\operatorname{sinc}_{\mathbb C}(z)|\le M$, so preimages in $S$ of compact sets are compact. Hence $\operatorname{sinc}_{\mathbb C}: D\to Q$ is a proper local homeomorphism and a covering map; $D$ is path-connected (every point is joined horizontally to the line $\operatorname{Re}z = \pi/2$, using that $p\sin p/(-\cos p)$ is strictly decreasing on $(\pi/2,\pi)$) and $Q$ is convex, so the map $D\to Q$ is a bijection. The inverse $\operatorname{sinc}_{\mathbb C}^{-1}(w)$ is this preimage for $w\in Q$ (and $0$ otherwise), and $B^{\mathrm{up}}(s) = \zeta\cos\zeta/\sin\zeta$ with $\zeta = \operatorname{sinc}_{\mathbb C}^{-1}\bigl(1/\sqrt{s}\bigr)$.
--
--   6. **The closed sine map.** Let $\bar Q = \{w:\operatorname{Re}w>0,\ \operatorname{Im}w\le0\}$ and $\bar D = S\cap\operatorname{sinc}_{\mathbb C}^{-1}(\bar Q)$. With $\operatorname{sinhc}(q) = \sinh q/q$ ($\operatorname{sinhc}(0) = 1$), which is strictly increasing on $[0,\infty)$, and the real $\operatorname{sinc}$, strictly decreasing on $[0,\pi]$, one has $\operatorname{sinc}_{\mathbb C}(p) = \operatorname{sinc}(p)$ and $\operatorname{sinc}_{\mathbb C}(iq) = \operatorname{sinhc}(q)$ for real $p,q$. The map $\operatorname{sinc}_{\mathbb C}$ is injective on $\bar D$, and $\operatorname{sinc}_{\mathbb C}:\bar D\to\bar Q$ is a homeomorphism. Its inverse $\Theta(w)$ (set to $0$ for $w\notin\bar Q$) satisfies $\Theta(w)\in\bar D$ and $\operatorname{sinc}_{\mathbb C}(\Theta(w)) = w$ for $w\in\bar Q$, and $\Theta(1) = 0$. With $\operatorname{ccot}(z) = \cos z/\operatorname{sinc}_{\mathbb C}(z)$ ($=z\cot z$ for $z\ne0$, $=1$ at $0$) and the reflection $s^{\uparrow} = \operatorname{Re}s + i\,|\operatorname{Im}s|$, the boundary function is
--   $$
--   B^{\partial}(s) = \operatorname{ccot}\Bigl(\Theta\bigl(1/\sqrt{s^{\uparrow}}\bigr)\Bigr),\qquad B^{\partial}(1) = 1 .
--   $$
--
--   The real function $B$ and its complex counterparts $B^{\mathrm{up}}$, $B^{\partial}$ are the parameter inverses used elsewhere in the development; the bijectivity of the sine maps is what makes these inverses well defined on the whole open, respectively closed, quadrant.
--
--   **Formalization Note** $f$ is `f`, $b$ is `b`, $\beta$ is `bParameter` (defined with `Function.invFunOn` on $[0,\infty)$, so its value outside $(0,1]$ is unspecified), $B^{\mathrm{up}}$ is `upperB`, $\Theta$ is `closedSineInverse` and $B^{\partial}$ is `boundaryB`. $\operatorname{sinc}_{\mathbb C}$ and $\operatorname{sinhc}$ are defined as `dslope` of $\sin$ and $\sinh$ at $0$. The square root is Mathlib's principal `Complex.sqrt` $(a\mapsto a^{1/2})$, and inverses of $0$ are $0$. A private `dite` rewriting lemma is plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Functions.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Functions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber

open Set Filter Topology

def f (x : ℝ) : ℝ := if x = 0 then 1 else x / Real.sinh x

def b (x : ℝ) : ℝ := f x * Real.cosh x

@[simp] theorem f_zero : f 0 = 1 := by simp [f]
@[simp] theorem b_zero : b 0 = 1 := by simp [b]

theorem f_of_ne_zero {x : ℝ} (hx : x ≠ 0) : f x = x / Real.sinh x := by
  simp [f, hx]

@[simp] theorem f_neg (x : ℝ) : f (-x) = f x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [f, hx, Real.sinh_neg]

@[simp] theorem b_neg (x : ℝ) : b (-x) = b x := by
  simp [b, Real.cosh_neg]

theorem f_pos (x : ℝ) : 0 < f x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [← f_neg, f_of_ne_zero (neg_ne_zero.mpr hx.ne)]
    exact div_pos (neg_pos.mpr hx) (Real.sinh_pos_iff.mpr (neg_pos.mpr hx))
  · simp [hx]
  · rw [f_of_ne_zero hx.ne']
    exact div_pos hx (Real.sinh_pos_iff.mpr hx)

def fourWeightTarget (m x y : ℝ) : ℝ := m * f x * f y / f (x + y)

theorem fourWeightTarget_pos {m : ℝ} (hm : 0 < m) (x y : ℝ) :
    0 < fourWeightTarget m x y := by
  exact div_pos (mul_pos (mul_pos hm (f_pos x)) (f_pos y)) (f_pos (x + y))

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric

namespace EntropyPhotonNumber

open Set Filter Topology
theorem f_eq_inv_dslope (x : ℝ) : f x = (dslope Real.sinh 0 x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, dslope_same, Real.deriv_sinh]
  · rw [f_of_ne_zero hx, dslope_of_ne _ hx]
    simp [slope, div_eq_mul_inv, mul_comm]

theorem continuous_f : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change ContinuousAt (fun u => f u) x
  simp_rw [f_eq_inv_dslope]
  apply ContinuousAt.inv₀
  · by_cases hx : x = 0
    · subst x
      exact continuousAt_dslope_same.mpr Real.differentiableAt_sinh
    · exact (continuousAt_dslope_of_ne hx).mpr Real.continuous_sinh.continuousAt
  · by_cases hx : x = 0
    · simp [hx, dslope_same, Real.deriv_sinh]
    · rw [dslope_of_ne _ hx]
      simp [slope, hx, Real.sinh_ne_zero.mpr hx]

theorem f_le_one (x : ℝ) : f x ≤ 1 := by
  have h (y : ℝ) (hy : 0 ≤ y) : f y ≤ 1 := by
    rcases hy.eq_or_lt with hy | hy
    · simp [← hy]
    · rw [f_of_ne_zero hy.ne', div_le_one (Real.sinh_pos_iff.mpr hy)]
      exact Real.self_le_sinh_iff.mpr hy.le
  rcases le_total 0 x with hx | hx
  · exact h x hx
  · simpa using h (-x) (neg_nonneg.mpr hx)

theorem sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) : Real.sinh x < x * Real.cosh x := by
  have hmono : StrictMonoOn (fun u : ℝ => u * Real.cosh u - Real.sinh u) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    intro u hu
    rw [interior_Ici, mem_Ioi] at hu
    have hd := ((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)).sub
      (Real.hasDerivAt_sinh u)
    rw [hd.deriv]
    simpa using mul_pos hu (Real.sinh_pos_iff.mpr hu)
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) hx.le hx
  simpa using h

theorem hasDerivAt_f {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt f ((Real.sinh x - x * Real.cosh x) / Real.sinh x ^ 2) x := by
  have hd := (hasDerivAt_id x).div (Real.hasDerivAt_sinh x) (Real.sinh_ne_zero.mpr hx)
  simp only [one_mul, id_eq] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact f_of_ne_zero hy

theorem strictAntiOn_f : StrictAntiOn f (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) continuous_f.continuousOn
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  rw [(hasDerivAt_f hx.ne').deriv]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (sinh_lt_mul_cosh hx))
    (sq_pos_of_pos (Real.sinh_pos_iff.mpr hx))

theorem strictAntiOn_f_sq : StrictAntiOn (fun u => f u ^ 2) (Ici 0) := by
  intro x hx y hy hxy
  exact sq_lt_sq₀ (f_pos y).le (f_pos x).le |>.mpr (strictAntiOn_f hx hy hxy)

theorem f_eq_exp {x : ℝ} (hx : 0 < x) :
    f x = (2 * (x * Real.exp (-x))) / (1 - Real.exp (-x) ^ 2) := by
  have he : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  have hep : 0 < Real.exp (-x) := Real.exp_pos _
  have hden : 1 - Real.exp (-x) ^ 2 ≠ 0 := by nlinarith
  rw [f_of_ne_zero hx.ne', Real.sinh_eq]
  have hs : Real.exp x - Real.exp (-x) ≠ 0 := by
    have : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    rw [Real.sinh_eq] at this
    linarith
  have hm : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  nlinarith [congrArg (fun t : ℝ => 2 * x * t) hm]

theorem tendsto_f_atTop : Tendsto f atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hxe : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hfrac := (hxe.const_mul 2).div (tendsto_const_nhds.sub (he.pow 2))
    (show (1 : ℝ) - 0 ^ 2 ≠ 0 by norm_num)
  have heq : f =ᶠ[atTop] (fun x : ℝ => (2 * (x * Real.exp (-x))) / (1 - Real.exp (-x) ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact f_eq_exp hx
  have ht : Tendsto (fun x : ℝ => (2 * (x * Real.exp (-x))) /
      (1 - Real.exp (-x) ^ 2)) atTop (𝓝 0) := by
    convert! hfrac using 1; norm_num
  exact ht.congr' heq.symm

theorem range_f_nonneg : f '' Ici 0 = Ioc 0 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨f_pos x, f_le_one x⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ : ∃ x : ℝ, 0 ≤ x ∧ f x < y := by
      have h := (tendsto_order.mp tendsto_f_atTop).2 y hy.1
      obtain ⟨x, hx, hxy⟩ := (eventually_ge_atTop (0 : ℝ)).and h |>.exists
      exact ⟨x, hx, hxy⟩
    have hsurj := continuous_f.continuousOn.surjOn_Icc
      (s := Ici (0 : ℝ)) hx (show (0 : ℝ) ∈ Ici 0 by simp)
    exact hsurj ⟨hxy.le, by simpa using hy.2⟩

theorem existsUnique_f_sq_parameter {s : ℝ} (hs : s ∈ Ioc 0 1) :
    ∃! x : ℝ, 0 ≤ x ∧ f x ^ 2 = s := by
  have hroot : Real.sqrt s ∈ f '' Ici 0 := by
    rw [range_f_nonneg]
    exact ⟨Real.sqrt_pos.2 hs.1, Real.sqrt_le_one.2 hs.2⟩
  obtain ⟨x, hx, hfx⟩ := hroot
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · rw [hfx, Real.sq_sqrt hs.1.le]
  · intro y hy
    apply strictAntiOn_f_sq.injOn hy.1 hx
    change f y ^ 2 = f x ^ 2
    rw [hy.2, hfx, Real.sq_sqrt hs.1.le]

def bParameter (s : ℝ) : ℝ := Function.invFunOn (fun x : ℝ => f x ^ 2) (Ici 0) s

def B (s : ℝ) : ℝ := b (bParameter s)

theorem bParameter_nonneg {s : ℝ} (hs : s ∈ Ioc 0 1) : 0 ≤ bParameter s := by
  apply Function.invFunOn_mem
  obtain ⟨x, hx, _⟩ := existsUnique_f_sq_parameter hs
  exact ⟨x, hx⟩

theorem f_sq_bParameter {s : ℝ} (hs : s ∈ Ioc 0 1) : f (bParameter s) ^ 2 = s := by
  change (fun x : ℝ => f x ^ 2) (Function.invFunOn (fun x : ℝ => f x ^ 2) (Ici 0) s) = s
  apply Function.invFunOn_eq (f := fun x : ℝ => f x ^ 2) (s := Ici (0 : ℝ))
  obtain ⟨x, hx, _⟩ := existsUnique_f_sq_parameter hs
  exact ⟨x, hx⟩

theorem f_sq_mem {x : ℝ} (_hx : 0 ≤ x) : f x ^ 2 ∈ Ioc (0 : ℝ) 1 := by
  exact ⟨sq_pos_of_pos (f_pos x), by nlinarith [f_pos x, f_le_one x]⟩

theorem bParameter_f_sq {x : ℝ} (hx : 0 ≤ x) : bParameter (f x ^ 2) = x := by
  apply strictAntiOn_f_sq.injOn (bParameter_nonneg (f_sq_mem hx)) hx
  exact f_sq_bParameter (f_sq_mem hx)

@[simp] theorem bParameter_one : bParameter 1 = 0 := by
  simpa using bParameter_f_sq (x := 0) le_rfl

@[simp] theorem B_one : B 1 = 1 := by simp [B]

def sineParameter (z : ℂ) : ℂ := Complex.sin z / z

def cotParameter (z : ℂ) : ℂ := z * Complex.cos z / Complex.sin z

theorem normSq_sin (z : ℂ) :
    Complex.normSq (Complex.sin z) = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sin_eq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.cosh_ofReal_re,
    Complex.cosh_ofReal_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    mul_one]
  have ht := Real.sin_sq_add_cos_sq z.re
  have hh := Real.cosh_sq_sub_sinh_sq z.im
  nlinarith [congrArg (fun t : ℝ => Real.sin z.re ^ 2 * t) hh,
    congrArg (fun t : ℝ => Real.sinh z.im ^ 2 * t) ht]

theorem sin_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : Complex.sin z ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [normSq_sin]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (Real.sinh_pos_iff.mpr hz))

theorem cotParameter_im (z : ℂ) :
    (cotParameter z).im =
      (z.im * Real.sin z.re * Real.cos z.re - z.re * Real.sinh z.im * Real.cosh z.im) /
        (Real.sin z.re ^ 2 + Real.sinh z.im ^ 2) := by
  dsimp [cotParameter]
  rw [Complex.div_im, normSq_sin, Complex.sin_eq, Complex.cos_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, mul_one, zero_sub]
  rw [← sub_div]
  congr 1
  have ht := Real.sin_sq_add_cos_sq z.re
  have hh := Real.cosh_sq_sub_sinh_sq z.im
  nlinarith [congrArg (fun t : ℝ => z.im * Real.sin z.re * Real.cos z.re * t) hh,
    congrArg (fun t : ℝ => z.re * Real.sinh z.im * Real.cosh z.im * t) ht]

theorem cotParameter_im_neg {z : ℂ} (hr : 0 < z.re) (hi : 0 < z.im) :
    (cotParameter z).im < 0 := by
  rw [cotParameter_im]
  apply div_neg_of_neg_of_pos
  · have ht := Real.sin_le (show 0 ≤ 2 * z.re by positivity)
    have hh := Real.self_lt_sinh_iff.mpr (show 0 < 2 * z.im by positivity)
    rw [Real.sin_two_mul] at ht
    rw [Real.sinh_two_mul] at hh
    nlinarith [mul_le_mul_of_nonneg_left ht hi.le, mul_lt_mul_of_pos_left hh hr]
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr hi))

theorem hasDerivAt_sineParameter {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt sineParameter ((z * Complex.cos z - Complex.sin z) / z ^ 2) z := by
  convert! (Complex.hasDerivAt_sin z).div (hasDerivAt_id z) hz using 1
  simp [mul_comm]

theorem deriv_sineParameter_ne_zero {z : ℂ} (hr : 0 < z.re) (hi : 0 < z.im) :
    deriv sineParameter z ≠ 0 := by
  have hz : z ≠ 0 := by intro h; simp [h] at hr
  rw [(hasDerivAt_sineParameter hz).deriv]
  apply div_ne_zero _ (pow_ne_zero _ hz)
  intro h
  have hc : cotParameter z = 1 := by
    dsimp [cotParameter]
    rw [sub_eq_zero.mp h, div_self (sin_ne_zero_of_im_pos hi)]
  have hn := cotParameter_im_neg hr hi
  simp [hc] at hn

theorem covering_bijective_of_simplyConnected
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) : Function.Bijective p := by
  classical
  let e₀ : E := Classical.choice inferInstance
  obtain ⟨F, ⟨hF₀, hF⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) (p e₀) e₀ rfl
  have hright : p ∘ F = id := hF
  have hleft : F ∘ p = id := by
    apply hp.eq_of_comp_eq (F.continuous.comp hp.continuous) continuous_id _ e₀ hF₀
    ext e
    exact congrFun hright (p e)
  constructor
  · intro e e' h
    have he := congrFun hleft e
    have he' := congrFun hleft e'
    change F (p e) = e at he
    change F (p e') = e' at he'
    exact he.symm.trans ((congrArg F h).trans he')
  · intro x
    exact ⟨F x, congrFun hright x⟩

def csinc : ℂ → ℂ := dslope Complex.sin 0

theorem csinc_zero : csinc 0 = 1 := by
  rw [csinc, dslope_same, (Complex.hasDerivAt_sin 0).deriv]
  simp

theorem csinc_of_ne {z : ℂ} (hz : z ≠ 0) : csinc z = sineParameter z := by
  simp [csinc, dslope_of_ne _ hz, slope, sineParameter, div_eq_mul_inv, mul_comm]

theorem analyticAt_csinc (z : ℂ) : AnalyticAt ℂ csinc z := by
  rcases eq_or_ne z 0 with rfl | hz
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (differentiableAt_dslope_of_ne hz).mpr (Complex.differentiableAt_sin)
    · exact continuousAt_dslope_same.mpr (Complex.differentiableAt_sin)
  · have he : csinc =ᶠ[𝓝 z] sineParameter := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact csinc_of_ne hw
    exact ((Complex.analyticAt_sin).div analyticAt_id hz).congr he.symm

theorem continuous_csinc : Continuous csinc := continuous_iff_continuousAt.mpr
  (fun z => (analyticAt_csinc z).continuousAt)

theorem sin_sub_mul_cos_pos {p : ℝ} (hp : p ∈ Ioo 0 Real.pi) :
    0 < Real.sin p - p * Real.cos p := by
  have hm : StrictMonoOn (fun u : ℝ => Real.sin u - u * Real.cos u) (Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
      (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
    intro u hu
    rw [interior_Icc, mem_Ioo] at hu
    have hd := (Real.hasDerivAt_sin u).sub ((hasDerivAt_id u).mul (Real.hasDerivAt_cos u))
    rw [hd.deriv]
    have hs := Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2
    simp only [id_eq] at *
    nlinarith [mul_pos hu.1 hs]
  have he := hm (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    ⟨hp.1.le, hp.2.le⟩ hp.1
  simpa using he

theorem sineParameter_re (z : ℂ) :
    (sineParameter z).re =
      (z.re * Real.sin z.re * Real.cosh z.im + z.im * Real.cos z.re * Real.sinh z.im) /
        (z.re ^ 2 + z.im ^ 2) := by
  rw [sineParameter, Complex.div_re, Complex.sin_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_one, Complex.normSq_apply]
  ring

theorem sineParameter_im (z : ℂ) :
    (sineParameter z).im =
      (z.re * Real.cos z.re * Real.sinh z.im - z.im * Real.sin z.re * Real.cosh z.im) /
        (z.re ^ 2 + z.im ^ 2) := by
  rw [sineParameter, Complex.div_im, Complex.sin_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_one, Complex.normSq_apply]
  ring

theorem sineParameter_im_neg {z : ℂ} (hp : z.re ∈ Ioo 0 Real.pi) (hq : 0 < z.im) :
    (sineParameter z).im < 0 := by
  rw [sineParameter_im]
  have hs := Real.sin_pos_of_pos_of_lt_pi hp.1 hp.2
  have hsh := Real.sinh_pos_iff.mpr hq
  have hch := Real.cosh_pos z.im
  apply div_neg_of_neg_of_pos _ (add_pos_of_pos_of_nonneg (sq_pos_of_pos hp.1) (sq_nonneg _))
  rcases le_or_gt (Real.cos z.re) 0 with hc | hc
  · have h₁ := mul_nonpos_of_nonneg_of_nonpos hp.1.le hc
    have h₂ := mul_nonpos_of_nonpos_of_nonneg h₁ hsh.le
    have h₃ := mul_pos (mul_pos hq hs) hch
    linarith
  · have h₁ := sinh_lt_mul_cosh hq
    have h₂ := sin_sub_mul_cos_pos hp
    have h₃ := mul_lt_mul_of_pos_left h₁ (mul_pos hp.1 hc)
    have h₄ := mul_lt_mul_of_pos_right (sub_pos.mp h₂) (mul_pos hq hch)
    nlinarith

theorem half_sq_le_sinh {x : ℝ} (hx : 0 ≤ x) : x ^ 2 / 2 ≤ Real.sinh x := by
  have hm : MonotoneOn (fun u : ℝ => Real.sinh u - u ^ 2 / 2) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (Real.continuous_sinh.sub ((continuous_id.pow 2).div_const 2)).continuousOn
    · intro u hu
      exact ((Real.differentiableAt_sinh).sub
        ((differentiableAt_id.pow 2).div_const 2)).differentiableWithinAt
    · intro u hu
      rw [interior_Ici, mem_Ioi] at hu
      rw [((Real.hasDerivAt_sinh u).sub
        ((hasDerivAt_id u).pow 2 |>.div_const 2)).deriv]
      have h₁ := Real.self_le_sinh_iff.mpr hu.le
      have h₂ := Real.sinh_lt_cosh u
      simp only [id_eq, mul_one]
      linarith
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  simpa using h

def sineDomain : Set ℂ := {z | 0 < z.re ∧ z.re < Real.pi ∧ 0 < z.im ∧ 0 < (csinc z).re}
def sineQuadrant : Set ℂ := {z | 0 < z.re ∧ z.im < 0}
def sineStrip : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ Real.pi ∧ 0 ≤ z.im}

theorem isOpen_sineDomain : IsOpen sineDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_csinc))))

theorem isOpen_sineQuadrant : IsOpen sineQuadrant :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem isClosed_sineStrip : IsClosed sineStrip :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im))

theorem csinc_mapsTo : MapsTo csinc sineDomain sineQuadrant := by
  intro z hz
  refine ⟨hz.2.2.2, ?_⟩
  rw [csinc_of_ne (by intro he; have := hz.1; simp [he] at this)]
  exact sineParameter_im_neg ⟨hz.1, hz.2.1⟩ hz.2.2.1

theorem csinc_strip_bound {z : ℂ} (hz : z ∈ sineStrip) {M : ℝ} (hM : ‖csinc z‖ ≤ M) :
    z.im ≤ Real.pi + 4 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  by_contra! hq
  have hz0 : z ≠ 0 := by
    intro he
    simp only [he, Complex.zero_im] at hq
    linarith [Real.pi_pos]
  have hn : Real.sinh z.im ≤ ‖Complex.sin z‖ := by
    have hnorm := Complex.normSq_eq_norm_sq (Complex.sin z)
    rw [normSq_sin] at hnorm
    nlinarith [norm_nonneg (Complex.sin z), Real.sinh_nonneg_iff.mpr hz.2.2,
      sq_nonneg (Real.sin z.re)]
  have hzbound : ‖z‖ ≤ Real.pi + z.im := by
    have he := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hz.1, abs_of_nonneg hz.2.2] at he
    linarith [hz.2.1]
  have he : ‖Complex.sin z‖ = ‖csinc z‖ * ‖z‖ := by
    rw [csinc_of_ne hz0, sineParameter, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz0)]
  have hsq := half_sq_le_sinh hz.2.2
  have hu : z.im ^ 2 / 2 ≤ M * (Real.pi + z.im) :=
    hsq.trans (hn.trans (he ▸ mul_le_mul hM hzbound (norm_nonneg _) hM0))
  have hqp : Real.pi < z.im := by linarith
  have hqm : 4 * M < z.im := by linarith [Real.pi_pos]
  have hpos : 0 < z.im := Real.pi_pos.trans hqp
  nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hqp.le), mul_pos hpos (sub_pos.mpr hqm)]

theorem csinc_strip_quadrant {z : ℂ} (hz : z ∈ sineStrip)
    (ha : csinc z ∈ sineQuadrant) : z ∈ sineDomain := by
  have hz0 : z ≠ 0 := by intro he; simp [he, csinc_zero, sineQuadrant] at ha
  have he := csinc_of_ne hz0
  have hi := ha.2
  have hr := ha.1
  rw [he, sineParameter_im] at hi
  rw [he, sineParameter_re] at hr
  refine ⟨?_, ?_, ?_, ha.1⟩
  · by_contra! h
    have hp : z.re = 0 := le_antisymm h hz.1
    simp [hp] at hi
  · by_contra! h
    have hp : z.re = Real.pi := le_antisymm hz.2.1 h
    simp [hp] at hr
    have : -(z.im * Real.sinh z.im) / (Real.pi ^ 2 + z.im ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
        (mul_nonneg hz.2.2 (Real.sinh_nonneg_iff.mpr hz.2.2))) (by positivity)
    linarith
  · by_contra! h
    have hq : z.im = 0 := le_antisymm h hz.2.2
    simp [hq] at hi

theorem isCompact_strip_preimage {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (sineStrip ∩ csinc ⁻¹' K) := by
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_sineStrip.inter (hK.isClosed.preimage continuous_csinc))
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨Real.pi + (Real.pi + 4 * M), ?_⟩
  intro z hz
  have he := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hz.1.1, abs_of_nonneg hz.1.2.2] at he
  linarith [hz.1.2.1, csinc_strip_bound hz.1 (hM _ hz.2)]

def sineMap : sineDomain → sineQuadrant := fun z => ⟨csinc z, csinc_mapsTo z.property⟩

theorem continuous_sineMap : Continuous sineMap :=
  (continuous_csinc.comp continuous_subtype_val).subtype_mk _

theorem proper_sineMap : IsProperMap sineMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_sineMap, ?_⟩
  intro K hK
  have hc := isCompact_strip_preimage (hK.image continuous_subtype_val)
  have he : Subtype.val '' (sineMap ⁻¹' K) = sineStrip ∩ csinc ⁻¹' (Subtype.val '' K) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u.property.1.le, u.property.2.1.le, u.property.2.2.1.le⟩, _, hu, rfl⟩
    · rintro ⟨hz, w, hw, he⟩
      have ha : csinc z ∈ sineQuadrant := he ▸ w.property
      refine ⟨⟨z, csinc_strip_quadrant hz ha⟩, ?_, rfl⟩
      have hw' : sineMap ⟨z, csinc_strip_quadrant hz ha⟩ = w := Subtype.ext he.symm
      simpa [hw'] using hw
  exact (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr (he ▸ hc)

theorem deriv_csinc_ne_zero {z : ℂ} (hz : z ∈ sineDomain) : deriv csinc z ≠ 0 := by
  have hn : z ≠ 0 := by intro he; have := hz.1; simp [he] at this
  have he : csinc =ᶠ[𝓝 z] sineParameter := by
    filter_upwards [eventually_ne_nhds hn] with w hw
    exact csinc_of_ne hw
  rw [he.deriv_eq]
  exact deriv_sineParameter_ne_zero hz.1 hz.2.2.1

theorem localHomeomorphOn_csinc : IsLocalHomeomorphOn csinc sineDomain := by
  intro z hz
  let hd := (analyticAt_csinc z).hasStrictDerivAt.hasStrictFDerivAt_equiv
    (deriv_csinc_ne_zero hz)
  exact ⟨hd.toOpenPartialHomeomorph csinc, hd.mem_toOpenPartialHomeomorph_source,
    hd.toOpenPartialHomeomorph_coe.symm⟩

theorem localHomeomorph_sineMap : IsLocalHomeomorph sineMap := by
  have hi := isOpen_sineDomain.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have ho := isOpen_sineQuadrant.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hc : IsLocalHomeomorph (csinc ∘ (Subtype.val : sineDomain → ℂ)) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    exact localHomeomorphOn_csinc.comp hi.isLocalHomeomorphOn (fun x _ => x.property)
  change IsLocalHomeomorph ((Subtype.val : sineQuadrant → ℂ) ∘ sineMap) at hc
  exact hc.of_comp ho continuous_sineMap

theorem covering_sineMap : IsCoveringMap sineMap := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply proper_sineMap.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro x _
    apply (proper_sineMap.isCompact_preimage isCompact_singleton).finite
    apply (show IsLocalHomeomorphOn sineMap (sineMap ⁻¹' {x}) from
      fun z _ => localHomeomorph_sineMap z).isDiscrete_of_image
    exact ((Set.finite_singleton x).subset (Set.image_preimage_subset _ _)).isDiscrete
  · exact localHomeomorph_sineMap.isLocalHomeomorphOn

theorem strictAnti_boundaryRatio :
    StrictAntiOn (fun p : ℝ => p * Real.sin p / (-Real.cos p))
      (Ioo (Real.pi / 2) Real.pi) := by
  have hc : ∀ p ∈ Ioo (Real.pi / 2) Real.pi, Real.cos p < 0 := by
    intro p hp
    exact Real.cos_neg_of_pi_div_two_lt_of_lt hp.1 (by linarith [hp.2, Real.pi_pos])
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · apply ContinuousOn.div
    · exact (continuous_id.mul Real.continuous_sin).continuousOn
    · exact Real.continuous_cos.neg.continuousOn
    · intro p hp
      exact neg_ne_zero.mpr (ne_of_lt (hc p hp))
  · intro p hp
    rw [interior_Ioo] at hp
    have hn : -Real.cos p ≠ 0 := neg_ne_zero.mpr (ne_of_lt (hc p hp))
    have hd := ((hasDerivAt_id p).mul (Real.hasDerivAt_sin p)).div
      (Real.hasDerivAt_cos p).neg hn
    simp only [Pi.mul_apply, Pi.neg_apply, id_eq] at hd
    change deriv (id * Real.sin / -Real.cos) p < 0
    rw [hd.deriv]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_ne_zero hn)
    simp only [one_mul, neg_neg]
    have hs := Real.sin_sq_add_cos_sq p
    have hq := sq_nonneg (Real.sin p + Real.cos p)
    have hp1 : 1 < p := by linarith [hp.1, Real.pi_gt_three]
    nlinarith

theorem csinc_re_pos_of_small_re {z : ℂ} (hp : 0 < z.re)
    (hp' : z.re ≤ Real.pi / 2) (hq : 0 < z.im) : 0 < (csinc z).re := by
  rw [csinc_of_ne (by intro h; simp [h] at hp), sineParameter_re]
  apply div_pos _ (add_pos_of_pos_of_nonneg (sq_pos_of_pos hp) (sq_nonneg _))
  have hsin := Real.sin_pos_of_pos_of_lt_pi hp (by linarith [Real.pi_pos])
  have hcos := Real.cos_nonneg_of_mem_Icc (show z.re ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
    from ⟨by linarith [Real.pi_pos], hp'⟩)
  exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hp hsin) (Real.cosh_pos _))
    (mul_nonneg (mul_nonneg hq.le hcos) (Real.sinh_nonneg_iff.mpr hq.le))

theorem csinc_re_pos_iff_of_large_re {z : ℂ} (hp : Real.pi / 2 < z.re)
    (hp' : z.re < Real.pi) (_hq : 0 < z.im) :
    0 < (csinc z).re ↔ z.im * Real.sinh z.im / Real.cosh z.im <
      z.re * Real.sin z.re / (-Real.cos z.re) := by
  have hp0 : 0 < z.re := by linarith [Real.pi_pos]
  have hcos := Real.cos_neg_of_pi_div_two_lt_of_lt hp (show z.re < Real.pi + Real.pi / 2 by
    linarith [Real.pi_pos])
  rw [csinc_of_ne (by intro h; simp [h] at hp0), sineParameter_re,
    div_pos_iff_of_pos_right (add_pos_of_pos_of_nonneg (sq_pos_of_pos hp0) (sq_nonneg _)),
    div_lt_div_iff₀ (Real.cosh_pos _) (neg_pos.mpr hcos)]
  constructor <;> intro h <;> nlinarith

theorem sineDomain_horizontal {z w : ℂ} (hz : z ∈ sineDomain)
    (hi : w.im = z.im) (hp : 0 < w.re)
    (hl : w.re ≤ max (Real.pi / 2) z.re) : w ∈ sineDomain := by
  have hpi : w.re < Real.pi := lt_of_le_of_lt hl
    (max_lt (by linarith [Real.pi_pos]) hz.2.1)
  refine ⟨hp, hpi, hi ▸ hz.2.2.1, ?_⟩
  by_cases hs : w.re ≤ Real.pi / 2
  · exact csinc_re_pos_of_small_re hp hs (hi ▸ hz.2.2.1)
  · have hs' : Real.pi / 2 < w.re := lt_of_not_ge hs
    have hz' : Real.pi / 2 < z.re := by
      by_contra! hn
      rw [max_eq_left hn] at hl
      exact hs hl
    rw [csinc_re_pos_iff_of_large_re hs' hpi (hi ▸ hz.2.2.1)]
    have hzr := (csinc_re_pos_iff_of_large_re hz' hz.2.1 hz.2.2.1).mp hz.2.2.2
    rw [hi]
    apply lt_of_lt_of_le hzr
    apply strictAnti_boundaryRatio.antitoneOn ⟨hs', hpi⟩ ⟨hz', hz.2.1⟩
    simpa [max_eq_right hz'.le] using hl

def sineMidPoint (q : ℝ) : ℂ := ⟨Real.pi / 2, q⟩

theorem sineMidPoint_mem {q : ℝ} (hq : 0 < q) : sineMidPoint q ∈ sineDomain := by
  have hp : 0 < Real.pi / 2 := by positivity
  refine ⟨hp, by dsimp [sineMidPoint]; linarith [Real.pi_pos], hq, ?_⟩
  exact csinc_re_pos_of_small_re hp le_rfl hq

theorem joined_horizontal {z : ℂ} (hz : z ∈ sineDomain) :
    JoinedIn sineDomain z (sineMidPoint z.im) := by
  apply JoinedIn.of_segment_subset
  intro w hw
  have hp : 0 < w.re := (convex_halfSpace_re_gt 0).segment_subset
    hz.1 (show 0 < (sineMidPoint z.im).re by dsimp [sineMidPoint]; positivity) hw
  have hl : w.re ≤ max (Real.pi / 2) z.re :=
    (convex_halfSpace_re_le (max (Real.pi / 2) z.re)).segment_subset
      (show z.re ≤ max (Real.pi / 2) z.re from le_max_right _ _) (show (sineMidPoint z.im).re ≤ max (Real.pi / 2) z.re from le_max_left _ _) hw
  apply sineDomain_horizontal hz _ hp hl
  rcases hw with ⟨a, b, ha, hb, hab, rfl⟩
  simp only [Complex.add_im, Complex.smul_im, sineMidPoint, smul_eq_mul]
  rw [← add_mul, hab, one_mul]

theorem joined_sineMidPoints {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    JoinedIn sineDomain (sineMidPoint q) (sineMidPoint r) := by
  apply JoinedIn.of_segment_subset
  intro w hw
  have hi : 0 < w.im := (convex_halfSpace_im_gt 0).segment_subset hq hr hw
  have he : w = sineMidPoint w.im := by
    apply Complex.ext
    · rcases hw with ⟨a, b, ha, hb, hab, rfl⟩
      simp only [Complex.add_re, Complex.smul_re, sineMidPoint, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    · rfl
  rw [he]
  exact sineMidPoint_mem hi

theorem isPathConnected_sineDomain : IsPathConnected sineDomain := by
  refine ⟨sineMidPoint 1, sineMidPoint_mem zero_lt_one, ?_⟩
  intro z hz
  exact (joined_sineMidPoints zero_lt_one hz.2.2.1).trans (joined_horizontal hz).symm

theorem convex_sineQuadrant : Convex ℝ sineQuadrant :=
  (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)

theorem bijective_sineMap : Function.Bijective sineMap := by
  let : PathConnectedSpace sineDomain :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_sineDomain
  let : ContractibleSpace sineQuadrant := convex_sineQuadrant.contractibleSpace
    ⟨⟨1, -1⟩, by constructor <;> norm_num⟩
  let : LocallyPathConnectedSpace sineQuadrant := convex_sineQuadrant.locallyPathConnectedSpace
  exact covering_bijective_of_simplyConnected covering_sineMap

def sineInverse (w : ℂ) : ℂ := by
  classical
  exact if hw : w ∈ sineQuadrant then
    ((Equiv.ofBijective sineMap bijective_sineMap).symm ⟨w, hw⟩).val
  else 0

def upperB (s : ℂ) : ℂ := cotParameter (sineInverse (Complex.sqrt s)⁻¹)

def sinhc : ℝ → ℝ := dslope Real.sinh 0

@[simp] theorem sinhc_zero : sinhc 0 = 1 := by
  simp [sinhc, dslope_same, (Real.hasDerivAt_sinh 0).deriv]

theorem sinhc_of_ne {q : ℝ} (hq : q ≠ 0) : sinhc q = Real.sinh q / q := by
  simp [sinhc, dslope_of_ne _ hq, slope, div_eq_mul_inv, mul_comm]

theorem continuous_sinhc : Continuous sinhc := by
  apply continuous_iff_continuousAt.mpr
  intro q
  rcases eq_or_ne q 0 with rfl | hq
  · exact continuousAt_dslope_same.mpr Real.differentiableAt_sinh
  · exact (continuousAt_dslope_of_ne hq).mpr Real.continuous_sinh.continuousAt

theorem strictMonoOn_sinhc : StrictMonoOn sinhc (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) continuous_sinhc.continuousOn
  intro q hq
  rw [interior_Ici, mem_Ioi] at hq
  have he : sinhc =ᶠ[𝓝 q] fun x => Real.sinh x / x := by
    filter_upwards [eventually_ne_nhds hq.ne'] with x hx
    exact sinhc_of_ne hx
  rw [he.deriv_eq]
  change 0 < deriv (Real.sinh / id) q
  rw [((Real.hasDerivAt_sinh q).div (hasDerivAt_id q) hq.ne').deriv]
  simpa only [one_mul, mul_one, mul_comm, id_eq] using
    div_pos (sub_pos.mpr (sinh_lt_mul_cosh hq)) (sq_pos_of_pos hq)

theorem strictAntiOn_sinc : StrictAntiOn Real.sinc (Icc 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 Real.pi) Real.continuous_sinc.continuousOn
  intro p hp
  rw [interior_Icc, mem_Ioo] at hp
  have he : Real.sinc =ᶠ[𝓝 p] fun x => Real.sin x / x := by
    filter_upwards [eventually_ne_nhds hp.1.ne'] with x hx
    exact Real.sinc_of_ne_zero hx
  rw [he.deriv_eq]
  change deriv (Real.sin / id) p < 0
  rw [((Real.hasDerivAt_sin p).div (hasDerivAt_id p) hp.1.ne').deriv]
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hp.1)
  have := sin_sub_mul_cos_pos hp
  simp only [mul_one, id_eq]
  nlinarith

@[simp] theorem csinc_ofReal (p : ℝ) : csinc (p : ℂ) = (Real.sinc p : ℂ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [csinc_zero]
  · rw [csinc_of_ne (Complex.ofReal_ne_zero.mpr hp), sineParameter,
      Real.sinc_of_ne_zero hp, ← Complex.ofReal_sin, Complex.ofReal_div]

@[simp] theorem csinc_mul_I (q : ℝ) : csinc ((q : ℂ) * I) = (sinhc q : ℂ) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [csinc_zero]
  · rw [csinc_of_ne (mul_ne_zero (Complex.ofReal_ne_zero.mpr hq) Complex.I_ne_zero),
      sineParameter, Complex.sin_mul_I, ← Complex.ofReal_sinh, sinhc_of_ne hq,
      Complex.ofReal_div]
    field_simp

def closedSineQuadrant : Set ℂ := {w | 0 < w.re ∧ w.im ≤ 0}
def closedSineDomain : Set ℂ := sineStrip ∩ csinc ⁻¹' closedSineQuadrant

theorem csinc_strip_re_lt_pi {z : ℂ} (hz : z ∈ sineStrip) (ha : 0 < (csinc z).re) :
    z.re < Real.pi := by
  by_contra! hn
  have hp : z.re = Real.pi := le_antisymm hz.2.1 hn
  have hz0 : z ≠ 0 := by intro he; simp [he] at hp; linarith [Real.pi_pos]
  rw [csinc_of_ne hz0, sineParameter_re, hp] at ha
  simp only [Real.sin_pi, Real.cos_pi, mul_zero, zero_mul, mul_neg_one, zero_add] at ha
  have : -(z.im * Real.sinh z.im) / (Real.pi ^ 2 + z.im ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
      (mul_nonneg hz.2.2 (Real.sinh_nonneg_iff.mpr hz.2.2))) (by positivity)
  rw [neg_mul] at ha
  linarith

theorem csinc_boundary_axes {z : ℂ} (hz : z ∈ closedSineDomain)
    (hi : (csinc z).im = 0) : z.re = 0 ∨ z.im = 0 := by
  by_contra! hn
  have hp : 0 < z.re := lt_of_le_of_ne hz.1.1 hn.1.symm
  have hq : 0 < z.im := lt_of_le_of_ne hz.1.2.2 hn.2.symm
  have he := sineParameter_im_neg ⟨hp, csinc_strip_re_lt_pi hz.1 hz.2.1⟩ hq
  rw [← csinc_of_ne (show z ≠ 0 by intro he; simp [he] at hp)] at he
  linarith

theorem sinc_eq_sinhc_only_zero {p q : ℝ} (hp : p ∈ Icc 0 Real.pi) (hq : 0 ≤ q)
    (he : Real.sinc p = sinhc q) : p = 0 ∧ q = 0 := by
  have hlow : 1 ≤ sinhc q := by
    simpa using strictMonoOn_sinhc.monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp) hq hq
  have hp0 : p = 0 := by
    by_contra hn
    have hlt := strictAntiOn_sinc ⟨le_rfl, Real.pi_pos.le⟩ hp (lt_of_le_of_ne hp.1 (Ne.symm hn))
    simp only [Real.sinc_zero] at hlt
    linarith
  have hq0 : q = 0 := by
    by_contra hn
    have hlt := strictMonoOn_sinhc (show (0 : ℝ) ∈ Ici 0 by simp) hq
      (lt_of_le_of_ne hq (Ne.symm hn))
    simp only [sinhc_zero] at hlt
    simp [hp0] at he
    linarith
  exact ⟨hp0, hq0⟩

theorem eq_of_im_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hz]

theorem eq_mul_I_of_re_zero {z : ℂ} (hz : z.re = 0) : z = (z.im : ℂ) * I := by
  apply Complex.ext <;> simp [hz]

theorem csinc_eq_sinhc_of_re_zero {z : ℂ} (hz : z.re = 0) :
    csinc z = (sinhc z.im : ℂ) :=
  (congrArg csinc (eq_mul_I_of_re_zero hz)).trans (csinc_mul_I z.im)

theorem csinc_eq_sinc_of_im_zero {z : ℂ} (hz : z.im = 0) :
    csinc z = (Real.sinc z.re : ℂ) :=
  (congrArg csinc (eq_of_im_zero hz)).trans (csinc_ofReal z.re)

theorem csinc_injOn_closedSineDomain : InjOn csinc closedSineDomain := by
  intro z hz w hw he
  by_cases hi : (csinc z).im < 0
  · have hz' : z ∈ sineDomain := csinc_strip_quadrant hz.1 ⟨hz.2.1, hi⟩
    have hw' : w ∈ sineDomain := csinc_strip_quadrant hw.1 ⟨hw.2.1, he ▸ hi⟩
    exact congrArg Subtype.val (bijective_sineMap.1 (a₁ := ⟨z, hz'⟩) (a₂ := ⟨w, hw'⟩)
      (Subtype.ext he))
  · have hi0 : (csinc z).im = 0 := le_antisymm hz.2.2 (le_of_not_gt hi)
    have hiw : (csinc w).im = 0 := he ▸ hi0
    rcases csinc_boundary_axes hz hi0 with hzr | hzi <;>
      rcases csinc_boundary_axes hw hiw with hwr | hwi
    · have he' : sinhc z.im = sinhc w.im := by
        apply Complex.ofReal_injective
        simpa only [csinc_eq_sinhc_of_re_zero hzr, csinc_eq_sinhc_of_re_zero hwr] using he
      have heq := strictMonoOn_sinhc.injOn hz.1.2.2 hw.1.2.2 he'
      exact Complex.ext (hzr.trans hwr.symm) heq
    · have he' : Real.sinc w.re = sinhc z.im := by
        apply Complex.ofReal_injective
        simpa only [csinc_eq_sinhc_of_re_zero hzr, csinc_eq_sinc_of_im_zero hwi]
          using he.symm
      obtain ⟨hwr0, hzi0⟩ := sinc_eq_sinhc_only_zero ⟨hw.1.1, hw.1.2.1⟩ hz.1.2.2 he'
      exact Complex.ext (hzr.trans hwr0.symm) (hzi0.trans hwi.symm)
    · have he' : Real.sinc z.re = sinhc w.im := by
        apply Complex.ofReal_injective
        simpa only [csinc_eq_sinc_of_im_zero hzi, csinc_eq_sinhc_of_re_zero hwr]
          using he
      obtain ⟨hzr0, hwi0⟩ := sinc_eq_sinhc_only_zero ⟨hz.1.1, hz.1.2.1⟩ hw.1.2.2 he'
      exact Complex.ext (hzr0.trans hwr.symm) (hzi.trans hwi0.symm)
    · have he' : Real.sinc z.re = Real.sinc w.re := by
        apply Complex.ofReal_injective
        simpa only [csinc_eq_sinc_of_im_zero hzi, csinc_eq_sinc_of_im_zero hwi] using he
      have heq := strictAntiOn_sinc.injOn ⟨hz.1.1, hz.1.2.1⟩ ⟨hw.1.1, hw.1.2.1⟩ he'
      exact Complex.ext heq (hzi.trans hwi.symm)

def closedSineMap : closedSineDomain → closedSineQuadrant := fun z => ⟨csinc z, z.property.2⟩

theorem continuous_closedSineMap : Continuous closedSineMap :=
  (continuous_csinc.comp continuous_subtype_val).subtype_mk _

theorem proper_closedSineMap : IsProperMap closedSineMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_closedSineMap, ?_⟩
  intro K hK
  have hc := isCompact_strip_preimage (hK.image continuous_subtype_val)
  have he : Subtype.val '' (closedSineMap ⁻¹' K) = sineStrip ∩ csinc ⁻¹' (Subtype.val '' K) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property.1, _, hu, rfl⟩
    · rintro ⟨hz, w, hw, he⟩
      have ha : csinc z ∈ closedSineQuadrant := he ▸ w.property
      refine ⟨⟨z, hz, ha⟩, ?_, rfl⟩
      have hw' : closedSineMap ⟨z, hz, ha⟩ = w := Subtype.ext he.symm
      simpa [hw'] using hw
  exact (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr (he ▸ hc)

theorem closedSineMap_injective : Function.Injective closedSineMap := by
  intro z w he
  apply Subtype.ext
  exact csinc_injOn_closedSineDomain z.property w.property (congrArg Subtype.val he)

theorem range_closedSineMap_of_im_neg {w : closedSineQuadrant} (hw : w.val.im < 0) :
    w ∈ range closedSineMap := by
  obtain ⟨z, hz⟩ := bijective_sineMap.2 ⟨w, w.property.1, hw⟩
  have hm : z.val ∈ closedSineDomain :=
    ⟨⟨z.property.1.le, z.property.2.1.le, z.property.2.2.1.le⟩,
       z.property.2.2.2, (csinc_mapsTo z.property).2.le⟩
  have he : csinc z.val = w.val := congrArg (fun u : sineQuadrant => u.val) hz
  exact ⟨⟨z, hm⟩, Subtype.ext he⟩

theorem closedSineMap_surjective : Function.Surjective closedSineMap := by
  intro w
  let v : ℕ → closedSineQuadrant := fun n =>
    ⟨⟨w.val.re, w.val.im - 1 / ((n : ℝ) + 1)⟩, w.property.1,
      sub_nonpos.mpr (w.property.2.trans (by positivity))⟩
  have hv (n : ℕ) : (v n).val.im < 0 := by
    dsimp [v]
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith [w.property.2]
  have ht : Tendsto v atTop (𝓝 w) := by
    apply tendsto_subtype_rng.mpr
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    have h := (tendsto_const_nhds (x := w.val)).sub
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hzero).mul_const I)
    simp only [Complex.ofReal_zero, zero_mul, sub_zero] at h
    convert h using 1
    funext n
    apply Complex.ext <;>
      simp only [v, Function.comp_apply, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

  exact proper_closedSineMap.isClosed_range.mem_of_tendsto ht
    (Eventually.of_forall (fun n => range_closedSineMap_of_im_neg (hv n)))

def closedSineHomeomorph : closedSineDomain ≃ₜ closedSineQuadrant :=
  (Equiv.ofBijective closedSineMap ⟨closedSineMap_injective, closedSineMap_surjective⟩).toHomeomorphOfContinuousClosed continuous_closedSineMap proper_closedSineMap.isClosedMap

def closedSineInverse (w : ℂ) : ℂ := by
  classical
  exact if hw : w ∈ closedSineQuadrant then (closedSineHomeomorph.symm ⟨w, hw⟩).val else 0

theorem closedSineInverse_mem {w : ℂ} (hw : w ∈ closedSineQuadrant) :
    closedSineInverse w ∈ closedSineDomain := by
  simpa only [closedSineInverse, dite_eq_left hw] using
    (closedSineHomeomorph.symm ⟨w, hw⟩).property

theorem csinc_closedSineInverse {w : ℂ} (hw : w ∈ closedSineQuadrant) :
    csinc (closedSineInverse w) = w := by
  have he := congrArg Subtype.val (closedSineHomeomorph.apply_symm_apply ⟨w, hw⟩)
  change csinc (closedSineHomeomorph.symm ⟨w, hw⟩).val = w at he
  simpa only [closedSineInverse, dite_eq_left hw] using he

def ccot (z : ℂ) : ℂ := Complex.cos z / csinc z

@[simp] theorem ccot_zero : ccot 0 = 1 := by simp [ccot, csinc_zero]

def upperReflect (s : ℂ) : ℂ := ⟨s.re, |s.im|⟩

theorem upperReflect_eq {s : ℂ} (hs : 0 ≤ s.im) : upperReflect s = s := by
  apply Complex.ext <;> simp [upperReflect, abs_of_nonneg hs]

def boundaryB (s : ℂ) : ℂ := ccot (closedSineInverse (Complex.sqrt (upperReflect s))⁻¹)

@[simp] theorem closedSineInverse_one : closedSineInverse 1 = 0 := by
  have hw : (1 : ℂ) ∈ closedSineQuadrant := by constructor <;> norm_num
  have hz : (0 : ℂ) ∈ closedSineDomain := by
    refine ⟨⟨le_rfl, Real.pi_pos.le, le_rfl⟩, ?_⟩
    change csinc 0 ∈ closedSineQuadrant
    simpa only [csinc_zero] using hw
  exact csinc_injOn_closedSineDomain (closedSineInverse_mem hw) hz
    ((csinc_closedSineInverse hw).trans csinc_zero.symm)

@[simp] theorem boundaryB_one : boundaryB 1 = 1 := by
  rw [boundaryB, upperReflect_eq (by norm_num), Complex.sqrt_one, inv_one,
    closedSineInverse_one, ccot_zero]

end EntropyPhotonNumber

end

end OAI


