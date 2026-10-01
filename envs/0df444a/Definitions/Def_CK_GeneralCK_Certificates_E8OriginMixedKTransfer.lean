-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedKTransfer
-- name    : CK_GeneralCK_Certificates_E8OriginMixedKTransfer
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:08:47.797733+00:00
-- url     : https://prove2.me/theorems/a5a9b24c-b3f7-4ecb-b17a-fbdd87a8b8b2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginMixedKTransfer` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginMixedKTransfer` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginMixedKTransfer` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginMixedKTransfer (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginMixedKTransfer.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginRealTaylorTransfer

-- ===== source module GeneralCK.Certificates.E8OriginMixedKTransfer =====
section

/-! Exact differential and error algebra for the E8 origin `K` transfer. -/

namespace GeneralCK.Certificates.E8OriginMixedKTransfer

open E8OriginMixedDerivativeConsumer
open E8OriginAnalyticCertificate E8OriginPositiveConsumer
open E8OriginRemainder E8AnalyticGerm E8AnalyticCoefficientBoxes
open E8OriginRealTaylorTransfer

/-- The twelve products obtained from `∂s²∂t (e8Delta Q)`. -/
noncomputable def mixedKFormula (Q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  -4 * Q s * iteratedDeriv 3 Q (2 * s + t) +
  Q t * iteratedDeriv 3 Q (s + t) -
  8 * Q t * iteratedDeriv 3 Q (2 * s + t) +
  4 * Q (s + t) * iteratedDeriv 3 Q (2 * s + t) +
  Q (2 * s + t) * iteratedDeriv 3 Q (s + t) -
  4 * iteratedDeriv 1 Q s * iteratedDeriv 2 Q (2 * s + t) +
  iteratedDeriv 2 Q s * iteratedDeriv 1 Q t -
  iteratedDeriv 2 Q s * iteratedDeriv 1 Q (2 * s + t) +
  iteratedDeriv 1 Q t * iteratedDeriv 2 Q (s + t) -
  8 * iteratedDeriv 1 Q t * iteratedDeriv 2 Q (2 * s + t) +
  8 * iteratedDeriv 1 Q (s + t) * iteratedDeriv 2 Q (2 * s + t) +
  5 * iteratedDeriv 2 Q (s + t) * iteratedDeriv 1 Q (2 * s + t)

/-- The mixed formula viewed as a function of four independent derivative
profiles.  This form exposes the cancellation of the linear Taylor jet. -/
def mixedKJetFormula (q0 q1 q2 q3 : ℝ → ℝ) (s t : ℝ) : ℝ :=
  -4 * q0 s * q3 (2 * s + t) +
  q0 t * q3 (s + t) - 8 * q0 t * q3 (2 * s + t) +
  4 * q0 (s + t) * q3 (2 * s + t) +
  q0 (2 * s + t) * q3 (s + t) -
  4 * q1 s * q2 (2 * s + t) + q2 s * q1 t -
  q2 s * q1 (2 * s + t) + q1 t * q2 (s + t) -
  8 * q1 t * q2 (2 * s + t) +
  8 * q1 (s + t) * q2 (2 * s + t) +
  5 * q2 (s + t) * q1 (2 * s + t)

theorem mixedKFormula_eq_jetFormula (Q : ℝ → ℝ) (s t : ℝ) :
    mixedKFormula Q s t = mixedKJetFormula Q (iteratedDeriv 1 Q)
      (iteratedDeriv 2 Q) (iteratedDeriv 3 Q) s t := by
  rfl


/-- Six-term intermediate expression for `∂s² (e8Delta Q)`. -/
noncomputable def mixedSSFormula (Q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (4 * iteratedDeriv 2 Q (2 * s + t) - iteratedDeriv 2 Q s) *
      (Q (s + t) - Q t) +
  2 * (2 * iteratedDeriv 1 Q (2 * s + t) - iteratedDeriv 1 Q s) *
      iteratedDeriv 1 Q (s + t) +
  (Q (2 * s + t) - Q s) * iteratedDeriv 2 Q (s + t) -
  (4 * iteratedDeriv 2 Q (2 * s + t) - iteratedDeriv 2 Q (s + t)) *
      (Q s + Q t) -
  2 * (2 * iteratedDeriv 1 Q (2 * s + t) - iteratedDeriv 1 Q (s + t)) *
      iteratedDeriv 1 Q s -
  (Q (2 * s + t) - Q (s + t)) * iteratedDeriv 2 Q s

theorem deltaS_eq_e8DeltaDerivS
    {Q : ℝ → ℝ}
    (hQ : ∀ x, HasDerivAt Q (iteratedDeriv 1 Q x) x) (s t : ℝ) :
    deltaS Q s t = e8DeltaDerivS Q s t := by
  unfold deltaS
  apply deriv_e8Delta_left
  · exact (hQ _).differentiableAt
  · exact (hQ _).differentiableAt
  · exact (hQ _).differentiableAt

theorem deltaSS_eq_mixedSSFormula
    {Q : ℝ → ℝ}
    (hQ : ∀ x, HasDerivAt Q (iteratedDeriv 1 Q x) x)
    (hQ1 : ∀ x, HasDerivAt (iteratedDeriv 1 Q) (iteratedDeriv 2 Q x) x)
    (s t : ℝ) :
    deltaSS Q s t = mixedSSFormula Q s t := by
  have hfun : (fun u => deltaS Q u t) = fun u => e8DeltaDerivS Q u t := by
    funext u
    exact deltaS_eq_e8DeltaDerivS hQ u t
  unfold deltaSS
  rw [hfun]
  let hlin : HasDerivAt (fun u : ℝ => 2 * u + t) 2 s :=
    by simpa only [id_eq, mul_one] using
      ((hasDerivAt_id s).const_mul 2).add_const t
  let hone : HasDerivAt (fun u : ℝ => u + t) 1 s :=
    (hasDerivAt_id s).add_const t
  have hB0 := (hQ (2 * s + t)).comp s hlin
  have hB1 := (hQ1 (2 * s + t)).comp s hlin
  have hC0 := (hQ (s + t)).comp s hone
  have hC1 := (hQ1 (s + t)).comp s hone
  have hD0 := hQ s
  have hD1 := hQ1 s
  have hA0 := hasDerivAt_const s (Q t)
  let rawS : ℝ → ℝ :=
    (((fun y => 2 * (iteratedDeriv 1 Q ∘ fun u => 2 * u + t) y) -
          iteratedDeriv 1 Q) *
        ((Q ∘ fun u => u + t) - fun _ => Q t) +
      ((Q ∘ fun u => 2 * u + t) - Q) *
        (iteratedDeriv 1 Q ∘ fun u => u + t)) -
    ((fun y => 2 * (iteratedDeriv 1 Q ∘ fun u => 2 * u + t) y) -
        (iteratedDeriv 1 Q ∘ fun u => u + t)) * (Q + fun _ => Q t) -
    ((Q ∘ fun u => 2 * u + t) - (Q ∘ fun u => u + t)) * iteratedDeriv 1 Q
  let dSS : ℝ :=
    (((2 * (iteratedDeriv 2 Q (2 * s + t) * 2) - iteratedDeriv 2 Q s) *
            (Q (s + t) - Q t) +
          (2 * iteratedDeriv 1 Q (2 * s + t) - iteratedDeriv 1 Q s) *
            iteratedDeriv 1 Q (s + t)) +
        ((iteratedDeriv 1 Q (2 * s + t) * 2 - iteratedDeriv 1 Q s) *
            iteratedDeriv 1 Q (s + t) +
          (Q (2 * s + t) - Q s) * iteratedDeriv 2 Q (s + t)) -
      ((2 * (iteratedDeriv 2 Q (2 * s + t) * 2) - iteratedDeriv 2 Q (s + t)) *
            (Q s + Q t) +
          (2 * iteratedDeriv 1 Q (2 * s + t) - iteratedDeriv 1 Q (s + t)) *
            iteratedDeriv 1 Q s)) -
    ((iteratedDeriv 1 Q (2 * s + t) * 2 - iteratedDeriv 1 Q (s + t)) *
          iteratedDeriv 1 Q s +
        (Q (2 * s + t) - Q (s + t)) * iteratedDeriv 2 Q s)
  have h : HasDerivAt rawS dSS s := by
    unfold rawS dSS
    simpa only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      mul_one, sub_zero, add_zero] using
    (((hB1.const_mul 2).sub hD1).mul (hC0.sub hA0)).add
      ((hB0.sub hD0).mul hC1) |>.sub
      (((hB1.const_mul 2).sub hC1).mul (hD0.add hA0)) |>.sub
      ((hB0.sub hC0).mul hD1)
  have heq : (fun u => e8DeltaDerivS Q u t) = rawS := by
    funext u
    simp only [rawS, e8DeltaDerivS, iteratedDeriv_one, Function.comp_apply,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  have hd : dSS = mixedSSFormula Q s t := by
    simp only [dSS, mixedSSFormula]
    ring
  rw [heq, h.deriv, hd]

theorem deltaSST_eq_mixedKFormula
    {Q : ℝ → ℝ}
    (hQ : ∀ x, HasDerivAt Q (iteratedDeriv 1 Q x) x)
    (hQ1 : ∀ x, HasDerivAt (iteratedDeriv 1 Q) (iteratedDeriv 2 Q x) x)
    (hQ2 : ∀ x, HasDerivAt (iteratedDeriv 2 Q) (iteratedDeriv 3 Q x) x)
    (s t : ℝ) :
    deltaSST Q s t = mixedKFormula Q s t := by
  have hfun : (fun v => deltaSS Q s v) = fun v => mixedSSFormula Q s v := by
    funext v
    exact deltaSS_eq_mixedSSFormula hQ hQ1 s v
  unfold deltaSST
  rw [hfun]
  let hB : HasDerivAt (fun v : ℝ => 2 * s + v) 1 t :=
    by simpa only [id_eq] using (hasDerivAt_id t).const_add (2 * s)
  let hC : HasDerivAt (fun v : ℝ => s + v) 1 t :=
    by simpa only [id_eq] using (hasDerivAt_id t).const_add s
  have hB0 := (hQ (2 * s + t)).comp t hB
  have hB1 := (hQ1 (2 * s + t)).comp t hB
  have hB2 := (hQ2 (2 * s + t)).comp t hB
  have hC0 := (hQ (s + t)).comp t hC
  have hC1 := (hQ1 (s + t)).comp t hC
  have hC2 := (hQ2 (s + t)).comp t hC
  have hA0 := hQ t
  have hA1 := hQ1 t
  have hD0 := hasDerivAt_const t (Q s)
  have hD1 := hasDerivAt_const t (iteratedDeriv 1 Q s)
  have hD2 := hasDerivAt_const t (iteratedDeriv 2 Q s)
  let rawT : ℝ → ℝ := fun v =>
    (4 * iteratedDeriv 2 Q (2 * s + v) - iteratedDeriv 2 Q s) *
        (Q (s + v) - Q v) +
    2 * (2 * iteratedDeriv 1 Q (2 * s + v) - iteratedDeriv 1 Q s) *
        iteratedDeriv 1 Q (s + v) +
    (Q (2 * s + v) - Q s) * iteratedDeriv 2 Q (s + v) -
    (4 * iteratedDeriv 2 Q (2 * s + v) - iteratedDeriv 2 Q (s + v)) *
        (Q s + Q v) -
    2 * (2 * iteratedDeriv 1 Q (2 * s + v) - iteratedDeriv 1 Q (s + v)) *
        iteratedDeriv 1 Q s -
    (Q (2 * s + v) - Q (s + v)) * iteratedDeriv 2 Q s
  have h0 :=
    (((hB2.const_mul 4).sub hD2).mul (hC0.sub hA0)).add
      ((((hB1.const_mul 2).sub hD1).mul hC1).const_mul 2) |>.add
      ((hB0.sub hD0).mul hC2) |>.sub
      (((hB2.const_mul 4).sub hC2).mul (hD0.add hA0)) |>.sub
      ((((hB1.const_mul 2).sub hC1).mul hD1).const_mul 2) |>.sub
      ((hB0.sub hC0).mul hD2)
  have h := h0.congr_of_eventuallyEq (show rawT =ᶠ[nhds t] _ by
    filter_upwards with v
    simp only [rawT, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring)
  have heq : (fun v => mixedSSFormula Q s v) = rawT := by
    funext v
    simp only [rawT, mixedSSFormula]
  rw [heq, h.deriv]
  simp only [mixedKFormula, Function.comp_apply, Pi.add_apply, Pi.sub_apply,
    mul_one, sub_zero]
  ring

/-- Absolute coefficient weights of the two product classes in the exact
twelve-term formula.  These are the `18` and `28` factors in the retained
remainder calculation. -/
theorem mixedK_product_weights :
    (|(-4 : ℤ)| + |(1 : ℤ)| + |(-8 : ℤ)| + |(4 : ℤ)| + |(1 : ℤ)| = 18) ∧
    (|(-4 : ℤ)| + |(1 : ℤ)| + |(-1 : ℤ)| + |(1 : ℤ)| + |(-8 : ℤ)| +
      |(8 : ℤ)| + |(5 : ℤ)| = 28) := by
  norm_num

def weight03 : ℕ → ℝ
  | 0 => -4 | 1 => 1 | 2 => -8 | 3 => 4 | 4 => 1 | _ => 0

def weight12 : ℕ → ℝ
  | 0 => -4 | 1 => 1 | 2 => -1 | 3 => 1 | 4 => -8 | 5 => 8 | 6 => 5 | _ => 0

def weightedMixedProducts (x03 x12 : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5, weight03 i * x03 i) +
  ∑ i ∈ Finset.range 7, weight12 i * x12 i

noncomputable def mixedProducts03 (Q : ℝ → ℝ) (s t : ℝ) : ℕ → ℝ
  | 0 => Q s * iteratedDeriv 3 Q (2 * s + t)
  | 1 => Q t * iteratedDeriv 3 Q (s + t)
  | 2 => Q t * iteratedDeriv 3 Q (2 * s + t)
  | 3 => Q (s + t) * iteratedDeriv 3 Q (2 * s + t)
  | 4 => Q (2 * s + t) * iteratedDeriv 3 Q (s + t)
  | _ => 0

noncomputable def mixedProducts12 (Q : ℝ → ℝ) (s t : ℝ) : ℕ → ℝ
  | 0 => iteratedDeriv 1 Q s * iteratedDeriv 2 Q (2 * s + t)
  | 1 => iteratedDeriv 2 Q s * iteratedDeriv 1 Q t
  | 2 => iteratedDeriv 2 Q s * iteratedDeriv 1 Q (2 * s + t)
  | 3 => iteratedDeriv 1 Q t * iteratedDeriv 2 Q (s + t)
  | 4 => iteratedDeriv 1 Q t * iteratedDeriv 2 Q (2 * s + t)
  | 5 => iteratedDeriv 1 Q (s + t) * iteratedDeriv 2 Q (2 * s + t)
  | 6 => iteratedDeriv 2 Q (s + t) * iteratedDeriv 1 Q (2 * s + t)
  | _ => 0

/-- The two weighted product families are definitionally the twelve-term mixed
formula.  This is the exact interface used by the tail perturbation bounds. -/
theorem weightedMixedProducts_mixedProducts_eq
    (Q : ℝ → ℝ) (s t : ℝ) :
    weightedMixedProducts (mixedProducts03 Q s t) (mixedProducts12 Q s t) =
      mixedKFormula Q s t := by
  norm_num [weightedMixedProducts, mixedProducts03, mixedProducts12,
    weight03, weight12, mixedKFormula, Finset.sum_range_succ]
  ring

#print axioms weightedMixedProducts_mixedProducts_eq
theorem product_perturbation_le
    {x x₀ y y₀ X Y ex ey : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hex0 : 0 ≤ ex)
    (hx : |x₀| ≤ X) (hy : |y₀| ≤ Y)
    (hex : |x - x₀| ≤ ex) (hey : |y - y₀| ≤ ey) :
    |x * y - x₀ * y₀| ≤ X * ey + Y * ex + ex * ey := by
  have hid : x * y - x₀ * y₀ =
      x₀ * (y - y₀) + y₀ * (x - x₀) + (x - x₀) * (y - y₀) := by ring
  rw [hid]
  calc
    _ ≤ |x₀ * (y - y₀)| + |y₀ * (x - x₀)| +
        |(x - x₀) * (y - y₀)| := by
      exact (abs_add_three _ _ _)
    _ ≤ X * ey + Y * ex + ex * ey := by
      rw [abs_mul, abs_mul, abs_mul]
      gcongr

/-- A `Q·Q'''` product perturbation whose higher-coefficient errors begin in
degrees five and two is cubic after extracting the common radius. -/
theorem scaled03_product_perturbation_le
    {x x₀ y y₀ P0 P3 E0 E3 r R : ℝ}
    (hP0 : 0 ≤ P0) (hP3 : 0 ≤ P3) (hE0 : 0 ≤ E0) (hE3 : 0 ≤ E3)
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hx₀ : |x₀| ≤ P0 * r) (hy₀ : |y₀| ≤ P3)
    (hx : |x - x₀| ≤ E0 * r ^ 5) (hy : |y - y₀| ≤ E3 * r ^ 2) :
    |x * y - x₀ * y₀| ≤
      (P0 * E3 + P3 * E0 * R ^ 2 + E0 * E3 * R ^ 4) * r ^ 3 := by
  have hR : 0 ≤ R := hr.trans hrR
  have hbase := product_perturbation_le
    (X := P0 * r) (Y := P3) (ex := E0 * r ^ 5) (ey := E3 * r ^ 2)
    (mul_nonneg hP0 hr) hP3 (mul_nonneg hE0 (pow_nonneg hr 5))
    hx₀ hy₀ hx hy
  calc
    |x * y - x₀ * y₀| ≤
        (P0 * r) * (E3 * r ^ 2) + P3 * (E0 * r ^ 5) +
          (E0 * r ^ 5) * (E3 * r ^ 2) := hbase
    _ = (P0 * E3 + P3 * E0 * r ^ 2 + E0 * E3 * r ^ 4) * r ^ 3 := by ring
    _ ≤ (P0 * E3 + P3 * E0 * R ^ 2 + E0 * E3 * R ^ 4) * r ^ 3 := by
      gcongr

/-- The analogous `Q'·Q''` perturbation: higher-coefficient errors begin in
degrees four and three and hence again contribute only cubically. -/
theorem scaled12_product_perturbation_le
    {x x₀ y y₀ P1 P2 E1 E2 r R : ℝ}
    (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hx₀ : |x₀| ≤ P1) (hy₀ : |y₀| ≤ P2 * r)
    (hx : |x - x₀| ≤ E1 * r ^ 4) (hy : |y - y₀| ≤ E2 * r ^ 3) :
    |x * y - x₀ * y₀| ≤
      (P1 * E2 + P2 * E1 * R ^ 2 + E1 * E2 * R ^ 4) * r ^ 3 := by
  have hR : 0 ≤ R := hr.trans hrR
  have hbase := product_perturbation_le
    (X := P1) (Y := P2 * r) (ex := E1 * r ^ 4) (ey := E2 * r ^ 3)
    hP1 (mul_nonneg hP2 hr) (mul_nonneg hE1 (pow_nonneg hr 4))
    hx₀ hy₀ hx hy
  calc
    |x * y - x₀ * y₀| ≤
        P1 * (E2 * r ^ 3) + (P2 * r) * (E1 * r ^ 4) +
          (E1 * r ^ 4) * (E2 * r ^ 3) := hbase
    _ = (P1 * E2 + P2 * E1 * r ^ 2 + E1 * E2 * r ^ 4) * r ^ 3 := by ring
    _ ≤ (P1 * E2 + P2 * E1 * R ^ 2 + E1 * E2 * R ^ 4) * r ^ 3 := by
      gcongr

#print axioms scaled03_product_perturbation_le
#print axioms scaled12_product_perturbation_le
/-- Order-17 Taylor tails in a `Q·Q'''` product have orders 17 and 14.
After multiplying by the source polynomial sizes, the three perturbation terms
are bounded by the exact radius powers 12, 14, and 28 used in
`remainderOverRadiusCubed`. -/
theorem tail03_product_perturbation_le
    {x x₀ y y₀ P0 P3 E0 E3 r R : ℝ}
    (hP0 : 0 ≤ P0) (hP3 : 0 ≤ P3) (hE0 : 0 ≤ E0) (hE3 : 0 ≤ E3)
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hx₀ : |x₀| ≤ P0 * r) (hy₀ : |y₀| ≤ P3)
    (hx : |x - x₀| ≤ E0 * r ^ 17) (hy : |y - y₀| ≤ E3 * r ^ 14) :
    |x * y - x₀ * y₀| ≤
      (P0 * E3 * R ^ 12 + P3 * E0 * R ^ 14 +
        E0 * E3 * R ^ 28) * r ^ 3 := by
  have hR : 0 ≤ R := hr.trans hrR
  have hbase := product_perturbation_le
    (X := P0 * r) (Y := P3) (ex := E0 * r ^ 17) (ey := E3 * r ^ 14)
    (mul_nonneg hP0 hr) hP3 (mul_nonneg hE0 (pow_nonneg hr 17))
    hx₀ hy₀ hx hy
  calc
    |x * y - x₀ * y₀| ≤
        (P0 * r) * (E3 * r ^ 14) + P3 * (E0 * r ^ 17) +
          (E0 * r ^ 17) * (E3 * r ^ 14) := hbase
    _ = (P0 * E3 * r ^ 12 + P3 * E0 * r ^ 14 +
          E0 * E3 * r ^ 28) * r ^ 3 := by ring
    _ ≤ (P0 * E3 * R ^ 12 + P3 * E0 * R ^ 14 +
          E0 * E3 * R ^ 28) * r ^ 3 := by
      gcongr

/-- Order-17 Taylor tails in a `Q'·Q''` product have orders 16 and 15,
giving the same checked radius powers 12, 14, and 28 after cubic extraction. -/
theorem tail12_product_perturbation_le
    {x x₀ y y₀ P1 P2 E1 E2 r R : ℝ}
    (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hx₀ : |x₀| ≤ P1) (hy₀ : |y₀| ≤ P2 * r)
    (hx : |x - x₀| ≤ E1 * r ^ 16) (hy : |y - y₀| ≤ E2 * r ^ 15) :
    |x * y - x₀ * y₀| ≤
      (P1 * E2 * R ^ 12 + P2 * E1 * R ^ 14 +
        E1 * E2 * R ^ 28) * r ^ 3 := by
  have hR : 0 ≤ R := hr.trans hrR
  have hbase := product_perturbation_le
    (X := P1) (Y := P2 * r) (ex := E1 * r ^ 16) (ey := E2 * r ^ 15)
    hP1 (mul_nonneg hP2 hr) (mul_nonneg hE1 (pow_nonneg hr 16))
    hx₀ hy₀ hx hy
  calc
    |x * y - x₀ * y₀| ≤
        P1 * (E2 * r ^ 15) + (P2 * r) * (E1 * r ^ 16) +
          (E1 * r ^ 16) * (E2 * r ^ 15) := hbase
    _ = (P1 * E2 * r ^ 12 + P2 * E1 * r ^ 14 +
          E1 * E2 * r ^ 28) * r ^ 3 := by ring
    _ ≤ (P1 * E2 * R ^ 12 + P2 * E1 * R ^ 14 +
          E1 * E2 * R ^ 28) * r ^ 3 := by
      gcongr

#print axioms tail03_product_perturbation_le
#print axioms tail12_product_perturbation_le
theorem weighted_family_error_le
    {n : ℕ} {c x y : ℕ → ℝ} {E : ℝ}
    (hxy : ∀ i ∈ Finset.range n, |x i - y i| ≤ E) :
    |(∑ i ∈ Finset.range n, c i * x i) -
        ∑ i ∈ Finset.range n, c i * y i| ≤
      (∑ i ∈ Finset.range n, |c i|) * E := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n, |c i * x i - c i * y i| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Finset.range n) (fun i => c i * x i - c i * y i))
    _ ≤ ∑ i ∈ Finset.range n, |c i| * E := by
      gcongr with i hi
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hxy i hi) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

/-- Aggregating five `Q·Q'''` and seven `Q'·Q''` product errors that already
carry a common cubic radius gives exactly the coefficient weights 18 and 28. -/
theorem weightedMixedProducts_cubic_error_le
    {actual03 source03 actual12 source12 : ℕ → ℝ} {A B r : ℝ}
    (h03 : ∀ i ∈ Finset.range 5,
      |actual03 i - source03 i| ≤ A * r ^ 3)
    (h12 : ∀ i ∈ Finset.range 7,
      |actual12 i - source12 i| ≤ B * r ^ 3) :
    |weightedMixedProducts actual03 actual12 -
        weightedMixedProducts source03 source12| ≤
      (18 * A + 28 * B) * r ^ 3 := by
  have ha := weighted_family_error_le (c := weight03) h03
  have hb := weighted_family_error_le (c := weight12) h12
  unfold weightedMixedProducts
  have hsplit :
      ((∑ i ∈ Finset.range 5, weight03 i * actual03 i) +
          ∑ i ∈ Finset.range 7, weight12 i * actual12 i) -
        ((∑ i ∈ Finset.range 5, weight03 i * source03 i) +
          ∑ i ∈ Finset.range 7, weight12 i * source12 i) =
      ((∑ i ∈ Finset.range 5, weight03 i * actual03 i) -
          ∑ i ∈ Finset.range 5, weight03 i * source03 i) +
        ((∑ i ∈ Finset.range 7, weight12 i * actual12 i) -
          ∑ i ∈ Finset.range 7, weight12 i * source12 i) := by ring
  rw [hsplit]
  calc
    _ ≤ |(∑ i ∈ Finset.range 5, weight03 i * actual03 i) -
          ∑ i ∈ Finset.range 5, weight03 i * source03 i| +
        |(∑ i ∈ Finset.range 7, weight12 i * actual12 i) -
          ∑ i ∈ Finset.range 7, weight12 i * source12 i| := abs_add_le _ _
    _ ≤ (∑ i ∈ Finset.range 5, |weight03 i|) * (A * r ^ 3) +
        (∑ i ∈ Finset.range 7, |weight12 i|) * (B * r ^ 3) := add_le_add ha hb
    _ = (18 * A + 28 * B) * r ^ 3 := by
      norm_num [weight03, weight12, Finset.sum_range_succ]
      ring

#print axioms weightedMixedProducts_cubic_error_le
/-- One common factor for the five `Q·Q'''` perturbations and the seven
`Q'·Q''` perturbations.  Substituting errors already factored by `(s+t)^3`
gives the coefficient-box plus Taylor-tail cubic error used by `MixedKTransfer`. -/
def combinedCubicErrorFactor
    (P0 P1 P2 P3 E0 E1 E2 E3 : ℝ) : ℝ :=
  18 * (P0 * E3 + P3 * E0 + E0 * E3) +
  28 * (P1 * E2 + P2 * E1 + E1 * E2)

theorem weightedMixedProducts_sub_le_combinedCubicErrorFactor
    {actual03 source03 actual12 source12 : ℕ → ℝ}
    {P0 P1 P2 P3 E0 E1 E2 E3 : ℝ}
    (h03 : ∀ i ∈ Finset.range 5,
      |actual03 i - source03 i| ≤ P0 * E3 + P3 * E0 + E0 * E3)
    (h12 : ∀ i ∈ Finset.range 7,
      |actual12 i - source12 i| ≤ P1 * E2 + P2 * E1 + E1 * E2) :
    |weightedMixedProducts actual03 actual12 -
        weightedMixedProducts source03 source12| ≤
      combinedCubicErrorFactor P0 P1 P2 P3 E0 E1 E2 E3 := by
  let A := P0 * E3 + P3 * E0 + E0 * E3
  let B := P1 * E2 + P2 * E1 + E1 * E2
  have ha := weighted_family_error_le (c := weight03) h03
  have hb := weighted_family_error_le (c := weight12) h12
  unfold weightedMixedProducts combinedCubicErrorFactor
  have hsplit :
      ((∑ i ∈ Finset.range 5, weight03 i * actual03 i) +
          ∑ i ∈ Finset.range 7, weight12 i * actual12 i) -
        ((∑ i ∈ Finset.range 5, weight03 i * source03 i) +
          ∑ i ∈ Finset.range 7, weight12 i * source12 i) =
      ((∑ i ∈ Finset.range 5, weight03 i * actual03 i) -
          ∑ i ∈ Finset.range 5, weight03 i * source03 i) +
        ((∑ i ∈ Finset.range 7, weight12 i * actual12 i) -
          ∑ i ∈ Finset.range 7, weight12 i * source12 i) := by ring
  rw [hsplit]
  calc
    _ ≤ |(∑ i ∈ Finset.range 5, weight03 i * actual03 i) -
          ∑ i ∈ Finset.range 5, weight03 i * source03 i| +
        |(∑ i ∈ Finset.range 7, weight12 i * actual12 i) -
          ∑ i ∈ Finset.range 7, weight12 i * source12 i| := abs_add_le _ _
    _ ≤ (∑ i ∈ Finset.range 5, |weight03 i|) * A +
        (∑ i ∈ Finset.range 7, |weight12 i|) * B := add_le_add ha hb
    _ = 18 * (P0 * E3 + P3 * E0 + E0 * E3) +
        28 * (P1 * E2 + P2 * E1 + E1 * E2) := by
      norm_num [A, B, weight03, weight12, Finset.sum_range_succ]

/-- Point-local first derivative identity; unlike `deltaS_eq_e8DeltaDerivS`,
this needs differentiability only at the three arguments actually occurring. -/
theorem deltaS_eq_e8DeltaDerivS_at
    {Q : ℝ → ℝ} {s t : ℝ}
    (hB : DifferentiableAt ℝ Q (2 * s + t))
    (hC : DifferentiableAt ℝ Q (s + t))
    (hD : DifferentiableAt ℝ Q s) :
    deltaS Q s t = e8DeltaDerivS Q s t := by
  unfold deltaS
  exact deriv_e8Delta_left Q s t hB hC hD

/-- Near any admissible base point, the first derivative of the E8 defect for
`qReal` agrees with its explicit formula.  This eventual equality is what is
needed to differentiate once more without any global smoothness premise. -/
theorem eventually_deltaS_qReal_eq_e8DeltaDerivS
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate) {s t : ℝ}
    (hs : |s| < E8QuantitativeBranchBridge.yOuterRadius)
    (hst : |s + t| < E8QuantitativeBranchBridge.yOuterRadius)
    (h2st : |2 * s + t| < E8QuantitativeBranchBridge.yOuterRadius) :
    (fun u => deltaS (E8OriginPositiveConsumer.qReal cert) u t) =ᶠ[nhds s]
      (fun u => e8DeltaDerivS (E8OriginPositiveConsumer.qReal cert) u t) := by
  let U : Set ℝ := {x | |x| < E8QuantitativeBranchBridge.yOuterRadius}
  have hU : IsOpen U := isOpen_lt continuous_abs continuous_const
  have hD : ∀ᶠ u in nhds s, u ∈ U := hU.mem_nhds hs
  have hC : ∀ᶠ u in nhds s, u + t ∈ U :=
    (hU.preimage (continuous_id.add continuous_const)).mem_nhds hst
  have hB : ∀ᶠ u in nhds s, 2 * u + t ∈ U :=
    (hU.preimage ((continuous_const.mul continuous_id).add continuous_const)).mem_nhds h2st
  filter_upwards [hD, hC, hB] with u huD huC huB
  exact deltaS_eq_e8DeltaDerivS_at
    (E8OriginQRealRegularity.qReal_differentiableAt cert huB)
    (E8OriginQRealRegularity.qReal_differentiableAt cert huC)
    (E8OriginQRealRegularity.qReal_differentiableAt cert huD)
/-- Inside the quantitative inverse disc, consecutive real iterated derivatives
form an exact `HasDerivAt` chain.  This is the point-local replacement for the
global derivative hypotheses used by `deltaSST_eq_mixedKFormula`. -/
theorem qReal_hasDerivAt_iteratedDeriv
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate) (n : ℕ)
    {y : ℝ} (hy : |y| < E8QuantitativeBranchBridge.yOuterRadius) :
    HasDerivAt
      (iteratedDeriv n (E8OriginPositiveConsumer.qReal cert))
      (iteratedDeriv (n + 1) (E8OriginPositiveConsumer.qReal cert) y) y := by
  rw [iteratedDeriv_succ]
  exact
    ((E8OriginRealTaylorTransfer.iteratedDeriv_qReal_contDiffAt cert n hy).differentiableAt
      (by simp)).hasDerivAt

/-- The three derivative links needed by the twelve-term mixed formula are
available at every point strictly inside the quantitative inverse disc. -/
theorem qReal_three_derivative_layers
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate)
    {y : ℝ} (hy : |y| < E8QuantitativeBranchBridge.yOuterRadius) :
    HasDerivAt (E8OriginPositiveConsumer.qReal cert)
        (iteratedDeriv 1 (E8OriginPositiveConsumer.qReal cert) y) y ∧
      HasDerivAt (iteratedDeriv 1 (E8OriginPositiveConsumer.qReal cert))
        (iteratedDeriv 2 (E8OriginPositiveConsumer.qReal cert) y) y ∧
      HasDerivAt (iteratedDeriv 2 (E8OriginPositiveConsumer.qReal cert))
        (iteratedDeriv 3 (E8OriginPositiveConsumer.qReal cert) y) y := by
  constructor
  · simpa only [iteratedDeriv_zero, Nat.zero_add] using
      qReal_hasDerivAt_iteratedDeriv cert 0 hy
  constructor
  · simpa only [Nat.reduceAdd] using qReal_hasDerivAt_iteratedDeriv cert 1 hy
  · simpa only [Nat.reduceAdd] using qReal_hasDerivAt_iteratedDeriv cert 2 hy

theorem pow_le_two_mul_radius {y r R : ℝ} (n : ℕ) (hn : 0 < n)
    (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r) (hrR : r ≤ R) :
    y ^ n ≤ 2 ^ n * R ^ (n - 1) * r := by
  have hR : 0 ≤ R := hr.trans hrR
  calc
    y ^ n ≤ (2 * r) ^ n := pow_le_pow_left₀ hy hyr n
    _ = 2 ^ n * r ^ n := by rw [mul_pow]
    _ = 2 ^ n * (r ^ (n - 1) * r) := by
      rw [← pow_succ]
      congr 2
      omega
    _ ≤ 2 ^ n * (R ^ (n - 1) * r) := by gcongr
    _ = 2 ^ n * R ^ (n - 1) * r := by ring

/-- Extract an arbitrary common radius power from an affine argument bounded
by `2*r`. -/
theorem pow_le_two_mul_radius_pow {y r R : ℝ} (n d : ℕ) (hd : d ≤ n)
    (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r) (hrR : r ≤ R) :
    y ^ n ≤ 2 ^ n * R ^ (n - d) * r ^ d := by
  have hR : 0 ≤ R := hr.trans hrR
  calc
    y ^ n ≤ (2 * r) ^ n := pow_le_pow_left₀ hy hyr n
    _ = 2 ^ n * r ^ n := by rw [mul_pow]
    _ = 2 ^ n * (r ^ (n - d) * r ^ d) := by
      rw [← pow_add]
      congr 2
      omega
    _ ≤ 2 ^ n * (R ^ (n - d) * r ^ d) := by gcongr
    _ = 2 ^ n * R ^ (n - d) * r ^ d := by ring

/-- Degree-5-through-15 part of the actual derivative polynomial. -/
noncomputable def qRealTaylorHighDerivative (cert : QuantitativeCertificate)
    (j : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 11,
    ((k + 5).factorial : ℝ) / (k + 5 - j).factorial *
      (qTaylorCoeff (k + 5)).re * y ^ (k + 5 - j)

/-- Degree-5-through-15 part of the rational source-center polynomial. -/
noncomputable def qSourceTaylorHighDerivative (j : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 11,
    ((k + 5).factorial : ℝ) / (k + 5 - j).factorial *
      (sourceCenter (k + 5) : ℝ) * y ^ (k + 5 - j)

def lowJetDerivative (a b : ℝ) : ℕ → ℝ → ℝ
  | 0, y => a * y + b * y ^ 3
  | 1, y => a + 3 * b * y ^ 2
  | 2, y => 6 * b * y
  | 3, _ => 6 * b
  | _, _ => 0

theorem qRealTaylorDerivative_eq_low_add_high
    (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 3) (y : ℝ) :
    qRealTaylorDerivative cert j y =
      lowJetDerivative (qTaylorCoeff 1).re (qTaylorCoeff 3).re j y +
        qRealTaylorHighDerivative cert j y := by
  rw [qRealTaylorDerivative_eq_coefficients15 cert j
    (show j ≤ 5 by omega)]
  interval_cases j <;>
    simp only [lowJetDerivative, qRealTaylorHighDerivative,
      Finset.sum_range_succ,
      qTaylorCoeff_eq_zero_of_even (show Even 0 by decide),
      qTaylorCoeff_eq_zero_of_even (show Even 2 by decide),
      qTaylorCoeff_eq_zero_of_even (show Even 4 by decide),
      qTaylorCoeff_eq_zero_of_even (show Even 6 by decide),
      qTaylorCoeff_eq_zero_of_even (show Even 8 by decide),
      qTaylorCoeff_eq_zero_of_even (show Even 10 by decide),
      qTaylorCoeff_eq_zero_of_even (show Even 12 by decide),
      qTaylorCoeff_eq_zero_of_even (show Even 14 by decide), Complex.zero_re] <;>
    norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub] <;> ring

theorem qSourceTaylorDerivative_eq_low_add_high
    (j : ℕ) (hj : j ≤ 3) (y : ℝ) :
    qSourceTaylorDerivative j y =
      lowJetDerivative (sourceCenter 1 : ℝ) (sourceCenter 3 : ℝ) j y +
        qSourceTaylorHighDerivative j y := by
  have h0 : (sourceCenter 0 : ℝ) = 0 := by norm_num [sourceCenter, sourceBox]
  have h2 : (sourceCenter 2 : ℝ) = 0 := by norm_num [sourceCenter, sourceBox]
  have h4 : (sourceCenter 4 : ℝ) = 0 := by norm_num [sourceCenter, sourceBox]
  have h6 : (sourceCenter 6 : ℝ) = 0 := by norm_num [sourceCenter, sourceBox]
  have h8 : (sourceCenter 8 : ℝ) = 0 := by norm_num [sourceCenter, sourceBox]
  have h10 : (sourceCenter 10 : ℝ) = 0 := by norm_num [sourceCenter, sourceBox]
  have h12 : (sourceCenter 12 : ℝ) = 0 := by norm_num [sourceCenter, sourceBox]
  have h14 : (sourceCenter 14 : ℝ) = 0 := by norm_num [sourceCenter, sourceBox]
  interval_cases j <;>
    simp only [qSourceTaylorDerivative, lowJetDerivative,
      qSourceTaylorHighDerivative, Finset.sum_range_succ,
      h0, h2, h4, h6, h8, h10, h12, h14, zero_mul, add_zero] <;>
    norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub] <;> ring

#print axioms qRealTaylorDerivative_eq_low_add_high
#print axioms qSourceTaylorDerivative_eq_low_add_high

noncomputable def highCoeffBound (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 11,
    ((k + 5).factorial : ℝ) / (k + 5 - j).factorial *
      (coeffAbsUpper (k + 5) : ℝ) * 2 ^ (k + 5 - j) *
        (radius : ℝ) ^ ((k + 5 - j) - (5 - j))

noncomputable def highCoeffError (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 11,
    ((k + 5).factorial : ℝ) / (k + 5 - j).factorial *
      (sourceHalfWidth (k + 5) : ℝ) * 2 ^ (k + 5 - j) *
        (radius : ℝ) ^ ((k + 5 - j) - (5 - j))

theorem abs_sourceCenter_le_coeffAbsUpper {n : ℕ} (hn : n < 16) :
    |(sourceCenter n : ℝ)| ≤ (coeffAbsUpper n : ℝ) := by
  interval_cases n <;>
    norm_num [sourceCenter, sourceBox, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15]

theorem abs_qTaylorCoeff_re_le_coeffAbsUpper_high {n : ℕ} (hn : n < 16) :
    |(qTaylorCoeff n).re| ≤ (coeffAbsUpper n : ℝ) := by
  have h := qTaylorCoeff_re_sourceCenter_le hn
  interval_cases n <;>
    norm_num [sourceCenter, sourceHalfWidth, sourceBox, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15] at h ⊢ <;>
    first | exact h | (rw [abs_le] at h ⊢; constructor <;> linarith [h.1, h.2])

/-- The high actual profile has the exact degree-dependent scaling needed by
the mixed products: powers `5,4,3,2` for derivative orders `0,1,2,3`. -/
theorem qRealTaylorHighDerivative_le
    (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 3)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (radius : ℝ)) :
    ‖qRealTaylorHighDerivative cert j y‖ ≤
      highCoeffBound j * r ^ (5 - j) := by
  unfold qRealTaylorHighDerivative highCoeffBound
  calc
    _ ≤ ∑ k ∈ Finset.range 11,
        ‖((k+5).factorial : ℝ) / (k+5-j).factorial *
          (qTaylorCoeff (k+5)).re * y ^ (k+5-j)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range 11,
        (((k+5).factorial : ℝ) / (k+5-j).factorial *
          (coeffAbsUpper (k+5) : ℝ) * 2 ^ (k+5-j) *
          (radius : ℝ) ^ ((k+5-j) - (5-j))) *
          r ^ (5 - j) := by
      gcongr with k hk
      have hk11 : k < 11 := Finset.mem_range.mp hk
      have hn16 : k + 5 < 16 := by omega
      have hd : 5 - j ≤ k + 5 - j := by omega
      have hfac : 0 ≤ ((k+5).factorial : ℝ) / (k+5-j).factorial := by positivity
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hfac,
        abs_of_nonneg hy]
      have hp := pow_le_two_mul_radius_pow (k+5-j) (5-j) hd hy hyr hr hrR
      have hc := abs_qTaylorCoeff_re_le_coeffAbsUpper_high hn16
      convert mul_le_mul_of_nonneg_left
        (mul_le_mul hc hp (pow_nonneg hy (k+5-j))
          ((abs_nonneg _).trans hc)) hfac using 1 <;> ring
    _ = (∑ k ∈ Finset.range 11,
        ((k+5).factorial : ℝ) / (k+5-j).factorial *
          (coeffAbsUpper (k+5) : ℝ) * 2 ^ (k+5-j) *
          (radius : ℝ) ^ ((k+5-j) - (5-j))) *
          r ^ (5 - j) := by
      rw [← Finset.sum_mul]

/-- The coefficient-box error in the high profile has the same scaling. -/
theorem qRealTaylorHighDerivative_sub_source_le
    (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 3)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (radius : ℝ)) :
    ‖qRealTaylorHighDerivative cert j y - qSourceTaylorHighDerivative j y‖ ≤
      highCoeffError j * r ^ (5 - j) := by
  unfold qRealTaylorHighDerivative qSourceTaylorHighDerivative highCoeffError
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range 11,
        ‖((k+5).factorial : ℝ) / (k+5-j).factorial * (qTaylorCoeff (k+5)).re *
            y ^ (k+5-j) -
          ((k+5).factorial : ℝ) / (k+5-j).factorial * (sourceCenter (k+5) : ℝ) *
            y ^ (k+5-j)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range 11,
        (((k+5).factorial : ℝ) / (k+5-j).factorial *
          (sourceHalfWidth (k+5) : ℝ) * 2 ^ (k+5-j) *
          (radius : ℝ) ^ ((k+5-j) - (5-j))) *
          r ^ (5 - j) := by
      gcongr with k hk
      have hk11 : k < 11 := Finset.mem_range.mp hk
      have hn16 : k + 5 < 16 := by omega
      have hd : 5 - j ≤ k + 5 - j := by omega
      have hfac : 0 ≤ ((k+5).factorial : ℝ) / (k+5-j).factorial := by positivity
      have heq :
          ((k+5).factorial : ℝ) / (k+5-j).factorial * (qTaylorCoeff (k+5)).re *
              y ^ (k+5-j) -
            ((k+5).factorial : ℝ) / (k+5-j).factorial * (sourceCenter (k+5) : ℝ) *
              y ^ (k+5-j) =
          ((k+5).factorial : ℝ) / (k+5-j).factorial *
            ((qTaylorCoeff (k+5)).re - (sourceCenter (k+5) : ℝ)) * y ^ (k+5-j) := by ring
      rw [heq, norm_mul, norm_mul, norm_pow]
      simp only [Real.norm_eq_abs, abs_of_nonneg hfac, abs_of_nonneg hy]
      have hp := pow_le_two_mul_radius_pow (k+5-j) (5-j) hd hy hyr hr hrR
      have hc := qTaylorCoeff_re_sourceCenter_le hn16
      convert mul_le_mul_of_nonneg_left
        (mul_le_mul hc hp (pow_nonneg hy (k+5-j))
          ((abs_nonneg _).trans hc)) hfac using 1 <;> ring
    _ = (∑ k ∈ Finset.range 11,
        ((k+5).factorial : ℝ) / (k+5-j).factorial *
          (sourceHalfWidth (k+5) : ℝ) * 2 ^ (k+5-j) *
          (radius : ℝ) ^ ((k+5-j) - (5-j))) *
          r ^ (5 - j) := by
      rw [← Finset.sum_mul]

#print axioms qRealTaylorHighDerivative_le
#print axioms qRealTaylorHighDerivative_sub_source_le

theorem highCoeffError_lt (j : ℕ) (hj : j ≤ 3) :
    highCoeffError j < (1 / 10 ^ 45 : ℝ) := by
  interval_cases j <;>
    norm_num [highCoeffError, sourceHalfWidth, sourceCenter, sourceBox, radius,
      a1, a3, a5, a7, a9, a11, a13, a15, Finset.sum_range_succ]

theorem highCoeffBound_nonnegative (j : ℕ) : 0 ≤ highCoeffBound j := by
  unfold highCoeffBound
  apply Finset.sum_nonneg
  intro k hk
  have hk11 : k < 11 := Finset.mem_range.mp hk
  interval_cases k <;>
    norm_num [coeffAbsUpper, radius, a1, a3, a5, a7, a9, a11, a13, a15] <;>
    positivity

theorem highCoeffError_nonnegative (j : ℕ) : 0 ≤ highCoeffError j := by
  unfold highCoeffError
  apply Finset.sum_nonneg
  intro k hk
  have hk11 : k < 11 := Finset.mem_range.mp hk
  interval_cases k <;>
    norm_num [sourceHalfWidth, sourceBox, radius,
      a1, a3, a5, a7, a9, a11, a13, a15] <;> positivity

#print axioms highCoeffError_lt

#print axioms pow_le_two_mul_radius

theorem abs_qTaylorCoeff_re_le_coeffAbsUpper {n : ℕ} (hn : n < 16) :
    |(qTaylorCoeff n).re| ≤ (coeffAbsUpper n : ℝ) := by
  have h := qTaylorCoeff_re_sourceCenter_le hn
  interval_cases n <;>
    norm_num [sourceCenter, sourceHalfWidth, sourceBox, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15] at h ⊢ <;>
    first | exact h | (rw [abs_le] at h ⊢; constructor <;> linarith [h.1, h.2])

#print axioms abs_qTaylorCoeff_re_le_coeffAbsUpper

theorem qRealTaylorDerivative_zero_le_p0c
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (E8OriginRemainder.radius : ℝ)) :
    ‖E8OriginRealTaylorTransfer.qRealTaylorDerivative cert 0 y‖ ≤
      (E8OriginRemainder.p0c : ℝ) * r := by
  rw [qRealTaylorDerivative_eq_coefficients15 cert 0 (by omega)]
  simp only [Nat.add_zero, Nat.sub_zero]
  calc
    ‖∑ k ∈ Finset.range 16,
        (k.factorial : ℝ) / k.factorial * (qTaylorCoeff k).re * y ^ k‖ ≤
      ∑ k ∈ Finset.range 16,
        ‖(k.factorial : ℝ) / k.factorial * (qTaylorCoeff k).re * y ^ k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range 16,
        (coeffAbsUpper k : ℝ) * 2 ^ k * (radius : ℝ) ^ (k - 1) * r := by
      gcongr with k hk
      have hk16 : k < 16 := Finset.mem_range.mp hk
      have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
      rw [div_self hkfac, one_mul, norm_mul, norm_pow]
      simp only [Real.norm_eq_abs, abs_of_nonneg hy]
      by_cases hk0 : k = 0
      · subst k
        norm_num [coeffAbsUpper]
      · have hpow := pow_le_two_mul_radius k (Nat.pos_of_ne_zero hk0)
          hy hyr hr hrR
        have hc := abs_qTaylorCoeff_re_le_coeffAbsUpper hk16
        convert mul_le_mul hc hpow (pow_nonneg hy k) ((abs_nonneg _).trans hc) using 1 <;> ring
    _ = (p0c : ℝ) * r := by
      rw [← Finset.sum_mul]
      norm_cast
#print axioms qRealTaylorDerivative_zero_le_p0c

theorem qRealTaylorDerivative_one_le_p1c
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (E8OriginRemainder.radius : ℝ)) :
    ‖E8OriginRealTaylorTransfer.qRealTaylorDerivative cert 1 y‖ ≤
      (E8OriginRemainder.p1c : ℝ) := by
  rw [qRealTaylorDerivative_eq_coefficients15 cert 1 (by omega)]
  calc
    ‖∑ k ∈ Finset.range 15,
        ((k + 1).factorial : ℝ) / k.factorial *
          (qTaylorCoeff (k + 1)).re * y ^ k‖ ≤
      ∑ k ∈ Finset.range 15,
        ‖((k + 1).factorial : ℝ) / k.factorial *
          (qTaylorCoeff (k + 1)).re * y ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range 15,
        ((k + 1).factorial : ℝ) / k.factorial *
          (coeffAbsUpper (k + 1) : ℝ) *
          (2 * (radius : ℝ)) ^ k := by
      gcongr with k hk
      have hk' : k < 15 := Finset.mem_range.mp hk
      have hk16 : k + 1 < 16 := by omega
      have hfac : 0 ≤ ((k + 1).factorial : ℝ) / k.factorial := by positivity
      have hpow : y ^ k ≤ (2 * (radius : ℝ)) ^ k := by
        gcongr
        linarith
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hfac,
        abs_of_nonneg hy]
      convert mul_le_mul_of_nonneg_left
        (mul_le_mul (abs_qTaylorCoeff_re_le_coeffAbsUpper hk16) hpow
          (pow_nonneg hy k)
          ((abs_nonneg _).trans (abs_qTaylorCoeff_re_le_coeffAbsUpper hk16))) hfac using 1 <;>
        ring
    _ = (p1c : ℝ) := by
      norm_num [p1c, coeffAbsUpper, radius, a1, a3, a5, a7, a9, a11, a13, a15,
        Finset.sum_range_succ]

theorem qRealTaylorDerivative_two_le_p2c
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (E8OriginRemainder.radius : ℝ)) :
    ‖E8OriginRealTaylorTransfer.qRealTaylorDerivative cert 2 y‖ ≤
      (E8OriginRemainder.p2c : ℝ) * r := by
  rw [qRealTaylorDerivative_eq_coefficients15 cert 2 (by omega)]
  calc
    ‖∑ k ∈ Finset.range 14,
        ((k + 2).factorial : ℝ) / k.factorial *
          (qTaylorCoeff (k + 2)).re * y ^ k‖ ≤
      ∑ k ∈ Finset.range 14,
        ‖((k + 2).factorial : ℝ) / k.factorial *
          (qTaylorCoeff (k + 2)).re * y ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range 14,
        ((k + 2).factorial : ℝ) / k.factorial *
          (coeffAbsUpper (k + 2) : ℝ) *
          2 ^ k * (radius : ℝ) ^ (k - 1) * r := by
      gcongr with k hk
      have hk' : k < 14 := Finset.mem_range.mp hk
      have hk16 : k + 2 < 16 := by omega
      have hfac : 0 ≤ ((k + 2).factorial : ℝ) / k.factorial := by positivity
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hfac,
        abs_of_nonneg hy]
      by_cases hk0 : k = 0
      · subst k
        rw [qTaylorCoeff_eq_zero_of_even (show Even 2 by decide)]
        norm_num [coeffAbsUpper]
      · have hpow := pow_le_two_mul_radius k (Nat.pos_of_ne_zero hk0)
          hy hyr hr hrR
        convert mul_le_mul_of_nonneg_left
          (mul_le_mul (abs_qTaylorCoeff_re_le_coeffAbsUpper hk16) hpow
            (pow_nonneg hy k)
            ((abs_nonneg _).trans (abs_qTaylorCoeff_re_le_coeffAbsUpper hk16))) hfac using 1 <;>
          ring
    _ = (p2c : ℝ) * r := by
      norm_num [p2c, coeffAbsUpper, radius, a1, a3, a5, a7, a9, a11, a13, a15,
        Finset.sum_range_succ, Finset.sum_Icc_succ_top]
      ring

theorem qRealTaylorDerivative_three_le_p3c
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (E8OriginRemainder.radius : ℝ)) :
    ‖E8OriginRealTaylorTransfer.qRealTaylorDerivative cert 3 y‖ ≤
      (E8OriginRemainder.p3c : ℝ) := by
  rw [qRealTaylorDerivative_eq_coefficients15 cert 3 (by omega)]
  calc
    ‖∑ k ∈ Finset.range 13,
        ((k + 3).factorial : ℝ) / k.factorial *
          (qTaylorCoeff (k + 3)).re * y ^ k‖ ≤
      ∑ k ∈ Finset.range 13,
        ‖((k + 3).factorial : ℝ) / k.factorial *
          (qTaylorCoeff (k + 3)).re * y ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range 13,
        ((k + 3).factorial : ℝ) / k.factorial *
          (coeffAbsUpper (k + 3) : ℝ) *
          (2 * (radius : ℝ)) ^ k := by
      gcongr with k hk
      have hk' : k < 13 := Finset.mem_range.mp hk
      have hk16 : k + 3 < 16 := by omega
      have hfac : 0 ≤ ((k + 3).factorial : ℝ) / k.factorial := by positivity
      have hpow : y ^ k ≤ (2 * (radius : ℝ)) ^ k := by
        gcongr
        linarith
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hfac,
        abs_of_nonneg hy]
      convert mul_le_mul_of_nonneg_left
        (mul_le_mul (abs_qTaylorCoeff_re_le_coeffAbsUpper hk16) hpow
          (pow_nonneg hy k)
          ((abs_nonneg _).trans (abs_qTaylorCoeff_re_le_coeffAbsUpper hk16))) hfac using 1 <;>
        ring
    _ = (p3c : ℝ) := by
      norm_num [p3c, coeffAbsUpper, radius, a1, a3, a5, a7, a9, a11, a13, a15,
        Finset.sum_range_succ, Finset.sum_Icc_succ_top]

#print axioms qRealTaylorDerivative_one_le_p1c
#print axioms qRealTaylorDerivative_two_le_p2c
#print axioms qRealTaylorDerivative_three_le_p3c

theorem qReal_derivative_taylor_tail_le_scaled
    (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 3)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ 2 / 25) :
    ‖iteratedDeriv j (qReal cert) y - qRealTaylorDerivative cert j y‖ ≤
      (tailError j : ℝ) * r ^ (17 - j) := by
  have hyR : y ≤ 4 / 25 := by linarith
  calc
    ‖iteratedDeriv j (qReal cert) y - qRealTaylorDerivative cert j y‖ ≤
        (q17AbsBound : ℝ) * y ^ (17 - j) / (17 - j).factorial :=
      qReal_derivative_exact_polynomial_remainder_le cert j
        (show j ≤ 5 by omega) hy hyR
    _ ≤ (q17AbsBound : ℝ) * (2 * r) ^ (17 - j) / (17 - j).factorial := by
      gcongr
      norm_num [q17AbsBound]
    _ = (tailError j : ℝ) * r ^ (17 - j) := by
      rw [mul_pow]
      norm_num [tailError, q17AbsBound]
      ring

#print axioms qReal_derivative_taylor_tail_le_scaled

theorem p_constants_nonnegative :
    (0 : ℝ) ≤ p0c ∧ (0 : ℝ) ≤ p1c ∧ (0 : ℝ) ≤ p2c ∧
      (0 : ℝ) ≤ p3c ∧ ∀ j ≤ 3, (0 : ℝ) ≤ tailError j := by
  constructor
  · norm_num [p0c, coeffAbsUpper, radius, a1, a3, a5, a7, a9, a11, a13, a15,
      Finset.sum_range_succ]
  constructor
  · norm_num [p1c, coeffAbsUpper, radius, a1, a3, a5, a7, a9, a11, a13, a15,
      Finset.sum_range_succ]
  constructor
  · norm_num [p2c, coeffAbsUpper, radius, a1, a3, a5, a7, a9, a11, a13, a15,
      Finset.sum_Icc_succ_top]
  constructor
  · norm_num [p3c, coeffAbsUpper, radius, a1, a3, a5, a7, a9, a11, a13, a15,
      Finset.sum_Icc_succ_top]
  · intro j hj
    interval_cases j <;> norm_num [tailError, q17AbsBound]

/-- A concrete `Q·Q'''` tail-product estimate, ready to instantiate at each
of the five argument pairs in `mixedProducts03`. -/
theorem qReal_tail03_product_perturbation_le
    (cert : QuantitativeCertificate) {x y r : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ 2 * r) (hy : 0 ≤ y) (hyr : y ≤ 2 * r)
    (hr : 0 ≤ r) (hrR : r ≤ (radius : ℝ)) :
    |qReal cert x * iteratedDeriv 3 (qReal cert) y -
        qRealTaylorDerivative cert 0 x * qRealTaylorDerivative cert 3 y| ≤
      ((p0c : ℝ) * tailError 3 * radius ^ 12 +
        (p3c : ℝ) * tailError 0 * radius ^ 14 +
        (tailError 0 : ℝ) * tailError 3 * radius ^ 28) * r ^ 3 := by
  have hp := p_constants_nonnegative
  have hrR' : r ≤ (2 / 25 : ℝ) := by simpa [radius] using hrR
  apply tail03_product_perturbation_le hp.1 hp.2.2.2.1 (hp.2.2.2.2 0 (by omega))
    (hp.2.2.2.2 3 (by omega)) hr hrR
  · simpa only [Real.norm_eq_abs] using
      qRealTaylorDerivative_zero_le_p0c cert hx hxr hr hrR
  · simpa only [Real.norm_eq_abs] using
      qRealTaylorDerivative_three_le_p3c cert hy hyr hr hrR
  · simpa only [Real.norm_eq_abs, iteratedDeriv_zero, Nat.sub_zero] using
      qReal_derivative_taylor_tail_le_scaled cert 0 (by omega) hx hxr hr hrR'
  · simpa only [Real.norm_eq_abs] using
      qReal_derivative_taylor_tail_le_scaled cert 3 (by omega) hy hyr hr hrR'

/-- A concrete `Q'·Q''` tail-product estimate, ready to instantiate at each
of the seven argument pairs in `mixedProducts12`. -/
theorem qReal_tail12_product_perturbation_le
    (cert : QuantitativeCertificate) {x y r : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ 2 * r) (hy : 0 ≤ y) (hyr : y ≤ 2 * r)
    (hr : 0 ≤ r) (hrR : r ≤ (radius : ℝ)) :
    |iteratedDeriv 1 (qReal cert) x * iteratedDeriv 2 (qReal cert) y -
        qRealTaylorDerivative cert 1 x * qRealTaylorDerivative cert 2 y| ≤
      ((p1c : ℝ) * tailError 2 * radius ^ 12 +
        (p2c : ℝ) * tailError 1 * radius ^ 14 +
        (tailError 1 : ℝ) * tailError 2 * radius ^ 28) * r ^ 3 := by
  have hp := p_constants_nonnegative
  have hrR' : r ≤ (2 / 25 : ℝ) := by simpa [radius] using hrR
  apply tail12_product_perturbation_le hp.2.1 hp.2.2.1
    (hp.2.2.2.2 1 (by omega)) (hp.2.2.2.2 2 (by omega)) hr hrR
  · simpa only [Real.norm_eq_abs] using
      qRealTaylorDerivative_one_le_p1c cert hx hxr hr hrR
  · simpa only [Real.norm_eq_abs] using
      qRealTaylorDerivative_two_le_p2c cert hy hyr hr hrR
  · simpa only [Real.norm_eq_abs] using
      qReal_derivative_taylor_tail_le_scaled cert 1 (by omega) hx hxr hr hrR'
  · simpa only [Real.norm_eq_abs] using
      qReal_derivative_taylor_tail_le_scaled cert 2 (by omega) hy hyr hr hrR'

#print axioms qReal_tail03_product_perturbation_le
#print axioms qReal_tail12_product_perturbation_le

/-- The five degree-15 Taylor products paired as `Q·Q'''`. -/
noncomputable def taylorProducts03 (cert : QuantitativeCertificate)
    (s t : ℝ) : ℕ → ℝ
  | 0 => qRealTaylorDerivative cert 0 s * qRealTaylorDerivative cert 3 (2 * s + t)
  | 1 => qRealTaylorDerivative cert 0 t * qRealTaylorDerivative cert 3 (s + t)
  | 2 => qRealTaylorDerivative cert 0 t * qRealTaylorDerivative cert 3 (2 * s + t)
  | 3 => qRealTaylorDerivative cert 0 (s + t) * qRealTaylorDerivative cert 3 (2 * s + t)
  | 4 => qRealTaylorDerivative cert 0 (2 * s + t) * qRealTaylorDerivative cert 3 (s + t)
  | _ => 0

/-- The seven degree-15 Taylor products paired as `Q'·Q''`. -/
noncomputable def taylorProducts12 (cert : QuantitativeCertificate)
    (s t : ℝ) : ℕ → ℝ
  | 0 => qRealTaylorDerivative cert 1 s * qRealTaylorDerivative cert 2 (2 * s + t)
  | 1 => qRealTaylorDerivative cert 2 s * qRealTaylorDerivative cert 1 t
  | 2 => qRealTaylorDerivative cert 2 s * qRealTaylorDerivative cert 1 (2 * s + t)
  | 3 => qRealTaylorDerivative cert 1 t * qRealTaylorDerivative cert 2 (s + t)
  | 4 => qRealTaylorDerivative cert 1 t * qRealTaylorDerivative cert 2 (2 * s + t)
  | 5 => qRealTaylorDerivative cert 1 (s + t) * qRealTaylorDerivative cert 2 (2 * s + t)
  | 6 => qRealTaylorDerivative cert 2 (s + t) * qRealTaylorDerivative cert 1 (2 * s + t)
  | _ => 0

/-- All twelve order-17 tail instantiations, aggregated with the exact retained
`18` and `28` weights. -/
theorem mixedKFormula_sub_taylor_le_remainder
    (cert : QuantitativeCertificate) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : s + t ≤ (radius : ℝ)) :
    |mixedKFormula (qReal cert) s t -
        weightedMixedProducts (taylorProducts03 cert s t)
          (taylorProducts12 cert s t)| ≤
      (remainderOverRadiusCubed : ℝ) * (s + t) ^ 3 := by
  rw [← weightedMixedProducts_mixedProducts_eq]
  rw [show (remainderOverRadiusCubed : ℝ) =
      18 * ((p0c : ℝ) * tailError 3 * radius ^ 12 +
        (p3c : ℝ) * tailError 0 * radius ^ 14 +
        (tailError 0 : ℝ) * tailError 3 * radius ^ 28) +
      28 * ((p1c : ℝ) * tailError 2 * radius ^ 12 +
        (p2c : ℝ) * tailError 1 * radius ^ 14 +
        (tailError 1 : ℝ) * tailError 2 * radius ^ 28) by
    norm_num [remainderOverRadiusCubed]]
  apply weightedMixedProducts_cubic_error_le
    (A := (p0c : ℝ) * tailError 3 * radius ^ 12 +
      (p3c : ℝ) * tailError 0 * radius ^ 14 +
      (tailError 0 : ℝ) * tailError 3 * radius ^ 28)
    (B := (p1c : ℝ) * tailError 2 * radius ^ 12 +
      (p2c : ℝ) * tailError 1 * radius ^ 14 +
      (tailError 1 : ℝ) * tailError 2 * radius ^ 28)
    (r := s + t)
  · intro i hi
    have hi' : i < 5 := Finset.mem_range.mp hi
    interval_cases i <;>
      simp only [mixedProducts03, taylorProducts03] <;>
      apply qReal_tail03_product_perturbation_le cert <;> linarith
  · intro i hi
    have hi' : i < 7 := Finset.mem_range.mp hi
    interval_cases i <;> simp only [mixedProducts12, taylorProducts12]
    · apply qReal_tail12_product_perturbation_le cert <;> linarith
    · simpa only [mul_comm] using
        (qReal_tail12_product_perturbation_le cert (x := t) (y := s)
          ht (by linarith) hs (by linarith) (add_nonneg hs ht) hR)
    · simpa only [mul_comm] using
        (qReal_tail12_product_perturbation_le cert
          (x := 2 * s + t) (y := s) (by linarith) (by linarith)
          hs (by linarith) (add_nonneg hs ht) hR)
    · apply qReal_tail12_product_perturbation_le cert <;> linarith
    · apply qReal_tail12_product_perturbation_le cert <;> linarith
    · apply qReal_tail12_product_perturbation_le cert <;> linarith
    · simpa only [mul_comm] using
        (qReal_tail12_product_perturbation_le cert
          (x := 2 * s + t) (y := s + t) (by linarith) (by linarith)
          (add_nonneg hs ht) (by linarith) (add_nonneg hs ht) hR)

#print axioms mixedKFormula_sub_taylor_le_remainder

theorem deltaSS_eq_mixedSSFormula_qReal
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate) {s t : ℝ}
    (hs : |s| < E8QuantitativeBranchBridge.yOuterRadius)
    (hst : |s + t| < E8QuantitativeBranchBridge.yOuterRadius)
    (h2st : |2 * s + t| < E8QuantitativeBranchBridge.yOuterRadius) :
    deltaSS (E8OriginPositiveConsumer.qReal cert) s t =
      mixedSSFormula (E8OriginPositiveConsumer.qReal cert) s t := by
  let Q := E8OriginPositiveConsumer.qReal cert
  change deltaSS Q s t = mixedSSFormula Q s t
  have hfun : (fun u => deltaS Q u t) =ᶠ[nhds s]
      (fun u => e8DeltaDerivS Q u t) := by
    simpa only [Q] using eventually_deltaS_qReal_eq_e8DeltaDerivS cert hs hst h2st
  have hD_layers := qReal_three_derivative_layers cert hs
  have hC_layers := qReal_three_derivative_layers cert hst
  have hB_layers := qReal_three_derivative_layers cert h2st
  unfold deltaSS
  rw [hfun.deriv_eq]
  let hlin : HasDerivAt (fun u : ℝ => 2 * u + t) 2 s :=
    by simpa only [id_eq, mul_one] using
      ((hasDerivAt_id s).const_mul 2).add_const t
  let hone : HasDerivAt (fun u : ℝ => u + t) 1 s :=
    (hasDerivAt_id s).add_const t
  have hB0 := hB_layers.1.comp s hlin
  have hB1 := hB_layers.2.1.comp s hlin
  have hC0 := hC_layers.1.comp s hone
  have hC1 := hC_layers.2.1.comp s hone
  have hD0 := hD_layers.1
  have hD1 := hD_layers.2.1
  have hA0 := hasDerivAt_const s (Q t)
  let rawS : ℝ → ℝ :=
    (((fun y => 2 * (iteratedDeriv 1 Q ∘ fun u => 2 * u + t) y) -
          iteratedDeriv 1 Q) *
        ((Q ∘ fun u => u + t) - fun _ => Q t) +
      ((Q ∘ fun u => 2 * u + t) - Q) *
        (iteratedDeriv 1 Q ∘ fun u => u + t)) -
    ((fun y => 2 * (iteratedDeriv 1 Q ∘ fun u => 2 * u + t) y) -
        (iteratedDeriv 1 Q ∘ fun u => u + t)) * (Q + fun _ => Q t) -
    ((Q ∘ fun u => 2 * u + t) - (Q ∘ fun u => u + t)) * iteratedDeriv 1 Q
  let dSS : ℝ :=
    (((2 * (iteratedDeriv 2 Q (2 * s + t) * 2) - iteratedDeriv 2 Q s) *
            (Q (s + t) - Q t) +
          (2 * iteratedDeriv 1 Q (2 * s + t) - iteratedDeriv 1 Q s) *
            iteratedDeriv 1 Q (s + t)) +
        ((iteratedDeriv 1 Q (2 * s + t) * 2 - iteratedDeriv 1 Q s) *
            iteratedDeriv 1 Q (s + t) +
          (Q (2 * s + t) - Q s) * iteratedDeriv 2 Q (s + t)) -
      ((2 * (iteratedDeriv 2 Q (2 * s + t) * 2) - iteratedDeriv 2 Q (s + t)) *
            (Q s + Q t) +
          (2 * iteratedDeriv 1 Q (2 * s + t) - iteratedDeriv 1 Q (s + t)) *
            iteratedDeriv 1 Q s)) -
    ((iteratedDeriv 1 Q (2 * s + t) * 2 - iteratedDeriv 1 Q (s + t)) *
          iteratedDeriv 1 Q s +
        (Q (2 * s + t) - Q (s + t)) * iteratedDeriv 2 Q s)
  have h : HasDerivAt rawS dSS s := by
    unfold rawS dSS
    simpa only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      mul_one, sub_zero, add_zero] using
    (((hB1.const_mul 2).sub hD1).mul (hC0.sub hA0)).add
      ((hB0.sub hD0).mul hC1) |>.sub
      (((hB1.const_mul 2).sub hC1).mul (hD0.add hA0)) |>.sub
      ((hB0.sub hC0).mul hD1)
  have heq : (fun u => e8DeltaDerivS Q u t) = rawS := by
    funext u
    simp only [rawS, e8DeltaDerivS, iteratedDeriv_one, Function.comp_apply,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  have hd : dSS = mixedSSFormula Q s t := by
    simp only [dSS, mixedSSFormula]
    ring
  rw [heq, h.deriv, hd]


/-- The exact twelve-term formula for the concrete analytic inverse needs only
local disc regularity.  This removes the global derivative-chain premise from
the E8-origin mixed-sign argument. -/
theorem deltaSST_eq_mixedKFormula_qReal
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate) {s t : ℝ}
    (hs : |s| < E8QuantitativeBranchBridge.yOuterRadius)
    (ht : |t| < E8QuantitativeBranchBridge.yOuterRadius)
    (hst : |s + t| < E8QuantitativeBranchBridge.yOuterRadius)
    (h2st : |2 * s + t| < E8QuantitativeBranchBridge.yOuterRadius) :
    deltaSST (E8OriginPositiveConsumer.qReal cert) s t =
      mixedKFormula (E8OriginPositiveConsumer.qReal cert) s t := by
  let Q := E8OriginPositiveConsumer.qReal cert
  change deltaSST Q s t = mixedKFormula Q s t
  let U : Set ℝ := {x | |x| < E8QuantitativeBranchBridge.yOuterRadius}
  have hU : IsOpen U := isOpen_lt continuous_abs continuous_const
  have hevA : ∀ᶠ v in nhds t, v ∈ U := hU.mem_nhds ht
  have hevC : ∀ᶠ v in nhds t, s + v ∈ U :=
    (hU.preimage (continuous_const.add continuous_id)).mem_nhds hst
  have hevB : ∀ᶠ v in nhds t, 2 * s + v ∈ U :=
    (hU.preimage (continuous_const.add continuous_id)).mem_nhds h2st
  have hfun : (fun v => deltaSS Q s v) =ᶠ[nhds t]
      (fun v => mixedSSFormula Q s v) := by
    filter_upwards [hevA, hevC, hevB] with v hvA hvC hvB
    simpa only [Q] using deltaSS_eq_mixedSSFormula_qReal cert hs hvC hvB
  have hA_layers := qReal_three_derivative_layers cert ht
  have hC_layers := qReal_three_derivative_layers cert hst
  have hB_layers := qReal_three_derivative_layers cert h2st
  unfold deltaSST
  rw [hfun.deriv_eq]
  let hB : HasDerivAt (fun v : ℝ => 2 * s + v) 1 t :=
    by simpa only [id_eq] using (hasDerivAt_id t).const_add (2 * s)
  let hC : HasDerivAt (fun v : ℝ => s + v) 1 t :=
    by simpa only [id_eq] using (hasDerivAt_id t).const_add s
  have hB0 := hB_layers.1.comp t hB
  have hB1 := hB_layers.2.1.comp t hB
  have hB2 := hB_layers.2.2.comp t hB
  have hC0 := hC_layers.1.comp t hC
  have hC1 := hC_layers.2.1.comp t hC
  have hC2 := hC_layers.2.2.comp t hC
  have hA0 := hA_layers.1
  have hA1 := hA_layers.2.1
  have hD0 := hasDerivAt_const t (Q s)
  have hD1 := hasDerivAt_const t (iteratedDeriv 1 Q s)
  have hD2 := hasDerivAt_const t (iteratedDeriv 2 Q s)
  let rawT : ℝ → ℝ := fun v =>
    (4 * iteratedDeriv 2 Q (2 * s + v) - iteratedDeriv 2 Q s) *
        (Q (s + v) - Q v) +
    2 * (2 * iteratedDeriv 1 Q (2 * s + v) - iteratedDeriv 1 Q s) *
        iteratedDeriv 1 Q (s + v) +
    (Q (2 * s + v) - Q s) * iteratedDeriv 2 Q (s + v) -
    (4 * iteratedDeriv 2 Q (2 * s + v) - iteratedDeriv 2 Q (s + v)) *
        (Q s + Q v) -
    2 * (2 * iteratedDeriv 1 Q (2 * s + v) - iteratedDeriv 1 Q (s + v)) *
        iteratedDeriv 1 Q s -
    (Q (2 * s + v) - Q (s + v)) * iteratedDeriv 2 Q s
  have h0 :=
    (((hB2.const_mul 4).sub hD2).mul (hC0.sub hA0)).add
      ((((hB1.const_mul 2).sub hD1).mul hC1).const_mul 2) |>.add
      ((hB0.sub hD0).mul hC2) |>.sub
      (((hB2.const_mul 4).sub hC2).mul (hD0.add hA0)) |>.sub
      ((((hB1.const_mul 2).sub hC1).mul hD1).const_mul 2) |>.sub
      ((hB0.sub hC0).mul hD2)
  have h := h0.congr_of_eventuallyEq (show rawT =ᶠ[nhds t] _ by
    filter_upwards with v
    simp only [rawT, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring)
  have heq : (fun v => mixedSSFormula Q s v) = rawT := by
    funext v
    simp only [rawT, mixedSSFormula]
  rw [heq, h.deriv]
  simp only [mixedKFormula, Function.comp_apply, Pi.add_apply, Pi.sub_apply,
    mul_one, sub_zero]
  ring


/-- Domain-shaped form of the local exact identity used by `MixedKTransfer`. -/
theorem deltaSST_eq_mixedKFormula_qReal_on_origin
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : s + t ≤ (2 / 25 : ℝ)) :
    deltaSST (E8OriginPositiveConsumer.qReal cert) s t =
      mixedKFormula (E8OriginPositiveConsumer.qReal cert) s t := by
  apply deltaSST_eq_mixedKFormula_qReal cert
  · rw [abs_of_nonneg hs]
    exact (show s ≤ (2 / 25 : ℝ) by linarith).trans_lt (by
      norm_num [E8QuantitativeBranchBridge.yOuterRadius])
  · rw [abs_of_nonneg ht]
    exact (show t ≤ (2 / 25 : ℝ) by linarith).trans_lt (by
      norm_num [E8QuantitativeBranchBridge.yOuterRadius])
  · rw [abs_of_nonneg (add_nonneg hs ht)]
    exact hR.trans_lt (by
      norm_num [E8QuantitativeBranchBridge.yOuterRadius])
  · rw [abs_of_nonneg (by linarith : 0 ≤ 2 * s + t)]
    exact (show 2 * s + t ≤ (4 / 25 : ℝ) by linarith).trans_lt (by
      norm_num [E8QuantitativeBranchBridge.yOuterRadius])

theorem mixedKFormula_linear_cubic (a b s t : ℝ) :
    mixedKFormula (fun x : ℝ => a * x + b * x ^ 3) s t =
      96 * b ^ 2 * (5 * s ^ 3 + 15 * s ^ 2 * t + 9 * s * t ^ 2 + t ^ 3) := by
  let f : ℝ → ℝ := fun x => a * x + b * x ^ 3
  have h1 : ∀ x : ℝ, deriv f x = a + 3 * b * x ^ 2 := by
    intro x
    have heq : f = (fun y : ℝ => a * y) + (fun y : ℝ => b * y ^ 3) := by
      funext y
      rfl
    rw [heq]
    have h := ((hasDerivAt_id x).const_mul a).add
      (((hasDerivAt_id x).pow 3).const_mul b)
    have hd := h.deriv
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one] at hd
    rw [hd]
    ring
  have h2 : ∀ x : ℝ, deriv (deriv f) x = 6 * b * x := by
    intro x
    rw [show deriv f = fun y => a + 3 * b * y ^ 2 by funext y; exact h1 y]
    have heq : (fun y : ℝ => a + 3 * b * y ^ 2) =
        (fun _ : ℝ => a) + (fun y : ℝ => (3 * b) * y ^ 2) := by
      funext y
      rfl
    rw [heq]
    have h := (hasDerivAt_const x a).add
      (((hasDerivAt_id x).pow 2).const_mul (3 * b))
    have hd := h.deriv
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one] at hd
    rw [hd]
    ring
  have h3 : ∀ x : ℝ, deriv (deriv (deriv f)) x = 6 * b := by
    intro x
    rw [show deriv (deriv f) = fun y => 6 * b * y by funext y; exact h2 y]
    have hd := ((hasDerivAt_id x).const_mul (6 * b)).deriv
    simpa only [id_eq, mul_one] using hd
  change mixedKFormula f s t = _
  simp only [mixedKFormula, iteratedDeriv_zero, iteratedDeriv_succ, h1, h2, h3]
  ring

/-- Comparing two linear/cubic jets removes both linear coefficients exactly;
only the difference of the squared cubic coefficients remains. -/
theorem mixedKFormula_linear_cubic_sub
    (a b a₀ b₀ s t : ℝ) :
    mixedKFormula (fun x : ℝ => a * x + b * x ^ 3) s t -
        mixedKFormula (fun x : ℝ => a₀ * x + b₀ * x ^ 3) s t =
      96 * (b ^ 2 - b₀ ^ 2) *
        (5 * s ^ 3 + 15 * s ^ 2 * t + 9 * s * t ^ 2 + t ^ 3) := by
  rw [mixedKFormula_linear_cubic, mixedKFormula_linear_cubic]
  ring

/-- Quantitative form of the combined low-jet cancellation. -/
theorem abs_mixedKFormula_linear_cubic_sub_le
    {a b a₀ b₀ B e s t : ℝ}
    (hB : 0 ≤ B) (he : 0 ≤ e) (hb : |b| ≤ B) (hb₀ : |b₀| ≤ B)
    (hbb₀ : |b - b₀| ≤ e) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |mixedKFormula (fun x : ℝ => a * x + b * x ^ 3) s t -
        mixedKFormula (fun x : ℝ => a₀ * x + b₀ * x ^ 3) s t| ≤
      960 * B * e * (s + t) ^ 3 := by
  rw [mixedKFormula_linear_cubic_sub, abs_mul, abs_mul]
  have hpoly0 : 0 ≤ 5 * s ^ 3 + 15 * s ^ 2 * t + 9 * s * t ^ 2 + t ^ 3 := by
    positivity
  have hpoly :
      5 * s ^ 3 + 15 * s ^ 2 * t + 9 * s * t ^ 2 + t ^ 3 ≤
        5 * (s + t) ^ 3 := by
    nlinarith [mul_nonneg hs (sq_nonneg t), pow_nonneg ht 3]
  have hsq : |b ^ 2 - b₀ ^ 2| ≤ 2 * B * e := by
    rw [show b ^ 2 - b₀ ^ 2 = (b + b₀) * (b - b₀) by ring, abs_mul]
    calc
      |b + b₀| * |b - b₀| ≤ (|b| + |b₀|) * e := by
        gcongr
        exact abs_add_le b b₀
      _ ≤ (B + B) * e := by gcongr
      _ = 2 * B * e := by ring
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 96 by norm_num), abs_of_nonneg hpoly0]
  calc
    96 * |b ^ 2 - b₀ ^ 2| *
        (5 * s ^ 3 + 15 * s ^ 2 * t + 9 * s * t ^ 2 + t ^ 3) ≤
      96 * (2 * B * e) * (5 * (s + t) ^ 3) := by gcongr
    _ = 960 * B * e * (s + t) ^ 3 := by ring

#print axioms mixedKFormula_linear_cubic_sub
#print axioms abs_mixedKFormula_linear_cubic_sub_le
/-- The universal linear/cubic contribution is controlled by a single cubic
radius factor on the nonnegative quadrant. -/
theorem abs_mixedKFormula_linear_cubic_le
    (a b : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |mixedKFormula (fun x : ℝ => a * x + b * x ^ 3) s t| ≤
      480 * b ^ 2 * (s + t) ^ 3 := by
  rw [mixedKFormula_linear_cubic]
  have hpoly :
      5 * s ^ 3 + 15 * s ^ 2 * t + 9 * s * t ^ 2 + t ^ 3 ≤
        5 * (s + t) ^ 3 := by
    nlinarith [mul_nonneg hs (sq_nonneg t), pow_nonneg ht 3]
  rw [abs_of_nonneg (mul_nonneg (by positivity) (by positivity))]
  calc
    96 * b ^ 2 * (5 * s ^ 3 + 15 * s ^ 2 * t + 9 * s * t ^ 2 + t ^ 3) ≤
        96 * b ^ 2 * (5 * (s + t) ^ 3) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = 480 * b ^ 2 * (s + t) ^ 3 := by ring

#print axioms abs_mixedKFormula_linear_cubic_le
#print axioms mixedKFormula_linear_cubic

/-! ## Final coefficient-box absorption

The full degree-15 product is split into its linear/cubic part and the
degree-5-through-15 cross terms.  The latter already carry three powers of
the origin radius, so they can be estimated term by term without losing the
low-jet cancellation above. -/

def lowProfileBound (A B R : ℝ) : ℕ → ℝ
  | 0 => 2 * A + 8 * B * R ^ 2
  | 1 => A + 12 * B * R ^ 2
  | 2 => 12 * B
  | 3 => 6 * B
  | _ => 0

theorem lowJetDerivative_zero_abs_le {a b A B y r R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r) (hrR : r ≤ R) :
    |lowJetDerivative a b 0 y| ≤ lowProfileBound A B R 0 * r := by
  have hR : 0 ≤ R := hr.trans hrR
  have hy1 := pow_le_two_mul_radius 1 (by omega) hy hyr hr hrR
  have hy3 := pow_le_two_mul_radius 3 (by omega) hy hyr hr hrR
  norm_num at hy1 hy3
  simp only [lowJetDerivative, lowProfileBound]
  calc
    |a * y + b * y ^ 3| ≤ |a * y| + |b * y ^ 3| := abs_add_le _ _
    _ = |a| * y + |b| * y ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hy, abs_pow, abs_of_nonneg hy]
    _ ≤ A * (2 * r) + B * (8 * R ^ 2 * r) := by gcongr
    _ = (2 * A + 8 * B * R ^ 2) * r := by ring

theorem lowJetDerivative_one_abs_le {a b A B y r R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r) (hrR : r ≤ R) :
    |lowJetDerivative a b 1 y| ≤ lowProfileBound A B R 1 := by
  have hR : 0 ≤ R := hr.trans hrR
  have hy2 : y ^ 2 ≤ 4 * R ^ 2 := by
    calc
      y ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ hy hyr 2
      _ ≤ (2 * R) ^ 2 := by gcongr
      _ = 4 * R ^ 2 := by ring
  simp only [lowJetDerivative, lowProfileBound]
  calc
    |a + 3 * b * y ^ 2| ≤ |a| + |3 * b * y ^ 2| := abs_add_le _ _
    _ = |a| + 3 * |b| * y ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hy]
      norm_num
    _ ≤ A + 3 * B * (4 * R ^ 2) := by gcongr
    _ = A + 12 * B * R ^ 2 := by ring

theorem lowJetDerivative_two_abs_le {a b B y r R : ℝ}
    (hB : 0 ≤ B) (hb : |b| ≤ B)
    (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r) (hrR : r ≤ R) :
    |lowJetDerivative a b 2 y| ≤ lowProfileBound 0 B R 2 * r := by
  simp only [lowJetDerivative, lowProfileBound]
  rw [abs_mul, abs_mul, abs_of_nonneg hy]
  norm_num
  calc
    6 * |b| * y ≤ 6 * B * (2 * r) := by gcongr
    _ = 12 * B * r := by ring

theorem lowJetDerivative_three_abs_le {a b B y : ℝ}
    (hB : 0 ≤ B) (hb : |b| ≤ B) :
    |lowJetDerivative a b 3 y| ≤ 6 * B := by
  simp only [lowJetDerivative]
  rw [abs_mul]
  norm_num
  gcongr

def lowSourceBound (j : ℕ) : ℝ :=
  lowProfileBound (coeffAbsUpper 1 : ℝ) (coeffAbsUpper 3 : ℝ) radius j

def lowCoeffError (j : ℕ) : ℝ :=
  lowProfileBound (sourceHalfWidth 1 : ℝ) (sourceHalfWidth 3 : ℝ) radius j

theorem low_constants_nonnegative (j : ℕ) (hj : j ≤ 3) :
    0 ≤ lowSourceBound j ∧ 0 ≤ lowCoeffError j := by
  unfold lowSourceBound lowCoeffError
  interval_cases j <;>
    norm_num [lowProfileBound, coeffAbsUpper, sourceHalfWidth, sourceBox,
      radius, a1, a3]

def crossPart (L H : ℕ → ℝ → ℝ) (j k : ℕ) (x y : ℝ) : ℝ :=
  L j x * H k y + H j x * L k y + H j x * H k y

theorem crossPart03_perturbation_le
    {L0 L H0 H : ℕ → ℝ → ℝ} {x y r R : ℝ}
    {P0 P3 U0 U3 E0 E3 e0 e3 : ℝ}
    (hP0 : 0 ≤ P0) (hP3 : 0 ≤ P3) (hU0 : 0 ≤ U0) (hU3 : 0 ≤ U3)
    (hE0 : 0 ≤ E0) (hE3 : 0 ≤ E3) (he0 : 0 ≤ e0) (he3 : 0 ≤ e3)
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hL0x : |L0 0 x| ≤ P0 * r) (hL0y : |L0 3 y| ≤ P3)
    (hH0x : |H0 0 x| ≤ U0 * r ^ 5) (hH0y : |H0 3 y| ≤ U3 * r ^ 2)
    (hLx : |L 0 x - L0 0 x| ≤ e0 * r) (hLy : |L 3 y - L0 3 y| ≤ e3)
    (hHx : |H 0 x - H0 0 x| ≤ E0 * r ^ 5)
    (hHy : |H 3 y - H0 3 y| ≤ E3 * r ^ 2) :
    |crossPart L H 0 3 x y - crossPart L0 H0 0 3 x y| ≤
      ((P0 * E3 + U3 * e0 + e0 * E3) +
        (U0 * e3 + P3 * E0 + E0 * e3) * R ^ 2 +
        (U0 * E3 + U3 * E0 + E0 * E3) * R ^ 4) * r ^ 3 := by
  have hR : 0 ≤ R := hr.trans hrR
  have h1 := product_perturbation_le
    (X := P0 * r) (Y := U3 * r ^ 2) (ex := e0 * r) (ey := E3 * r ^ 2)
    (mul_nonneg hP0 hr) (mul_nonneg hU3 (pow_nonneg hr 2))
    (mul_nonneg he0 hr) hL0x hH0y hLx hHy
  have h2 := product_perturbation_le
    (X := U0 * r ^ 5) (Y := P3) (ex := E0 * r ^ 5) (ey := e3)
    (mul_nonneg hU0 (pow_nonneg hr 5)) hP3
    (mul_nonneg hE0 (pow_nonneg hr 5)) hH0x hL0y hHx hLy
  have h3 := product_perturbation_le
    (X := U0 * r ^ 5) (Y := U3 * r ^ 2)
    (ex := E0 * r ^ 5) (ey := E3 * r ^ 2)
    (mul_nonneg hU0 (pow_nonneg hr 5)) (mul_nonneg hU3 (pow_nonneg hr 2))
    (mul_nonneg hE0 (pow_nonneg hr 5)) hH0x hH0y hHx hHy
  unfold crossPart
  have hsplit :
      (L 0 x * H 3 y + H 0 x * L 3 y + H 0 x * H 3 y) -
          (L0 0 x * H0 3 y + H0 0 x * L0 3 y + H0 0 x * H0 3 y) =
        (L 0 x * H 3 y - L0 0 x * H0 3 y) +
        (H 0 x * L 3 y - H0 0 x * L0 3 y) +
        (H 0 x * H 3 y - H0 0 x * H0 3 y) := by ring
  rw [hsplit]
  calc
    _ ≤ |L 0 x * H 3 y - L0 0 x * H0 3 y| +
        |H 0 x * L 3 y - H0 0 x * L0 3 y| +
        |H 0 x * H 3 y - H0 0 x * H0 3 y| := abs_add_three _ _ _
    _ ≤ (P0 * r) * (E3 * r ^ 2) + (U3 * r ^ 2) * (e0 * r) +
          (e0 * r) * (E3 * r ^ 2) +
        ((U0 * r ^ 5) * e3 + P3 * (E0 * r ^ 5) + (E0 * r ^ 5) * e3) +
        ((U0 * r ^ 5) * (E3 * r ^ 2) + (U3 * r ^ 2) * (E0 * r ^ 5) +
          (E0 * r ^ 5) * (E3 * r ^ 2)) := by linarith
    _ = ((P0 * E3 + U3 * e0 + e0 * E3) +
          (U0 * e3 + P3 * E0 + E0 * e3) * r ^ 2 +
          (U0 * E3 + U3 * E0 + E0 * E3) * r ^ 4) * r ^ 3 := by ring
    _ ≤ _ := by gcongr

theorem crossPart12_perturbation_le
    {L0 L H0 H : ℕ → ℝ → ℝ} {x y r R : ℝ}
    {P1 P2 U1 U2 E1 E2 e1 e2 : ℝ}
    (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (hU1 : 0 ≤ U1) (hU2 : 0 ≤ U2)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hL0x : |L0 1 x| ≤ P1) (hL0y : |L0 2 y| ≤ P2 * r)
    (hH0x : |H0 1 x| ≤ U1 * r ^ 4) (hH0y : |H0 2 y| ≤ U2 * r ^ 3)
    (hLx : |L 1 x - L0 1 x| ≤ e1) (hLy : |L 2 y - L0 2 y| ≤ e2 * r)
    (hHx : |H 1 x - H0 1 x| ≤ E1 * r ^ 4)
    (hHy : |H 2 y - H0 2 y| ≤ E2 * r ^ 3) :
    |crossPart L H 1 2 x y - crossPart L0 H0 1 2 x y| ≤
      ((P1 * E2 + U2 * e1 + e1 * E2) +
        (U1 * e2 + P2 * E1 + E1 * e2) * R ^ 2 +
        (U1 * E2 + U2 * E1 + E1 * E2) * R ^ 4) * r ^ 3 := by
  have hR : 0 ≤ R := hr.trans hrR
  have h1 := product_perturbation_le
    (X := P1) (Y := U2 * r ^ 3) (ex := e1) (ey := E2 * r ^ 3)
    hP1 (mul_nonneg hU2 (pow_nonneg hr 3)) he1 hL0x hH0y hLx hHy
  have h2 := product_perturbation_le
    (X := U1 * r ^ 4) (Y := P2 * r) (ex := E1 * r ^ 4) (ey := e2 * r)
    (mul_nonneg hU1 (pow_nonneg hr 4)) (mul_nonneg hP2 hr)
    (mul_nonneg hE1 (pow_nonneg hr 4)) hH0x hL0y hHx hLy
  have h3 := product_perturbation_le
    (X := U1 * r ^ 4) (Y := U2 * r ^ 3)
    (ex := E1 * r ^ 4) (ey := E2 * r ^ 3)
    (mul_nonneg hU1 (pow_nonneg hr 4)) (mul_nonneg hU2 (pow_nonneg hr 3))
    (mul_nonneg hE1 (pow_nonneg hr 4)) hH0x hH0y hHx hHy
  unfold crossPart
  have hsplit :
      (L 1 x * H 2 y + H 1 x * L 2 y + H 1 x * H 2 y) -
          (L0 1 x * H0 2 y + H0 1 x * L0 2 y + H0 1 x * H0 2 y) =
        (L 1 x * H 2 y - L0 1 x * H0 2 y) +
        (H 1 x * L 2 y - H0 1 x * L0 2 y) +
        (H 1 x * H 2 y - H0 1 x * H0 2 y) := by ring
  rw [hsplit]
  calc
    _ ≤ |L 1 x * H 2 y - L0 1 x * H0 2 y| +
        |H 1 x * L 2 y - H0 1 x * L0 2 y| +
        |H 1 x * H 2 y - H0 1 x * H0 2 y| := abs_add_three _ _ _
    _ ≤ P1 * (E2 * r ^ 3) + (U2 * r ^ 3) * e1 + e1 * (E2 * r ^ 3) +
        ((U1 * r ^ 4) * (e2 * r) + (P2 * r) * (E1 * r ^ 4) +
          (E1 * r ^ 4) * (e2 * r)) +
        ((U1 * r ^ 4) * (E2 * r ^ 3) + (U2 * r ^ 3) * (E1 * r ^ 4) +
          (E1 * r ^ 4) * (E2 * r ^ 3)) := by linarith
    _ = ((P1 * E2 + U2 * e1 + e1 * E2) +
          (U1 * e2 + P2 * E1 + E1 * e2) * r ^ 2 +
          (U1 * E2 + U2 * E1 + E1 * E2) * r ^ 4) * r ^ 3 := by ring
    _ ≤ _ := by gcongr

noncomputable def actualLow (cert : QuantitativeCertificate) : ℕ → ℝ → ℝ :=
  lowJetDerivative (qTaylorCoeff 1).re (qTaylorCoeff 3).re

noncomputable def sourceLow : ℕ → ℝ → ℝ :=
  lowJetDerivative (sourceCenter 1 : ℝ) (sourceCenter 3 : ℝ)

noncomputable def actualHigh (cert : QuantitativeCertificate) : ℕ → ℝ → ℝ :=
  qRealTaylorHighDerivative cert

noncomputable def sourceHigh : ℕ → ℝ → ℝ := qSourceTaylorHighDerivative

noncomputable def sourceHighBound (j : ℕ) : ℝ := highCoeffBound j + highCoeffError j

theorem sourceHighBound_nonnegative (j : ℕ) : 0 ≤ sourceHighBound j :=
  add_nonneg (highCoeffBound_nonnegative j) (highCoeffError_nonnegative j)

theorem sourceLow_zero_le {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r)
    (hr : 0 ≤ r) (hrR : r ≤ (radius : ℝ)) :
    |sourceLow 0 y| ≤ lowSourceBound 0 * r := by
  have hA : (0 : ℝ) ≤ (coeffAbsUpper 1 : ℝ) := by
    norm_num [coeffAbsUpper, a1]
  have hB : (0 : ℝ) ≤ (coeffAbsUpper 3 : ℝ) := by
    norm_num [coeffAbsUpper, a3]
  simpa only [sourceLow, lowSourceBound] using lowJetDerivative_zero_abs_le
    (A := (coeffAbsUpper 1 : ℝ)) (B := (coeffAbsUpper 3 : ℝ))
    (R := (radius : ℝ)) hA hB
    (abs_sourceCenter_le_coeffAbsUpper (n := 1) (by omega))
    (abs_sourceCenter_le_coeffAbsUpper (n := 3) (by omega)) hy hyr hr hrR

theorem sourceLow_one_le {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r)
    (hr : 0 ≤ r) (hrR : r ≤ (radius : ℝ)) :
    |sourceLow 1 y| ≤ lowSourceBound 1 := by
  have hA : (0 : ℝ) ≤ (coeffAbsUpper 1 : ℝ) := by
    norm_num [coeffAbsUpper, a1]
  have hB : (0 : ℝ) ≤ (coeffAbsUpper 3 : ℝ) := by
    norm_num [coeffAbsUpper, a3]
  simpa only [sourceLow, lowSourceBound] using lowJetDerivative_one_abs_le
    (A := (coeffAbsUpper 1 : ℝ)) (B := (coeffAbsUpper 3 : ℝ))
    (R := (radius : ℝ)) hA hB
    (abs_sourceCenter_le_coeffAbsUpper (n := 1) (by omega))
    (abs_sourceCenter_le_coeffAbsUpper (n := 3) (by omega)) hy hyr hr hrR

theorem sourceLow_two_le {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r)
    (hr : 0 ≤ r) (hrR : r ≤ (radius : ℝ)) :
    |sourceLow 2 y| ≤ lowSourceBound 2 * r := by
  have hB : (0 : ℝ) ≤ (coeffAbsUpper 3 : ℝ) := by
    norm_num [coeffAbsUpper, a3]
  simpa only [sourceLow, lowSourceBound, lowProfileBound] using lowJetDerivative_two_abs_le
    (B := (coeffAbsUpper 3 : ℝ)) (R := (radius : ℝ)) hB
    (abs_sourceCenter_le_coeffAbsUpper (n := 3) (by omega)) hy hyr hr hrR

theorem sourceLow_three_le (y : ℝ) : |sourceLow 3 y| ≤ lowSourceBound 3 := by
  have hB : (0 : ℝ) ≤ (coeffAbsUpper 3 : ℝ) := by
    norm_num [coeffAbsUpper, a3]
  simpa only [sourceLow, lowSourceBound, lowProfileBound] using lowJetDerivative_three_abs_le
    (B := (coeffAbsUpper 3 : ℝ)) hB
    (abs_sourceCenter_le_coeffAbsUpper (n := 3) (by omega))

theorem actualLow_sub_sourceLow_zero_le (cert : QuantitativeCertificate)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (radius : ℝ)) :
    |actualLow cert 0 y - sourceLow 0 y| ≤ lowCoeffError 0 * r := by
  have ha := qTaylorCoeff_re_sourceCenter_le (n := 1) (by omega)
  have hb := qTaylorCoeff_re_sourceCenter_le (n := 3) (by omega)
  have h := lowJetDerivative_zero_abs_le
    (a := (qTaylorCoeff 1).re - (sourceCenter 1 : ℝ))
    (b := (qTaylorCoeff 3).re - (sourceCenter 3 : ℝ))
    (A := sourceHalfWidth 1) (B := sourceHalfWidth 3)
    (R := radius)
    (by norm_num [sourceHalfWidth, sourceBox, a1])
    (by norm_num [sourceHalfWidth, sourceBox, a3]) ha hb hy hyr hr hrR
  convert h using 1 <;>
    simp only [actualLow, sourceLow, lowCoeffError, lowJetDerivative,
      lowProfileBound] <;> ring

theorem actualLow_sub_sourceLow_one_le (cert : QuantitativeCertificate)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (radius : ℝ)) :
    |actualLow cert 1 y - sourceLow 1 y| ≤ lowCoeffError 1 := by
  have ha := qTaylorCoeff_re_sourceCenter_le (n := 1) (by omega)
  have hb := qTaylorCoeff_re_sourceCenter_le (n := 3) (by omega)
  have h := lowJetDerivative_one_abs_le
    (a := (qTaylorCoeff 1).re - (sourceCenter 1 : ℝ))
    (b := (qTaylorCoeff 3).re - (sourceCenter 3 : ℝ))
    (A := sourceHalfWidth 1) (B := sourceHalfWidth 3)
    (R := radius)
    (by norm_num [sourceHalfWidth, sourceBox, a1])
    (by norm_num [sourceHalfWidth, sourceBox, a3]) ha hb hy hyr hr hrR
  convert h using 1 <;>
    simp only [actualLow, sourceLow, lowCoeffError, lowJetDerivative,
      lowProfileBound] <;> ring

theorem actualLow_sub_sourceLow_two_le (cert : QuantitativeCertificate)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (radius : ℝ)) :
    |actualLow cert 2 y - sourceLow 2 y| ≤ lowCoeffError 2 * r := by
  have hb := qTaylorCoeff_re_sourceCenter_le (n := 3) (by omega)
  have h := lowJetDerivative_two_abs_le
    (a := (qTaylorCoeff 1).re - (sourceCenter 1 : ℝ))
    (b := (qTaylorCoeff 3).re - (sourceCenter 3 : ℝ))
    (B := sourceHalfWidth 3) (R := radius)
    (by norm_num [sourceHalfWidth, sourceBox, a3]) hb hy hyr hr hrR
  convert h using 1 <;>
    simp only [actualLow, sourceLow, lowCoeffError, lowJetDerivative,
      lowProfileBound] <;> ring

theorem actualLow_sub_sourceLow_three_le (cert : QuantitativeCertificate) (y : ℝ) :
    |actualLow cert 3 y - sourceLow 3 y| ≤ lowCoeffError 3 := by
  have hb := qTaylorCoeff_re_sourceCenter_le (n := 3) (by omega)
  have h := lowJetDerivative_three_abs_le
    (a := (qTaylorCoeff 1).re - (sourceCenter 1 : ℝ))
    (b := (qTaylorCoeff 3).re - (sourceCenter 3 : ℝ))
    (B := sourceHalfWidth 3) (y := y)
    (by norm_num [sourceHalfWidth, sourceBox, a3]) hb
  convert h using 1 <;>
    simp only [actualLow, sourceLow, lowCoeffError, lowJetDerivative,
      lowProfileBound] <;> ring

theorem sourceHigh_le (cert : QuantitativeCertificate) (j : ℕ) (hj : j ≤ 3)
    {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ 2 * r) (hr : 0 ≤ r)
    (hrR : r ≤ (radius : ℝ)) :
    |sourceHigh j y| ≤ sourceHighBound j * r ^ (5 - j) := by
  have ha := qRealTaylorHighDerivative_le cert j hj hy hyr hr hrR
  have he := qRealTaylorHighDerivative_sub_source_le cert j hj hy hyr hr hrR
  have htri : |sourceHigh j y| ≤
      |actualHigh cert j y| + |actualHigh cert j y - sourceHigh j y| := by
    calc
      |sourceHigh j y| = |actualHigh cert j y -
          (actualHigh cert j y - sourceHigh j y)| := by congr 1 <;> ring
      _ ≤ _ := abs_sub _ _
  simpa only [actualHigh, sourceHigh, sourceHighBound, Real.norm_eq_abs,
    add_mul] using htri.trans (add_le_add ha he)

noncomputable def cross03ErrorFactor : ℝ :=
  (lowSourceBound 0 * highCoeffError 3 +
      sourceHighBound 3 * lowCoeffError 0 + lowCoeffError 0 * highCoeffError 3) +
  (sourceHighBound 0 * lowCoeffError 3 +
      lowSourceBound 3 * highCoeffError 0 + highCoeffError 0 * lowCoeffError 3) *
        radius ^ 2 +
  (sourceHighBound 0 * highCoeffError 3 +
      sourceHighBound 3 * highCoeffError 0 + highCoeffError 0 * highCoeffError 3) *
        radius ^ 4

noncomputable def cross12ErrorFactor : ℝ :=
  (lowSourceBound 1 * highCoeffError 2 +
      sourceHighBound 2 * lowCoeffError 1 + lowCoeffError 1 * highCoeffError 2) +
  (sourceHighBound 1 * lowCoeffError 2 +
      lowSourceBound 2 * highCoeffError 1 + highCoeffError 1 * lowCoeffError 2) *
        radius ^ 2 +
  (sourceHighBound 1 * highCoeffError 2 +
      sourceHighBound 2 * highCoeffError 1 + highCoeffError 1 * highCoeffError 2) *
        radius ^ 4

theorem concrete_crossPart03_le (cert : QuantitativeCertificate) {x y r : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ 2 * r) (hy : 0 ≤ y) (hyr : y ≤ 2 * r)
    (hr : 0 ≤ r) (hrR : r ≤ (radius : ℝ)) :
    |crossPart (actualLow cert) (actualHigh cert) 0 3 x y -
        crossPart sourceLow sourceHigh 0 3 x y| ≤ cross03ErrorFactor * r ^ 3 := by
  unfold cross03ErrorFactor
  apply crossPart03_perturbation_le
  · exact (low_constants_nonnegative 0 (by omega)).1
  · exact (low_constants_nonnegative 3 (by omega)).1
  · exact sourceHighBound_nonnegative 0
  · exact sourceHighBound_nonnegative 3
  · exact highCoeffError_nonnegative 0
  · exact highCoeffError_nonnegative 3
  · exact (low_constants_nonnegative 0 (by omega)).2
  · exact (low_constants_nonnegative 3 (by omega)).2
  · exact hr
  · exact hrR
  · exact sourceLow_zero_le hx hxr hr hrR
  · exact sourceLow_three_le y
  · exact sourceHigh_le cert 0 (by omega) hx hxr hr hrR
  · convert sourceHigh_le cert 3 (by omega) hy hyr hr hrR using 1 <;> norm_num
  · exact actualLow_sub_sourceLow_zero_le cert hx hxr hr hrR
  · exact actualLow_sub_sourceLow_three_le cert y
  · exact qRealTaylorHighDerivative_sub_source_le cert 0 (by omega) hx hxr hr hrR
  · convert qRealTaylorHighDerivative_sub_source_le cert 3 (by omega) hy hyr hr hrR using 1 <;>
      norm_num [actualHigh, sourceHigh, Real.norm_eq_abs]

theorem concrete_crossPart12_le (cert : QuantitativeCertificate) {x y r : ℝ}
    (hx : 0 ≤ x) (hxr : x ≤ 2 * r) (hy : 0 ≤ y) (hyr : y ≤ 2 * r)
    (hr : 0 ≤ r) (hrR : r ≤ (radius : ℝ)) :
    |crossPart (actualLow cert) (actualHigh cert) 1 2 x y -
        crossPart sourceLow sourceHigh 1 2 x y| ≤ cross12ErrorFactor * r ^ 3 := by
  unfold cross12ErrorFactor
  apply crossPart12_perturbation_le
  · exact (low_constants_nonnegative 1 (by omega)).1
  · exact (low_constants_nonnegative 2 (by omega)).1
  · exact sourceHighBound_nonnegative 1
  · exact sourceHighBound_nonnegative 2
  · exact highCoeffError_nonnegative 1
  · exact highCoeffError_nonnegative 2
  · exact (low_constants_nonnegative 1 (by omega)).2
  · exact (low_constants_nonnegative 2 (by omega)).2
  · exact hr
  · exact hrR
  · exact sourceLow_one_le hx hxr hr hrR
  · exact sourceLow_two_le hy hyr hr hrR
  · exact sourceHigh_le cert 1 (by omega) hx hxr hr hrR
  · exact sourceHigh_le cert 2 (by omega) hy hyr hr hrR
  · exact actualLow_sub_sourceLow_one_le cert hx hxr hr hrR
  · exact actualLow_sub_sourceLow_two_le cert hy hyr hr hrR
  · exact qRealTaylorHighDerivative_sub_source_le cert 1 (by omega) hx hxr hr hrR
  · exact qRealTaylorHighDerivative_sub_source_le cert 2 (by omega) hy hyr hr hrR

noncomputable def actualCrossProducts03 (cert : QuantitativeCertificate)
    (s t : ℝ) : ℕ → ℝ
  | 0 => crossPart (actualLow cert) (actualHigh cert) 0 3 s (2 * s + t)
  | 1 => crossPart (actualLow cert) (actualHigh cert) 0 3 t (s + t)
  | 2 => crossPart (actualLow cert) (actualHigh cert) 0 3 t (2 * s + t)
  | 3 => crossPart (actualLow cert) (actualHigh cert) 0 3 (s + t) (2 * s + t)
  | 4 => crossPart (actualLow cert) (actualHigh cert) 0 3 (2 * s + t) (s + t)
  | _ => 0

noncomputable def sourceCrossProducts03 (s t : ℝ) : ℕ → ℝ
  | 0 => crossPart sourceLow sourceHigh 0 3 s (2 * s + t)
  | 1 => crossPart sourceLow sourceHigh 0 3 t (s + t)
  | 2 => crossPart sourceLow sourceHigh 0 3 t (2 * s + t)
  | 3 => crossPart sourceLow sourceHigh 0 3 (s + t) (2 * s + t)
  | 4 => crossPart sourceLow sourceHigh 0 3 (2 * s + t) (s + t)
  | _ => 0

noncomputable def actualCrossProducts12 (cert : QuantitativeCertificate)
    (s t : ℝ) : ℕ → ℝ
  | 0 => crossPart (actualLow cert) (actualHigh cert) 1 2 s (2 * s + t)
  | 1 => crossPart (actualLow cert) (actualHigh cert) 1 2 t s
  | 2 => crossPart (actualLow cert) (actualHigh cert) 1 2 (2 * s + t) s
  | 3 => crossPart (actualLow cert) (actualHigh cert) 1 2 t (s + t)
  | 4 => crossPart (actualLow cert) (actualHigh cert) 1 2 t (2 * s + t)
  | 5 => crossPart (actualLow cert) (actualHigh cert) 1 2 (s + t) (2 * s + t)
  | 6 => crossPart (actualLow cert) (actualHigh cert) 1 2 (2 * s + t) (s + t)
  | _ => 0

noncomputable def sourceCrossProducts12 (s t : ℝ) : ℕ → ℝ
  | 0 => crossPart sourceLow sourceHigh 1 2 s (2 * s + t)
  | 1 => crossPart sourceLow sourceHigh 1 2 t s
  | 2 => crossPart sourceLow sourceHigh 1 2 (2 * s + t) s
  | 3 => crossPart sourceLow sourceHigh 1 2 t (s + t)
  | 4 => crossPart sourceLow sourceHigh 1 2 t (2 * s + t)
  | 5 => crossPart sourceLow sourceHigh 1 2 (s + t) (2 * s + t)
  | 6 => crossPart sourceLow sourceHigh 1 2 (2 * s + t) (s + t)
  | _ => 0

theorem weighted_actualCross_sub_sourceCross_le
    (cert : QuantitativeCertificate) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : s + t ≤ (radius : ℝ)) :
    |weightedMixedProducts (actualCrossProducts03 cert s t)
          (actualCrossProducts12 cert s t) -
        weightedMixedProducts (sourceCrossProducts03 s t)
          (sourceCrossProducts12 s t)| ≤
      (18 * cross03ErrorFactor + 28 * cross12ErrorFactor) * (s + t) ^ 3 := by
  apply weightedMixedProducts_cubic_error_le
  · intro i hi
    have hi' : i < 5 := Finset.mem_range.mp hi
    interval_cases i <;> simp only [actualCrossProducts03, sourceCrossProducts03] <;>
      apply concrete_crossPart03_le cert <;> linarith
  · intro i hi
    have hi' : i < 7 := Finset.mem_range.mp hi
    interval_cases i <;> simp only [actualCrossProducts12, sourceCrossProducts12] <;>
      apply concrete_crossPart12_le cert <;> linarith

theorem weighted_taylor_eq_low_add_cross (cert : QuantitativeCertificate) (s t : ℝ) :
    weightedMixedProducts (taylorProducts03 cert s t) (taylorProducts12 cert s t) =
      mixedKFormula
          (fun x => (qTaylorCoeff 1).re * x + (qTaylorCoeff 3).re * x ^ 3) s t +
        weightedMixedProducts (actualCrossProducts03 cert s t)
          (actualCrossProducts12 cert s t) := by
  rw [mixedKFormula_linear_cubic]
  simp only [weightedMixedProducts, taylorProducts03, taylorProducts12,
    actualCrossProducts03, actualCrossProducts12, weight03, weight12,
    Finset.sum_range_succ,
    qRealTaylorDerivative_eq_low_add_high cert 0 (by omega),
    qRealTaylorDerivative_eq_low_add_high cert 1 (by omega),
    qRealTaylorDerivative_eq_low_add_high cert 2 (by omega),
    qRealTaylorDerivative_eq_low_add_high cert 3 (by omega),
    actualLow, actualHigh, crossPart, lowJetDerivative]
  ring

noncomputable def sourceKFormula (s t : ℝ) : ℝ :=
  -4 * qSourceTaylorDerivative 0 s * qSourceTaylorDerivative 3 (2 * s + t) +
  qSourceTaylorDerivative 0 t * qSourceTaylorDerivative 3 (s + t) -
  8 * qSourceTaylorDerivative 0 t * qSourceTaylorDerivative 3 (2 * s + t) +
  4 * qSourceTaylorDerivative 0 (s + t) * qSourceTaylorDerivative 3 (2 * s + t) +
  qSourceTaylorDerivative 0 (2 * s + t) * qSourceTaylorDerivative 3 (s + t) -
  4 * qSourceTaylorDerivative 1 s * qSourceTaylorDerivative 2 (2 * s + t) +
  qSourceTaylorDerivative 2 s * qSourceTaylorDerivative 1 t -
  qSourceTaylorDerivative 2 s * qSourceTaylorDerivative 1 (2 * s + t) +
  qSourceTaylorDerivative 1 t * qSourceTaylorDerivative 2 (s + t) -
  8 * qSourceTaylorDerivative 1 t * qSourceTaylorDerivative 2 (2 * s + t) +
  8 * qSourceTaylorDerivative 1 (s + t) * qSourceTaylorDerivative 2 (2 * s + t) +
  5 * qSourceTaylorDerivative 2 (s + t) * qSourceTaylorDerivative 1 (2 * s + t)

theorem sourceKFormula_eq_low_add_cross (s t : ℝ) :
    sourceKFormula s t =
      mixedKFormula
          (fun x => (sourceCenter 1 : ℝ) * x + (sourceCenter 3 : ℝ) * x ^ 3) s t +
        weightedMixedProducts (sourceCrossProducts03 s t) (sourceCrossProducts12 s t) := by
  rw [mixedKFormula_linear_cubic]
  simp only [sourceKFormula, weightedMixedProducts, sourceCrossProducts03,
    sourceCrossProducts12, weight03, weight12, Finset.sum_range_succ,
    qSourceTaylorDerivative_eq_low_add_high 0 (by omega),
    qSourceTaylorDerivative_eq_low_add_high 1 (by omega),
    qSourceTaylorDerivative_eq_low_add_high 2 (by omega),
    qSourceTaylorDerivative_eq_low_add_high 3 (by omega),
    sourceLow, sourceHigh, crossPart, lowJetDerivative]
  ring

noncomputable def coefficientCubicErrorFactor : ℝ :=
  960 * (coeffAbsUpper 3 : ℝ) * (sourceHalfWidth 3 : ℝ) +
    18 * cross03ErrorFactor + 28 * cross12ErrorFactor

theorem coefficientCubicErrorFactor_nonnegative : 0 ≤ coefficientCubicErrorFactor := by
  norm_num [coefficientCubicErrorFactor, cross03ErrorFactor, cross12ErrorFactor,
    lowSourceBound, lowCoeffError, lowProfileBound, sourceHighBound,
    highCoeffBound, highCoeffError, coeffAbsUpper, sourceCenter, sourceHalfWidth,
    sourceBox, radius, a1, a3, a5, a7, a9, a11, a13, a15,
    Finset.sum_range_succ]

theorem coefficientCubicErrorFactor_lt :
    coefficientCubicErrorFactor < (1 / 10 ^ 35 : ℝ) := by
  norm_num [coefficientCubicErrorFactor, cross03ErrorFactor, cross12ErrorFactor,
    lowSourceBound, lowCoeffError, lowProfileBound, sourceHighBound,
    highCoeffBound, highCoeffError, coeffAbsUpper, sourceCenter, sourceHalfWidth,
    sourceBox, radius, a1, a3, a5, a7, a9, a11, a13, a15,
    Finset.sum_range_succ]

theorem weighted_taylor_sub_sourceKFormula_le_coefficient
    (cert : QuantitativeCertificate) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : s + t ≤ (radius : ℝ)) :
    |weightedMixedProducts (taylorProducts03 cert s t) (taylorProducts12 cert s t) -
        sourceKFormula s t| ≤ coefficientCubicErrorFactor * (s + t) ^ 3 := by
  rw [weighted_taylor_eq_low_add_cross, sourceKFormula_eq_low_add_cross]
  have hb : |(qTaylorCoeff 3).re| ≤ (coeffAbsUpper 3 : ℝ) :=
    abs_qTaylorCoeff_re_le_coeffAbsUpper (by omega)
  have hb0 : |(sourceCenter 3 : ℝ)| ≤ (coeffAbsUpper 3 : ℝ) :=
    abs_sourceCenter_le_coeffAbsUpper (by omega)
  have hbe := qTaylorCoeff_re_sourceCenter_le (n := 3) (by omega)
  have hlow := abs_mixedKFormula_linear_cubic_sub_le
    (a := (qTaylorCoeff 1).re) (b := (qTaylorCoeff 3).re)
    (a₀ := (sourceCenter 1 : ℝ)) (b₀ := (sourceCenter 3 : ℝ))
    (B := (coeffAbsUpper 3 : ℝ)) (e := (sourceHalfWidth 3 : ℝ))
    (by norm_num [coeffAbsUpper, a3])
    (by norm_num [sourceHalfWidth, sourceBox, a3]) hb hb0 hbe hs ht
  have hcross := weighted_actualCross_sub_sourceCross_le cert hs ht hR
  have hsplit :
      (mixedKFormula
          (fun x => (qTaylorCoeff 1).re * x + (qTaylorCoeff 3).re * x ^ 3) s t +
          weightedMixedProducts (actualCrossProducts03 cert s t)
            (actualCrossProducts12 cert s t)) -
        (mixedKFormula
          (fun x => (sourceCenter 1 : ℝ) * x + (sourceCenter 3 : ℝ) * x ^ 3) s t +
          weightedMixedProducts (sourceCrossProducts03 s t)
            (sourceCrossProducts12 s t)) =
      (mixedKFormula
          (fun x => (qTaylorCoeff 1).re * x + (qTaylorCoeff 3).re * x ^ 3) s t -
        mixedKFormula
          (fun x => (sourceCenter 1 : ℝ) * x + (sourceCenter 3 : ℝ) * x ^ 3) s t) +
      (weightedMixedProducts (actualCrossProducts03 cert s t)
          (actualCrossProducts12 cert s t) -
        weightedMixedProducts (sourceCrossProducts03 s t)
          (sourceCrossProducts12 s t)) := by ring
  change |(mixedKFormula
          (fun x => (qTaylorCoeff 1).re * x + (qTaylorCoeff 3).re * x ^ 3) s t +
          weightedMixedProducts (actualCrossProducts03 cert s t)
            (actualCrossProducts12 cert s t)) -
        (mixedKFormula
          (fun x => (sourceCenter 1 : ℝ) * x + (sourceCenter 3 : ℝ) * x ^ 3) s t +
          weightedMixedProducts (sourceCrossProducts03 s t)
            (sourceCrossProducts12 s t))| ≤ _
  rw [hsplit]
  calc
    _ ≤ |mixedKFormula
          (fun x => (qTaylorCoeff 1).re * x + (qTaylorCoeff 3).re * x ^ 3) s t -
        mixedKFormula
          (fun x => (sourceCenter 1 : ℝ) * x + (sourceCenter 3 : ℝ) * x ^ 3) s t| +
        |weightedMixedProducts (actualCrossProducts03 cert s t)
            (actualCrossProducts12 cert s t) -
          weightedMixedProducts (sourceCrossProducts03 s t)
            (sourceCrossProducts12 s t)| := abs_add_le _ _
    _ ≤ 960 * (coeffAbsUpper 3 : ℝ) * (sourceHalfWidth 3 : ℝ) * (s + t) ^ 3 +
        (18 * cross03ErrorFactor + 28 * cross12ErrorFactor) * (s + t) ^ 3 :=
      add_le_add hlow hcross
    _ = coefficientCubicErrorFactor * (s + t) ^ 3 := by
      unfold coefficientCubicErrorFactor
      ring

#print axioms coefficientCubicErrorFactor_lt
#print axioms weighted_taylor_sub_sourceKFormula_le_coefficient

#print axioms deltaSST_eq_mixedKFormula_qReal_on_origin
#print axioms qReal_three_derivative_layers
#print axioms deltaSST_eq_mixedKFormula
#print axioms mixedK_product_weights
#print axioms weightedMixedProducts_sub_le_combinedCubicErrorFactor

end GeneralCK.Certificates.E8OriginMixedKTransfer

end


