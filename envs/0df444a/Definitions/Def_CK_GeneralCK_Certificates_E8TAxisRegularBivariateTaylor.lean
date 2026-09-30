-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularBivariateTaylor
-- name    : CK_GeneralCK_Certificates_E8TAxisRegularBivariateTaylor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:37:50.994563+00:00
-- url     : https://prove2.me/theorems/7e40db76-9d9c-4048-b2cd-ec4e6fb04a95
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRegularBivariateTaylor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRegularBivariateTaylor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRegularBivariateTaylor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRegularBivariateTaylor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRegularBivariateTaylor.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularDirectionalJet
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisMixedCoefficients
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCenteredReplaySoundness

-- ===== source module GeneralCK.Certificates.E8TAxisRegularBivariateTaylor =====
section

/-!
# Boundary-aware bivariate Taylor semantics for the regular E8 t derivative

The mixed coefficients are integer polynomials in the canonical inverse jet.
The identities below prove that they give the raw directional derivatives
of the actual t derivative, with the binomial weights required by the
fourth-order centered replay.
-/

namespace GeneralCK.Certificates.E8TAxisRegularBivariateTaylor

open GeneralCK E8TAxisRegularDirectionalJet E8TAxisRegularGermJet E8TAxisMixedCoefficients
open E8TAxisCenteredReplaySoundness E8TAxisOneCellArithmetic Set

set_option maxHeartbeats 2000000

theorem ray_d0 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d0 u = mixed regularQJet (s0 + x*u) (t0 + y*u) 0 1 := by
  simp only [deltaTJet, E8TAxisDeltaDirectionalJet.deltaTGraph, E8TAxisDeltaDirectionalJet.sub, E8TAxisDeltaDirectionalJet.affine, regularQPrimeJet, E8TAxisDeltaDirectionalJet.shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

theorem ray_d1 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d1 u =
      mixed regularQJet (s0+x*u) (t0+y*u) 0 2 * y +
      mixed regularQJet (s0+x*u) (t0+y*u) 1 1 * x := by
  simp only [deltaTJet, E8TAxisDeltaDirectionalJet.deltaTGraph, E8TAxisDeltaDirectionalJet.sub, E8TAxisDeltaDirectionalJet.affine, regularQPrimeJet, E8TAxisDeltaDirectionalJet.shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

theorem ray_d2 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d2 u =
      mixed regularQJet (s0+x*u) (t0+y*u) 0 3 * y^2 +
      2 * mixed regularQJet (s0+x*u) (t0+y*u) 1 2 * x*y +
      mixed regularQJet (s0+x*u) (t0+y*u) 2 1 * x^2 := by
  simp only [deltaTJet, E8TAxisDeltaDirectionalJet.deltaTGraph, E8TAxisDeltaDirectionalJet.sub, E8TAxisDeltaDirectionalJet.affine, regularQPrimeJet, E8TAxisDeltaDirectionalJet.shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

theorem ray_d3 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d3 u =
      mixed regularQJet (s0+x*u) (t0+y*u) 0 4 * y^3 +
      3 * mixed regularQJet (s0+x*u) (t0+y*u) 1 3 * x*y^2 +
      3 * mixed regularQJet (s0+x*u) (t0+y*u) 2 2 * x^2*y +
      mixed regularQJet (s0+x*u) (t0+y*u) 3 1 * x^3 := by
  simp only [deltaTJet, E8TAxisDeltaDirectionalJet.deltaTGraph, E8TAxisDeltaDirectionalJet.sub, E8TAxisDeltaDirectionalJet.affine, regularQPrimeJet, E8TAxisDeltaDirectionalJet.shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

theorem ray_d4 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d4 u =
      mixed regularQJet (s0+x*u) (t0+y*u) 0 5 * y^4 +
      4 * mixed regularQJet (s0+x*u) (t0+y*u) 1 4 * x*y^3 +
      6 * mixed regularQJet (s0+x*u) (t0+y*u) 2 3 * x^2*y^2 +
      4 * mixed regularQJet (s0+x*u) (t0+y*u) 3 2 * x^3*y +
      mixed regularQJet (s0+x*u) (t0+y*u) 4 1 * x^4 := by
  simp only [deltaTJet, E8TAxisDeltaDirectionalJet.deltaTGraph, E8TAxisDeltaDirectionalJet.sub, E8TAxisDeltaDirectionalJet.affine, regularQPrimeJet, E8TAxisDeltaDirectionalJet.shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

/-- The center and whole-segment mixed coefficient boxes are the only
remaining numerical premises. All differentiation and Taylor semantics
in this implication are proved for the concrete regular E8 inverse. -/
theorem centeredReplay_contains {s0 t0 x y : ℝ}
    (hrange : ∀ u ∈ Icc (0 : ℝ) 1, InputsInRange (s0+x*u) (t0+y*u))
    (hc : CenterEnclosed (mixed regularQJet s0 t0))
    (hr : ∀ u ∈ Ioo (0 : ℝ) 1,
      RemainderEnclosed (mixed regularQJet (s0+x*u) (t0+y*u)))
    (hx : ds.Contains x) (hy : dt.Contains y) :
    centeredReplay.Contains (e8RegularDeltaT (s0+x) (t0+y)) := by
  have hj := deltaTJet_sound4On hrange
  have henclosed : centeredReplay.Contains ((deltaTJet s0 t0 x y).d0 1) := by
    apply endpoint_mem
      (fun u hu => (hj u hu).1) (fun u hu => (hj u hu).2.1)
      (fun u hu => (hj u hu).2.2.1) (fun u hu => (hj u hu).2.2.2)
      (c := mixed regularQJet s0 t0)
      (r := fun u => mixed regularQJet (s0+x*u) (t0+y*u))
    · simpa only [mul_zero, add_zero] using ray_d0 s0 t0 x y 0
    · simpa only [mul_zero, add_zero] using ray_d1 s0 t0 x y 0
    · simpa only [mul_zero, add_zero] using ray_d2 s0 t0 x y 0
    · simpa only [mul_zero, add_zero] using ray_d3 s0 t0 x y 0
    · intro u _
      exact ray_d4 s0 t0 x y u
    · exact hc
    · exact hr
    · exact hx
    · exact hy
  have heq := deltaTJet_d0_eq_regular (hrange 1 (by norm_num))
  rw [heq] at henclosed
  simpa only [mul_one] using henclosed

#print axioms ray_d4
#print axioms centeredReplay_contains

end GeneralCK.Certificates.E8TAxisRegularBivariateTaylor

end


