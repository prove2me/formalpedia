-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorDeltaJet
-- name    : CK_GeneralCK_Certificates_E8CompactAnchorDeltaJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:28:04.539811+00:00
-- url     : https://prove2.me/theorems/6a20eaae-97cc-4986-9831-41838e7ebc51
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8CompactAnchorDeltaJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8CompactAnchorDeltaJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8CompactAnchorDeltaJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8CompactAnchorDeltaJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8CompactAnchorDeltaJet.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisDeltaDirectionalJet

-- ===== source module GeneralCK.Certificates.E8CompactAnchorDeltaJet =====
section

/-!
# Regular E8 determinant directional jet through order three

The t-axis jet starts with the first t derivative.  This companion starts
with the determinant itself, retaining the factored expression used by the
compact-anchor pilot and all four canonical inverse arguments.
-/

namespace GeneralCK.Certificates.E8CompactAnchorDeltaJet

open GeneralCK Set E8TAxisDeltaDirectionalJet

/-- The exact factored determinant graph, with A=Q(t), B=Q(2s+t),
C=Q(s+t), and D=Q(s). -/
def deltaGraph (a b c d : Jet5) : Jet5 :=
  sub ((sub b d).mul (sub c a)) ((sub b c).mul (d.add a))

theorem deltaGraph_sound4At {a b c d : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u)
    (hc : Sound4At c u) (hd : Sound4At d u) :
    Sound4At (deltaGraph a b c d) u :=
  ((hb.sub hd).mul (hc.sub ha)).sub ((hb.sub hc).mul (hd.add ha))

/-- Along the affine ray `(s,t)=(s0+ds*u,t0+dt*u)`. -/
noncomputable def deltaJet (s0 t0 ds dt : ℝ) : Jet5 :=
  deltaGraph
    (affine qJet t0 dt)
    (affine qJet (2 * s0 + t0) (2 * ds + dt))
    (affine qJet (s0 + t0) (ds + dt))
    (affine qJet s0 ds)

theorem deltaJet_sound4At {s0 t0 ds dt u : ℝ}
    (h : InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    Sound4At (deltaJet s0 t0 ds dt) u := by
  have hB : (2 * s0 + t0) + (2 * ds + dt) * u ∈ e8SlopeRange := by
    rw [show (2 * s0 + t0) + (2 * ds + dt) * u =
      2 * (s0 + ds * u) + (t0 + dt * u) by ring]
    exact h.2.1
  have hC : (s0 + t0) + (ds + dt) * u ∈ e8SlopeRange := by
    rw [show (s0 + t0) + (ds + dt) * u =
      (s0 + ds * u) + (t0 + dt * u) by ring]
    exact h.2.2.1
  exact deltaGraph_sound4At
    (qJet_sound4At h.1).affine (qJet_sound4At hB).affine
    (qJet_sound4At hC).affine (qJet_sound4At h.2.2.2).affine

theorem deltaJet_sound4On {s0 t0 ds dt : ℝ} {S : Set ℝ}
    (h : ∀ u ∈ S, InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    Sound4On (deltaJet s0 t0 ds dt) S :=
  fun u hu => deltaJet_sound4At (h u hu)

/-- The value component is definitionally the actual determinant with the
canonical `e8Q`, independent of slope-range assumptions. -/
theorem deltaJet_d0_eq_e8Delta (s0 t0 ds dt u : ℝ) :
    (deltaJet s0 t0 ds dt).d0 u =
      e8Delta e8Q (s0 + ds * u) (t0 + dt * u) := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, qJet_d0, e8Delta]
  rw [show (2 * s0 + t0) + (2 * ds + dt) * u =
      2 * (s0 + ds * u) + (t0 + dt * u) by ring,
    show (s0 + t0) + (ds + dt) * u =
      (s0 + ds * u) + (t0 + dt * u) by ring]
  ring

/-- A vertical path jet evaluates the same center/whole pure-t
coefficient at its current t coordinate, with the correct raw scaling. -/
theorem vertical_d0_scaling (a tm dt v : ℝ) :
    (deltaJet a tm 0 dt).d0 v =
      (deltaJet a (tm + dt * v) 0 1).d0 0 := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, zero_mul, mul_zero, one_mul, add_zero, zero_add]
  rw [show 2 * a + tm + dt * v = 2 * a + (tm + dt * v) by ring,
    show a + tm + dt * v = a + (tm + dt * v) by ring]

theorem vertical_d1_scaling (a tm dt v : ℝ) :
    (deltaJet a tm 0 dt).d1 v =
      (deltaJet a (tm + dt * v) 0 1).d1 0 * dt := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, zero_mul, mul_zero, one_mul, add_zero, zero_add]
  rw [show 2 * a + tm + dt * v = 2 * a + (tm + dt * v) by ring,
    show a + tm + dt * v = a + (tm + dt * v) by ring]
  ring

theorem vertical_d2_scaling (a tm dt v : ℝ) :
    (deltaJet a tm 0 dt).d2 v =
      (deltaJet a (tm + dt * v) 0 1).d2 0 * dt ^ 2 := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, zero_mul, mul_zero, one_mul, add_zero, zero_add]
  rw [show 2 * a + tm + dt * v = 2 * a + (tm + dt * v) by ring,
    show a + tm + dt * v = a + (tm + dt * v) by ring]
  ring

theorem vertical_d3_scaling (a tm dt v : ℝ) :
    (deltaJet a tm 0 dt).d3 v =
      (deltaJet a (tm + dt * v) 0 1).d3 0 * dt ^ 3 := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, zero_mul, mul_zero, one_mul, add_zero, zero_add]
  rw [show 2 * a + tm + dt * v = 2 * a + (tm + dt * v) by ring,
    show a + tm + dt * v = a + (tm + dt * v) by ring]
  ring

#print axioms deltaGraph_sound4At
#print axioms deltaJet_sound4On
#print axioms deltaJet_d0_eq_e8Delta
#print axioms vertical_d0_scaling
#print axioms vertical_d1_scaling
#print axioms vertical_d2_scaling
#print axioms vertical_d3_scaling

end GeneralCK.Certificates.E8CompactAnchorDeltaJet

end


