-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_RayS
-- name    : CK_CKLaneC_SAxis_RayS
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:40:42.19645+00:00
-- url     : https://prove2.me/theorems/aa6f2b43-ed84-4120-a2b1-5cb51d41f130
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.RayS` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.RayS` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.RayS` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.RayS (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/RayS.lean)

import Definitions.Def_CK_CKLaneC_SAxis_MixedS
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisDeltaDirectionalJet
import Definitions.Def_CK_GeneralCK_PureGapE8SecondSJet

-- ===== source module CKLaneC.SAxis.RayS =====
section

/-!
# Lane C (sAxis): directional jet of the regular second `s` derivative of the E8 determinant

For an arbitrary raw jet `q` (in practice the canonical inverse jet or the regular inverse jet
`regularQJet`, which is sound also at slope `0`), `deltaSSJetOf q s0 t0 x y` is the jet-algebra
graph of `e8SecondSJet` along the ray `(s,t) = (s0 + x*u, t0 + y*u)`.  Its first three derivative
links are sound as soon as `q` is sound at the four ray arguments, its ray derivatives are the
binomial combinations of the raw mixed coefficients `mixedS q`, and an order-three Lagrange
remainder gives the corner Taylor identity.  When `q` agrees with `e8RegularQ` (through the
second derivative) at positive admissible slopes, the zeroth component is the regular second
`s` derivative `e8RegularDeltaSS`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace CKLaneC.SAxis

open Set GeneralCK GeneralCK.Certificates E8InverseJet5Bridge
open E8TAxisDeltaDirectionalJet

/-! ## Three derivative links -/

def Sound3At (j : Jet5) (u : ℝ) : Prop :=
  HasDerivAt j.d0 (j.d1 u) u ∧ HasDerivAt j.d1 (j.d2 u) u ∧ HasDerivAt j.d2 (j.d3 u) u

theorem sound3At_of_sound4At {j : Jet5} {u : ℝ} (h : Sound4At j u) : Sound3At j u :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem sound3At_const (c u : ℝ) : Sound3At (Jet5.const c) u :=
  sound3At_of_sound4At (sound4At_const c u)

theorem Sound3At.add {a b : Jet5} {u : ℝ}
    (ha : Sound3At a u) (hb : Sound3At b u) : Sound3At (a.add b) u :=
  ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.add hb.2.2⟩

theorem Sound3At.neg {a : Jet5} {u : ℝ} (ha : Sound3At a u) : Sound3At a.neg u :=
  ⟨ha.1.neg, ha.2.1.neg, ha.2.2.neg⟩

theorem Sound3At.sub {a b : Jet5} {u : ℝ}
    (ha : Sound3At a u) (hb : Sound3At b u) : Sound3At (sub a b) u :=
  ha.add hb.neg

theorem Sound3At.mul {a b : Jet5} {u : ℝ}
    (ha : Sound3At a u) (hb : Sound3At b u) : Sound3At (a.mul b) u := by
  refine ⟨ha.1.mul hb.1, ?_, ?_⟩
  · convert! (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1) using 1 <;>
      simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext v; simp <;> ring) | ring
  · have h := ((ha.2.2.mul hb.1).add
      ((ha.2.1.mul hb.2.1).const_mul 2)).add (ha.1.mul hb.2.2)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext v; simp <;> ring) | ring

theorem Sound3At.affine {j : Jet5} {c m u : ℝ}
    (h : Sound3At j (c + m * u)) : Sound3At (affine j c m) u := by
  have hi : HasDerivAt (fun v : ℝ => c + m * v) m u := by
    convert! (hasDerivAt_const u c).add ((hasDerivAt_id u).const_mul m) using 1 <;>
      simp
  refine ⟨?_, ?_, ?_⟩
  · convert! h.1.comp u hi using 1 <;> simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]
  · convert! (h.2.1.comp u hi).mul_const m using 1 <;>
      (try simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]) <;> ring
  · convert! (h.2.2.comp u hi).mul_const (m ^ 2) using 1 <;>
      (try simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]) <;> ring

/-! ## Links of a sound raw jet and of its shifts -/

theorem sound3At_of_soundAt {q : Jet5} {y : ℝ} (h : q.SoundAt y) : Sound3At q y :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem sound3At_shift_of_soundAt {q : Jet5} {y : ℝ} (h : q.SoundAt y) :
    Sound3At (shift q) y :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem sound3At_shift2_of_soundAt {q : Jet5} {y : ℝ} (h : q.SoundAt y) :
    Sound3At (shift (shift q)) y :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem qJet_d2_eq_deriv2_regular {y : ℝ} (hy : y ∈ e8SlopeRange) :
    qJet.d2 y = deriv (deriv e8RegularQ) y := by
  have hs : ∀ᶠ z in nhds y, deriv e8RegularQ z = qJet.d1 z := by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    have := qPrimeJet_d0_eq_deriv_regular hz
    simpa [qPrimeJet, shift] using this.symm
  have hd : HasDerivAt qJet.d1 (qJet.d2 y) y := (qJet_soundAt hy).2.1
  exact ((hd.congr_of_eventuallyEq hs).deriv).symm

theorem qJet_d1_eq_deriv_regular {y : ℝ} (hy : y ∈ e8SlopeRange) :
    qJet.d1 y = deriv e8RegularQ y := by
  simpa [qPrimeJet, shift] using qPrimeJet_d0_eq_deriv_regular hy

/-- The canonical inverse jet agrees with `e8RegularQ` through the second derivative. -/
theorem qJet_agrees {z : ℝ} (hz : z ∈ e8SlopeRange) :
    qJet.d0 z = e8RegularQ z ∧ qJet.d1 z = deriv e8RegularQ z ∧
      qJet.d2 z = deriv (deriv e8RegularQ) z :=
  ⟨qJet_d0_eq_regular hz, qJet_d1_eq_deriv_regular hz, qJet_d2_eq_deriv2_regular hz⟩

/-! ## The directional jet -/

/-- Jet-algebra graph of `e8SecondSJet`. -/
def deltaSSGraph (a b c d bp cp dp bpp cpp dpp : Jet5) : Jet5 :=
  ((((Jet5.const 4).mul bp).mul (sub cp dp)).add
    (((Jet5.const 4).mul bpp).mul (sub (sub c ((Jet5.const 2).mul a)) d))).add
    ((cpp.mul (a.add b)).add (dpp.mul (sub a b)))

theorem sound3At_deltaSSGraph {a b c d bp cp dp bpp cpp dpp : Jet5} {u : ℝ}
    (ha : Sound3At a u) (hb : Sound3At b u) (hc : Sound3At c u) (hd : Sound3At d u)
    (hbp : Sound3At bp u) (hcp : Sound3At cp u) (hdp : Sound3At dp u)
    (hbpp : Sound3At bpp u) (hcpp : Sound3At cpp u) (hdpp : Sound3At dpp u) :
    Sound3At (deltaSSGraph a b c d bp cp dp bpp cpp dpp) u :=
  ((((sound3At_const 4 u).mul hbp).mul (hcp.sub hdp)).add
    (((sound3At_const 4 u).mul hbpp).mul ((hc.sub ((sound3At_const 2 u).mul ha)).sub hd))).add
    ((hcpp.mul (ha.add hb)).add (hdpp.mul (ha.sub hb)))

/-- The order-three jet of the second `s` derivative along `(s0+x*u, t0+y*u)`, built from `q`. -/
noncomputable def deltaSSJetOf (q : Jet5) (s0 t0 x y : ℝ) : Jet5 :=
  deltaSSGraph
    (affine q t0 y)
    (affine q (2 * s0 + t0) (2 * x + y))
    (affine q (s0 + t0) (x + y))
    (affine q s0 x)
    (affine (shift q) (2 * s0 + t0) (2 * x + y))
    (affine (shift q) (s0 + t0) (x + y))
    (affine (shift q) s0 x)
    (affine (shift (shift q)) (2 * s0 + t0) (2 * x + y))
    (affine (shift (shift q)) (s0 + t0) (x + y))
    (affine (shift (shift q)) s0 x)

theorem deltaSSJetOf_sound3At {q : Jet5} {s0 t0 x y u : ℝ}
    (hA : q.SoundAt (t0 + y * u)) (hB : q.SoundAt ((2 * s0 + t0) + (2 * x + y) * u))
    (hC : q.SoundAt ((s0 + t0) + (x + y) * u)) (hD : q.SoundAt (s0 + x * u)) :
    Sound3At (deltaSSJetOf q s0 t0 x y) u :=
  sound3At_deltaSSGraph
    (sound3At_of_soundAt hA).affine (sound3At_of_soundAt hB).affine
    (sound3At_of_soundAt hC).affine (sound3At_of_soundAt hD).affine
    (sound3At_shift_of_soundAt hB).affine (sound3At_shift_of_soundAt hC).affine
    (sound3At_shift_of_soundAt hD).affine
    (sound3At_shift2_of_soundAt hB).affine (sound3At_shift2_of_soundAt hC).affine
    (sound3At_shift2_of_soundAt hD).affine

/-- Zeroth component: the regular second `s` derivative, for any `q` agreeing with
`e8RegularQ` through the second derivative at admissible positive slopes. -/
theorem deltaSSJetOf_d0_eq_regular {q : Jet5} {s0 t0 x y u : ℝ}
    (hq : ∀ z : ℝ, 0 < z → z ∈ e8SlopeRange →
      q.d0 z = e8RegularQ z ∧ q.d1 z = deriv e8RegularQ z ∧
        q.d2 z = deriv (deriv e8RegularQ) z)
    (h : E8Admissible (s0 + x * u) (t0 + y * u)) :
    (deltaSSJetOf q s0 t0 x y).d0 u = e8RegularDeltaSS (s0 + x * u) (t0 + y * u) := by
  obtain ⟨hs, ht, hsm, htm, hcm, hbm⟩ := h
  have hB : (2 * s0 + t0) + (2 * x + y) * u = 2 * (s0 + x * u) + (t0 + y * u) := by ring
  have hC : (s0 + t0) + (x + y) * u = (s0 + x * u) + (t0 + y * u) := by ring
  obtain ⟨a0, -, -⟩ := hq _ ht htm
  obtain ⟨b0, b1, b2⟩ := hq _ (by linarith) hbm
  obtain ⟨c0, c1, c2⟩ := hq _ (by linarith) hcm
  obtain ⟨d0, d1, d2⟩ := hq _ hs hsm
  rw [e8RegularDeltaSS_eq_jet ⟨hs, ht, hsm, htm, hcm, hbm⟩]
  dsimp only [deltaSSJetOf, deltaSSGraph, sub, Jet5.add, Jet5.neg, Jet5.mul, Jet5.const,
    affine, shift]
  rw [hB, hC, a0, b0, b1, b2, c0, c1, c2, d0, d1, d2]
  simp only [e8SecondSJet]
  ring

/-! ## Ray derivatives as mixed coefficients -/

set_option maxHeartbeats 4000000 in
theorem rayS_d0 (q : Jet5) (s0 t0 x y u : ℝ) :
    (deltaSSJetOf q s0 t0 x y).d0 u = mixedS q (s0 + x * u) (t0 + y * u) 2 0 := by
  simp only [deltaSSJetOf, deltaSSGraph, sub, affine, shift,
    Jet5.add, Jet5.neg, Jet5.mul, Jet5.const, mixedS]
  rw [show 2 * s0 + t0 + (2 * x + y) * u = 2 * (s0 + x * u) + (t0 + y * u) by ring,
    show s0 + t0 + (x + y) * u = (s0 + x * u) + (t0 + y * u) by ring]
  ring

set_option maxHeartbeats 4000000 in
theorem rayS_d1 (q : Jet5) (s0 t0 x y u : ℝ) :
    (deltaSSJetOf q s0 t0 x y).d1 u =
      mixedS q (s0 + x * u) (t0 + y * u) 3 0 * x +
      mixedS q (s0 + x * u) (t0 + y * u) 2 1 * y := by
  simp only [deltaSSJetOf, deltaSSGraph, sub, affine, shift,
    Jet5.add, Jet5.neg, Jet5.mul, Jet5.const, mixedS]
  rw [show 2 * s0 + t0 + (2 * x + y) * u = 2 * (s0 + x * u) + (t0 + y * u) by ring,
    show s0 + t0 + (x + y) * u = (s0 + x * u) + (t0 + y * u) by ring]
  ring

set_option maxHeartbeats 4000000 in
theorem rayS_d2 (q : Jet5) (s0 t0 x y u : ℝ) :
    (deltaSSJetOf q s0 t0 x y).d2 u =
      mixedS q (s0 + x * u) (t0 + y * u) 4 0 * x ^ 2 +
      2 * mixedS q (s0 + x * u) (t0 + y * u) 3 1 * x * y +
      mixedS q (s0 + x * u) (t0 + y * u) 2 2 * y ^ 2 := by
  simp only [deltaSSJetOf, deltaSSGraph, sub, affine, shift,
    Jet5.add, Jet5.neg, Jet5.mul, Jet5.const, mixedS]
  rw [show 2 * s0 + t0 + (2 * x + y) * u = 2 * (s0 + x * u) + (t0 + y * u) by ring,
    show s0 + t0 + (x + y) * u = (s0 + x * u) + (t0 + y * u) by ring]
  ring

set_option maxHeartbeats 4000000 in
theorem rayS_d3 (q : Jet5) (s0 t0 x y u : ℝ) :
    (deltaSSJetOf q s0 t0 x y).d3 u =
      mixedS q (s0 + x * u) (t0 + y * u) 5 0 * x ^ 3 +
      3 * mixedS q (s0 + x * u) (t0 + y * u) 4 1 * x ^ 2 * y +
      3 * mixedS q (s0 + x * u) (t0 + y * u) 3 2 * x * y ^ 2 +
      mixedS q (s0 + x * u) (t0 + y * u) 2 3 * y ^ 3 := by
  simp only [deltaSSJetOf, deltaSSGraph, sub, affine, shift,
    Jet5.add, Jet5.neg, Jet5.mul, Jet5.const, mixedS]
  rw [show 2 * s0 + t0 + (2 * x + y) * u = 2 * (s0 + x * u) + (t0 + y * u) by ring,
    show s0 + t0 + (x + y) * u = (s0 + x * u) + (t0 + y * u) by ring]
  ring

/-! ## Order-three Lagrange remainder on `[0,1]`

Proof pattern copied from Lane C3 (`CKLaneC3.TaylorChain.exists_remainder3`, itself following
`GeneralCK.Certificates.E8CompactAnchorTaylor3.exists_remainder`). -/

theorem rolle_step {g dg : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hd : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g (dg u) u)
    (heq : g 0 = g b) : ∃ c ∈ Ioo (0 : ℝ) b, dg c = 0 := by
  apply exists_hasDerivAt_eq_zero hb
  · intro u hu
    exact (hd u ⟨hu.1, hu.2.trans hb1⟩).continuousAt.continuousWithinAt
  · exact heq
  · intro u hu
    exact hd u ⟨hu.1.le, hu.2.le.trans hb1⟩

theorem exists_remainder1 {f f1 : ℝ → ℝ}
    (h0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f1 u) u) :
    ∃ u ∈ Ioo (0 : ℝ) 1, f 1 = f 0 + f1 u := by
  let R := 1 * (f 1 - (f 0))
  let g0 : ℝ → ℝ := fun u => f u - (f 0 + R * u)
  have hd0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g0 (f1 u - R) u := by
    intro u hu
    have hd := (h0 u hu).sub ((hasDerivAt_const u (f 0)).add ((hasDerivAt_id u).const_mul R))
    convert! hd using 1 <;>
      (try simp only [g0, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]) <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
      | (simp; ring)
      | simp
  obtain ⟨u1, hu1, he1⟩ := rolle_step (by norm_num : (0 : ℝ) < 1) le_rfl hd0
    (by simp only [g0, R]; ring)
  refine ⟨u1, ⟨hu1.1, hu1.2⟩, ?_⟩
  have hR : f1 u1 = R := by linarith
  rw [hR]
  simp only [R]
  ring

theorem exists_remainder2 {f f1 f2 : ℝ → ℝ}
    (h0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f1 u) u)
    (h1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f1 (f2 u) u) :
    ∃ u ∈ Ioo (0 : ℝ) 1, f 1 = f 0 + f1 0 + f2 u / 2 := by
  let R := 2 * (f 1 - (f 0 + f1 0))
  let g0 : ℝ → ℝ := fun u => f u - (f 0 + f1 0 * u + R * u ^ 2 / 2)
  let g1 : ℝ → ℝ := fun u => f1 u - (f1 0 + R * u)
  have hd0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g0 (g1 u) u := by
    intro u hu
    have hd := (h0 u hu).sub (((hasDerivAt_const u (f 0)).add ((hasDerivAt_id u).const_mul (f1 0))).add (((hasDerivAt_id u).pow 2).const_mul (R / 2)))
    convert! hd using 1 <;>
      (try simp only [g0, g1, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]) <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
      | (simp; ring)
      | simp
  have hd1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g1 (f2 u - R) u := by
    intro u hu
    have hd := (h1 u hu).sub ((hasDerivAt_const u (f1 0)).add ((hasDerivAt_id u).const_mul R))
    convert! hd using 1 <;>
      (try simp only [g1, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]) <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
      | (simp; ring)
      | simp
  obtain ⟨u1, hu1, he1⟩ := rolle_step (by norm_num : (0 : ℝ) < 1) le_rfl hd0
    (by simp only [g0, R]; ring)
  obtain ⟨u2, hu2, he2⟩ := rolle_step hu1.1 hu1.2.le hd1
    (by rw [he1]; simp [g1])
  refine ⟨u2, ⟨hu2.1, hu2.2.trans (hu1.2)⟩, ?_⟩
  have hR : f2 u2 = R := by linarith
  rw [hR]
  simp only [R]
  ring

theorem exists_remainder3 {f f1 f2 f3 : ℝ → ℝ}
    (h0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f1 u) u)
    (h1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f1 (f2 u) u)
    (h2 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f2 (f3 u) u) :
    ∃ u ∈ Ioo (0 : ℝ) 1, f 1 = f 0 + f1 0 + f2 0 / 2 + f3 u / 6 := by
  let R := 6 * (f 1 - (f 0 + f1 0 + f2 0 / 2))
  let g0 : ℝ → ℝ := fun u => f u - (f 0 + f1 0 * u + f2 0 * u ^ 2 / 2 + R * u ^ 3 / 6)
  let g1 : ℝ → ℝ := fun u => f1 u - (f1 0 + f2 0 * u + R * u ^ 2 / 2)
  let g2 : ℝ → ℝ := fun u => f2 u - (f2 0 + R * u)
  have hd0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g0 (g1 u) u := by
    intro u hu
    have hd := (h0 u hu).sub ((((hasDerivAt_const u (f 0)).add ((hasDerivAt_id u).const_mul (f1 0))).add (((hasDerivAt_id u).pow 2).const_mul (f2 0 / 2))).add (((hasDerivAt_id u).pow 3).const_mul (R / 6)))
    convert! hd using 1 <;>
      (try simp only [g0, g1, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]) <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
      | (simp; ring)
      | simp
  have hd1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g1 (g2 u) u := by
    intro u hu
    have hd := (h1 u hu).sub (((hasDerivAt_const u (f1 0)).add ((hasDerivAt_id u).const_mul (f2 0))).add (((hasDerivAt_id u).pow 2).const_mul (R / 2)))
    convert! hd using 1 <;>
      (try simp only [g1, g2, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]) <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
      | (simp; ring)
      | simp
  have hd2 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g2 (f3 u - R) u := by
    intro u hu
    have hd := (h2 u hu).sub ((hasDerivAt_const u (f2 0)).add ((hasDerivAt_id u).const_mul R))
    convert! hd using 1 <;>
      (try simp only [g2, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]) <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
      | (simp; ring)
      | simp
  obtain ⟨u1, hu1, he1⟩ := rolle_step (by norm_num : (0 : ℝ) < 1) le_rfl hd0
    (by simp only [g0, R]; ring)
  obtain ⟨u2, hu2, he2⟩ := rolle_step hu1.1 hu1.2.le hd1
    (by rw [he1]; simp [g1])
  obtain ⟨u3, hu3, he3⟩ := rolle_step hu2.1 (hu2.2.trans (hu1.2)).le hd2
    (by rw [he2]; simp [g2])
  refine ⟨u3, ⟨hu3.1, hu3.2.trans (hu2.2.trans (hu1.2))⟩, ?_⟩
  have hR : f3 u3 = R := by linarith
  rw [hR]
  simp only [R]
  ring

/-- The corner Taylor identity of the ray jet, for any raw jet sound along the ray. -/
theorem deltaSSOf_corner_taylor {q : Jet5} {s0 t0 x y : ℝ}
    (hsound : ∀ u ∈ Icc (0 : ℝ) 1,
      q.SoundAt (t0 + y * u) ∧ q.SoundAt ((2 * s0 + t0) + (2 * x + y) * u) ∧
        q.SoundAt ((s0 + t0) + (x + y) * u) ∧ q.SoundAt (s0 + x * u)) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      (deltaSSJetOf q s0 t0 x y).d0 1 =
        mixedS q s0 t0 2 0 +
        (mixedS q s0 t0 3 0 * x + mixedS q s0 t0 2 1 * y) +
        (mixedS q s0 t0 4 0 * x ^ 2 + 2 * mixedS q s0 t0 3 1 * x * y +
          mixedS q s0 t0 2 2 * y ^ 2) / 2 +
        (mixedS q (s0 + x * u) (t0 + y * u) 5 0 * x ^ 3 +
          3 * mixedS q (s0 + x * u) (t0 + y * u) 4 1 * x ^ 2 * y +
          3 * mixedS q (s0 + x * u) (t0 + y * u) 3 2 * x * y ^ 2 +
          mixedS q (s0 + x * u) (t0 + y * u) 2 3 * y ^ 3) / 6 := by
  have hj : ∀ u ∈ Icc (0 : ℝ) 1, Sound3At (deltaSSJetOf q s0 t0 x y) u := by
    intro u hu
    obtain ⟨hA, hB, hC, hD⟩ := hsound u hu
    exact deltaSSJetOf_sound3At hA hB hC hD
  obtain ⟨u, hu, heq⟩ := exists_remainder3 (fun u hu => (hj u hu).1)
    (fun u hu => (hj u hu).2.1) (fun u hu => (hj u hu).2.2)
  refine ⟨u, hu, ?_⟩
  rw [heq, rayS_d0, rayS_d1, rayS_d2, rayS_d3]
  simp only [mul_zero, add_zero]

/-- Order-one (mean value) corner identity. -/
theorem deltaSSOf_corner_taylor1 {q : Jet5} {s0 t0 x y : ℝ}
    (hsound : ∀ u ∈ Icc (0 : ℝ) 1,
      q.SoundAt (t0 + y * u) ∧ q.SoundAt ((2 * s0 + t0) + (2 * x + y) * u) ∧
        q.SoundAt ((s0 + t0) + (x + y) * u) ∧ q.SoundAt (s0 + x * u)) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      (deltaSSJetOf q s0 t0 x y).d0 1 =
        mixedS q s0 t0 2 0 +
        (mixedS q (s0 + x * u) (t0 + y * u) 3 0 * x +
          mixedS q (s0 + x * u) (t0 + y * u) 2 1 * y) := by
  have hj : ∀ u ∈ Icc (0 : ℝ) 1, Sound3At (deltaSSJetOf q s0 t0 x y) u := by
    intro u hu
    obtain ⟨hA, hB, hC, hD⟩ := hsound u hu
    exact deltaSSJetOf_sound3At hA hB hC hD
  obtain ⟨u, hu, heq⟩ := exists_remainder1 (fun u hu => (hj u hu).1)
  refine ⟨u, hu, ?_⟩
  rw [heq, rayS_d0, rayS_d1]
  simp only [mul_zero, add_zero]

/-- Order-two corner identity. -/
theorem deltaSSOf_corner_taylor2 {q : Jet5} {s0 t0 x y : ℝ}
    (hsound : ∀ u ∈ Icc (0 : ℝ) 1,
      q.SoundAt (t0 + y * u) ∧ q.SoundAt ((2 * s0 + t0) + (2 * x + y) * u) ∧
        q.SoundAt ((s0 + t0) + (x + y) * u) ∧ q.SoundAt (s0 + x * u)) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      (deltaSSJetOf q s0 t0 x y).d0 1 =
        mixedS q s0 t0 2 0 +
        (mixedS q s0 t0 3 0 * x + mixedS q s0 t0 2 1 * y) +
        (mixedS q (s0 + x * u) (t0 + y * u) 4 0 * x ^ 2 +
          2 * mixedS q (s0 + x * u) (t0 + y * u) 3 1 * x * y +
          mixedS q (s0 + x * u) (t0 + y * u) 2 2 * y ^ 2) / 2 := by
  have hj : ∀ u ∈ Icc (0 : ℝ) 1, Sound3At (deltaSSJetOf q s0 t0 x y) u := by
    intro u hu
    obtain ⟨hA, hB, hC, hD⟩ := hsound u hu
    exact deltaSSJetOf_sound3At hA hB hC hD
  obtain ⟨u, hu, heq⟩ := exists_remainder2 (fun u hu => (hj u hu).1)
    (fun u hu => (hj u hu).2.1)
  refine ⟨u, hu, ?_⟩
  rw [heq, rayS_d0, rayS_d1, rayS_d2]
  simp only [mul_zero, add_zero]

end CKLaneC.SAxis

end


