-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Jet5
-- name    : CK_GeneralCK_Certificates_Jet5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:50:33.574002+00:00
-- url     : https://prove2.me/theorems/a972acb4-c625-4bd4-9b9c-53b3ba7c82a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Jet5` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Jet5` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Jet5` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Jet5 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Jet5.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Jet2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_derivative_semantics
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.Certificates.Jet5 =====
section

/-! Order-five univariate jets with raw derivative components. -/

namespace GeneralCK.Certificates









namespace Jet5








def const (c : ℝ) : Jet5 :=
  ⟨fun _ => c, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def variableJet : Jet5 :=
  ⟨id, fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩





















/-- Raw Faà di Bruno propagation for the exponential through order five. -/
noncomputable def exp (a : Jet5) : Jet5 :=
  ⟨fun t => Real.exp (a.d0 t),
   fun t => Real.exp (a.d0 t)*a.d1 t,
   fun t => Real.exp (a.d0 t)*(a.d1 t^2+a.d2 t),
   fun t => Real.exp (a.d0 t)*(a.d1 t^3+3*a.d1 t*a.d2 t+a.d3 t),
   fun t => Real.exp (a.d0 t)*(a.d1 t^4+6*a.d1 t^2*a.d2 t+3*a.d2 t^2+
     4*a.d1 t*a.d3 t+a.d4 t),
   fun t => Real.exp (a.d0 t)*(a.d1 t^5+10*a.d1 t^3*a.d2 t+
     15*a.d1 t*a.d2 t^2+10*a.d1 t^2*a.d3 t+10*a.d2 t*a.d3 t+
     5*a.d1 t*a.d4 t+a.d5 t)⟩

theorem soundAt_const (c t : ℝ) : (const c).SoundAt t := by
  exact ⟨hasDerivAt_const t c, hasDerivAt_const t 0, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0⟩

theorem soundAt_variable (t : ℝ) : variableJet.SoundAt t := by
  exact ⟨hasDerivAt_id t, hasDerivAt_const t 1, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0⟩

theorem SoundAt.add {a b : Jet5} {t : ℝ} (ha : a.SoundAt t) (hb : b.SoundAt t) :
    (a.add b).SoundAt t := by
  exact ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.1.add hb.2.2.1,
    ha.2.2.2.1.add hb.2.2.2.1, ha.2.2.2.2.add hb.2.2.2.2⟩

theorem SoundAt.neg {a : Jet5} {t : ℝ} (ha : a.SoundAt t) : a.neg.SoundAt t := by
  exact ⟨ha.1.neg, ha.2.1.neg, ha.2.2.1.neg, ha.2.2.2.1.neg, ha.2.2.2.2.neg⟩

theorem SoundAt.mul {a b : Jet5} {t : ℝ} (ha : a.SoundAt t) (hb : b.SoundAt t) :
    (a.mul b).SoundAt t := by
  refine ⟨ha.1.mul hb.1, ?_, ?_, ?_, ?_⟩
  · convert! (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1) using 1 <;>
      simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;> first | (funext u; simp <;> ring) | ring
  · have h := ((ha.2.2.1.mul hb.1).add
      ((ha.2.1.mul hb.2.1).const_mul 2)).add (ha.1.mul hb.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((ha.2.2.2.1.mul hb.1).add
      ((ha.2.2.1.mul hb.2.1).const_mul 3)).add
      ((ha.2.1.mul hb.2.2.1).const_mul 3)).add (ha.1.mul hb.2.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((((ha.2.2.2.2.mul hb.1).add
      ((ha.2.2.2.1.mul hb.2.1).const_mul 4)).add
      ((ha.2.2.1.mul hb.2.2.1).const_mul 6)).add
      ((ha.2.1.mul hb.2.2.2.1).const_mul 4)).add (ha.1.mul hb.2.2.2.2)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring

/-- The order-five jet of `exp (c+m*t)`.  This is the first transcendental
shape needed by the E8 parameterization (`c=0`, `m=-2`). -/
noncomputable def expAffine (c m : ℝ) : Jet5 :=
  ⟨fun t => Real.exp (c+m*t), fun t => Real.exp (c+m*t)*m,
   fun t => Real.exp (c+m*t)*m^2, fun t => Real.exp (c+m*t)*m^3,
   fun t => Real.exp (c+m*t)*m^4, fun t => Real.exp (c+m*t)*m^5⟩

theorem soundAt_expAffine (c m t : ℝ) : (expAffine c m).SoundAt t := by
  have hi : HasDerivAt (fun u : ℝ => c+m*u) m t := by
    convert! (hasDerivAt_const t c).add ((hasDerivAt_id t).mul_const m) using 1
    · funext u
      simp [id_eq, mul_comm]
    · ring
  have he := (Real.hasDerivAt_exp (c+m*t)).comp t hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! he using 1 <;> simp [expAffine]
  · convert! he.mul_const m using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^2) using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^3) using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^4) using 1 <;> simp [expAffine] <;> ring

theorem soundOn_const (c : ℝ) (s : Set ℝ) : (const c).SoundOn s := fun t _ => soundAt_const c t
theorem soundOn_variable (s : Set ℝ) : variableJet.SoundOn s := fun t _ => soundAt_variable t

end Jet5
end GeneralCK.Certificates

end


