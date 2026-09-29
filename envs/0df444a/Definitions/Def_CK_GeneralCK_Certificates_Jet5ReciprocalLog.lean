-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Jet5ReciprocalLog
-- name    : CK_GeneralCK_Certificates_Jet5ReciprocalLog
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:52:36.730759+00:00
-- url     : https://prove2.me/theorems/4cd5a36c-24e3-4f6c-8c47-dbe735d57427
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Jet5ReciprocalLog` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Jet5ReciprocalLog` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Jet5ReciprocalLog` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Jet5ReciprocalLog (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Jet5ReciprocalLog.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Jet5
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp

-- ===== source module GeneralCK.Certificates.Jet5ReciprocalLog =====
section

/-! Sound reciprocal and logarithm propagation for raw order-five jets. -/

namespace GeneralCK.Certificates
namespace Jet5

/-- Raw derivatives of the reciprocal through order five. -/
noncomputable def inv (a : Jet5) : Jet5 :=
  ⟨a.d0⁻¹,
   -a.d1 / a.d0^2,
   (fun y => 2*(a.d1^2) y)/a.d0^3-a.d2/a.d0^2,
   (fun y => -6*(a.d1^3) y)/a.d0^4+
     ((fun y => 6*(a.d1*a.d2) y)/a.d0^3-a.d3/a.d0^2),
   (fun y => 24*(a.d1^4) y)/a.d0^5-(fun y => 36*(a.d1^2*a.d2) y)/a.d0^4+
     (fun y => 6*(a.d2^2) y)/a.d0^3+(fun y => 8*(a.d1*a.d3) y)/a.d0^3-
     a.d4/a.d0^2,
   fun t => -120*a.d1 t^5/a.d0 t^6+240*a.d1 t^3*a.d2 t/a.d0 t^5-
     90*a.d1 t*a.d2 t^2/a.d0 t^4-60*a.d1 t^2*a.d3 t/a.d0 t^4+
     20*a.d2 t*a.d3 t/a.d0 t^3+10*a.d1 t*a.d4 t/a.d0 t^3-
     a.d5 t/a.d0 t^2⟩

theorem SoundAt.inv {a : Jet5} {t : ℝ} (ha : a.SoundAt t) (hn : a.d0 t ≠ 0) :
    a.inv.SoundAt t := by
  have h2 : a.d0 t ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have h3 : a.d0 t ^ 3 ≠ 0 := pow_ne_zero 3 hn
  have h4 : a.d0 t ^ 4 ≠ 0 := pow_ne_zero 4 hn
  have h5 : a.d0 t ^ 5 ≠ 0 := pow_ne_zero 5 hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! ha.1.inv hn using 1 <;> simp [Jet5.inv]
  · have h := ha.2.1.neg.div (ha.1.pow 2) h2
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h := (((ha.2.1.pow 2).const_mul 2).div (ha.1.pow 3) h3).sub
      (ha.2.2.1.div (ha.1.pow 2) h2)
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h := (((ha.2.1.pow 3).const_mul (-6)).div (ha.1.pow 4) h4).add
      ((((ha.2.1.mul ha.2.2.1).const_mul 6).div (ha.1.pow 3) h3).sub
        (ha.2.2.2.1.div (ha.1.pow 2) h2))
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h1 := ((ha.2.1.pow 4).const_mul 24).div (ha.1.pow 5) h5
    have h2term := (((ha.2.1.pow 2).mul ha.2.2.1).const_mul 36).div (ha.1.pow 4) h4
    have h3' := ((ha.2.2.1.pow 2).const_mul 6).div (ha.1.pow 3) h3
    have h4' := ((ha.2.1.mul ha.2.2.2.1).const_mul 8).div (ha.1.pow 3) h3
    have h5' := ha.2.2.2.2.div (ha.1.pow 2) h2
    have h := (((h1.sub h2term).add h3').add h4').sub h5'
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring

/-- Define logarithmic derivatives from `a' * a⁻¹`; this exposes the domain
hypothesis only in the soundness theorem. -/
noncomputable def log (a : Jet5) : Jet5 :=
  let r := a.inv
  ⟨fun t => Real.log (a.d0 t),
   fun t => a.d1 t*r.d0 t,
   fun t => a.d2 t*r.d0 t+a.d1 t*r.d1 t,
   fun t => a.d3 t*r.d0 t+2*a.d2 t*r.d1 t+a.d1 t*r.d2 t,
   fun t => a.d4 t*r.d0 t+3*a.d3 t*r.d1 t+3*a.d2 t*r.d2 t+a.d1 t*r.d3 t,
   fun t => a.d5 t*r.d0 t+4*a.d4 t*r.d1 t+6*a.d3 t*r.d2 t+
     4*a.d2 t*r.d3 t+a.d1 t*r.d4 t⟩

theorem SoundAt.log {a : Jet5} {t : ℝ} (ha : a.SoundAt t) (hn : a.d0 t ≠ 0) :
    a.log.SoundAt t := by
  have hr := ha.inv hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! ha.1.log hn using 1 <;> simp [Jet5.log, Jet5.inv, div_eq_mul_inv]
  · convert! ha.2.1.mul hr.1 using 1 <;>
      simp [Jet5.log] <;> first | (funext u; simp <;> ring) | ring
  · have h := (ha.2.2.1.mul hr.1).add (ha.2.1.mul hr.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((ha.2.2.2.1.mul hr.1).add
      ((ha.2.2.1.mul hr.2.1).const_mul 2)).add
      (ha.2.1.mul hr.2.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((ha.2.2.2.2.mul hr.1).add
      ((ha.2.2.2.1.mul hr.2.1).const_mul 3)).add
      ((ha.2.2.1.mul hr.2.2.1).const_mul 3)).add
      (ha.2.1.mul hr.2.2.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring

end Jet5
end GeneralCK.Certificates

end


