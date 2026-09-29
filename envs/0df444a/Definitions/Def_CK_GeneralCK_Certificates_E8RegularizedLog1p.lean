-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8RegularizedLog1p
-- name    : CK_GeneralCK_Certificates_E8RegularizedLog1p
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:14:31.012758+00:00
-- url     : https://prove2.me/theorems/cd6c9d79-591f-40b1-8999-ff84e9802561
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8RegularizedLog1p` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8RegularizedLog1p` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8RegularizedLog1p` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8RegularizedLog1p (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8RegularizedLog1p.lean)

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- ===== source module GeneralCK.Certificates.E8RegularizedLog1p =====
section

/-!
# A regularized `log (1 + u) / u` primitive for the E8 tail

The historical E8 tail program changes variables to

`v = 1 / a`, `u = exp (-2 * a)`

and evaluates `log (1 + u) / u`.  Direct interval division by a box which
touches `u = 0` is unusable.  This file gives the quotient its removable
value at zero and records a sound first-order enclosure which remains valid
on such a box.  Only the value and first derivative are needed by the raw
(`non-centred`) formula for `E`, `E'`, and `L`; higher derivatives in the old
`PRJ3` implementation were used to sharpen a centred Taylor enclosure, not
by the mathematical identity itself.
-/

namespace GeneralCK.Certificates.E8RegularizedLog1p

/-- The continuous value of `log (1 + u) / u` at `u = 0`. -/
noncomputable def regLog1p (u : ℝ) : ℝ :=
  if u = 0 then 1 else Real.log (1 + u) / u

/-- The removable first derivative.  The value `-1/2` at zero is the first
Taylor coefficient of `log (1 + u) / u`.  The tail checker only consumes its
interval enclosure, so no division by an interval containing zero occurs. -/
noncomputable def regLog1pPrime (u : ℝ) : ℝ :=
  if u = 0 then -(1 / 2) else
    (u / (1 + u) - Real.log (1 + u)) / u ^ 2

@[simp] theorem regLog1p_zero : regLog1p 0 = 1 := by
  simp [regLog1p]

@[simp] theorem regLog1pPrime_zero : regLog1pPrime 0 = -(1 / 2) := by
  simp [regLog1pPrime]

theorem regLog1p_eq {u : ℝ} (hu : u ≠ 0) :
    regLog1p u = Real.log (1 + u) / u := by
  simp [regLog1p, hu]

theorem regLog1pPrime_eq {u : ℝ} (hu : u ≠ 0) :
    regLog1pPrime u =
      (u / (1 + u) - Real.log (1 + u)) / u ^ 2 := by
  simp [regLog1pPrime, hu]

/-- Away from the removable point, `regLog1pPrime` is the actual derivative
of the regularized quotient. -/
theorem hasDerivAt_regLog1p {u : ℝ} (hu : u ≠ 0) (h1u : 1 + u ≠ 0) :
    HasDerivAt regLog1p (regLog1pPrime u) u := by
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + u)) u := by
    have h := ((hasDerivAt_id u).const_add 1).log (by simpa [add_comm] using h1u)
    convert! h using 1 <;> ring
  have hquot := hlog.div (hasDerivAt_id u) hu
  have heq : regLog1p =ᶠ[nhds u]
      ((fun x : ℝ => Real.log (1 + x)) / id) := by
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hu] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp [regLog1p, hx0, Pi.div_apply]
  have hreg := hquot.congr_of_eventuallyEq heq
  have hcoef :
      (1 / (1 + u) * u - Real.log (1 + u)) / u ^ 2 =
        regLog1pPrime u := by
    rw [regLog1pPrime_eq hu]
    field_simp [hu, h1u]
  simp only [id_eq, mul_one] at hreg
  rw [hcoef] at hreg
  exact hreg

/-- A denominator-free lower value bound, valid uniformly down to zero. -/
theorem one_div_one_add_le_regLog1p {u : ℝ} (hu : 0 < u) :
    1 / (1 + u) ≤ regLog1p u := by
  rw [regLog1p_eq hu.ne']
  have hlog := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + u by linarith)
  have hid : 1 - (1 + u)⁻¹ = u / (1 + u) := by
    field_simp [show 1 + u ≠ 0 by linarith]
    ring
  rw [hid] at hlog
  apply (le_div_iff₀ hu).2
  calc
    1 / (1 + u) * u = u / (1 + u) := by ring
    _ ≤ Real.log (1 + u) := hlog

/-- The elementary upper value bound from `log (1 + u) ≤ u`. -/
theorem regLog1p_le_one {u : ℝ} (hu : 0 < u) : regLog1p u ≤ 1 := by
  rw [regLog1p_eq hu.ne']
  apply (div_le_iff₀ hu).2
  simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + u by linarith)

/-- Coarse but extremely effective derivative enclosure on the E8 tail.
For `u ≤ exp (-40)` its width is immaterial compared with the retained
`L / v² > 0.8499` margin. -/
theorem regLog1pPrime_mem {u : ℝ} (hu : 0 < u) :
    -(1 : ℝ) ≤ regLog1pPrime u ∧ regLog1pPrime u ≤ 0 := by
  rw [regLog1pPrime_eq hu.ne']
  have hpos : 0 < 1 + u := by linarith
  have hlower := Real.one_sub_inv_le_log_of_pos hpos
  have hupper := Real.log_le_sub_one_of_pos hpos
  have hid : 1 - (1 + u)⁻¹ = u / (1 + u) := by
    field_simp [hpos.ne']
    ring
  rw [hid] at hlower
  have hsq : 0 < u ^ 2 := sq_pos_of_pos hu
  constructor
  · apply (le_div_iff₀ hsq).2
    have hfrac : -u ^ 2 ≤ u / (1 + u) - u := by
      have heq : u / (1 + u) - u = -u ^ 2 / (1 + u) := by
        field_simp [hpos.ne']
        ring
      rw [heq]
      apply (le_div_iff₀ hpos).2
      nlinarith [mul_nonneg (sq_nonneg u) hu.le]
    nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlower) hsq.le

/-- A compact sound box interface for generated tail arithmetic.  The
checker may replace the analytic primitive by these four rational endpoint
inequalities and then use only ring operations and reciprocal checks. -/
structure FirstOrderBox (lo hi : ℝ) : Prop where
  value_lower : ∀ u, 0 < u → u ≤ hi → lo ≤ 1 / (1 + u) → lo ≤ regLog1p u
  value_upper : ∀ u, 0 < u → u ≤ hi → regLog1p u ≤ 1
  prime_lower : ∀ u, 0 < u → u ≤ hi → -(1 : ℝ) ≤ regLog1pPrime u
  prime_upper : ∀ u, 0 < u → u ≤ hi → regLog1pPrime u ≤ 0

/-- The canonical coarse box.  A generator can tighten it, but does not
need to in order to cross the removable singularity soundly. -/
theorem coarseFirstOrderBox {hi : ℝ} (hhi : 0 ≤ hi) :
    FirstOrderBox (1 / (1 + hi)) hi := by
  constructor
  · intro u hu hui _
    exact (one_div_le_one_div_of_le (by linarith) (by linarith)).trans
      (one_div_one_add_le_regLog1p hu)
  · intro u hu _
    exact regLog1p_le_one hu
  · intro u hu _
    exact (regLog1pPrime_mem hu).1
  · intro u hu _
    exact (regLog1pPrime_mem hu).2

#print axioms hasDerivAt_regLog1p
#print axioms one_div_one_add_le_regLog1p
#print axioms regLog1p_le_one
#print axioms regLog1pPrime_mem
#print axioms coarseFirstOrderBox

end GeneralCK.Certificates.E8RegularizedLog1p

end


