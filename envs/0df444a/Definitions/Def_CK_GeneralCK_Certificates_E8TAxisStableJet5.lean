-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableJet5
-- name    : CK_GeneralCK_Certificates_E8TAxisStableJet5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:59:23.391088+00:00
-- url     : https://prove2.me/theorems/4073af87-3844-4dc1-848c-c3941007f5d3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisStableJet5` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisStableJet5` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisStableJet5` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisStableJet5 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisStableJet5.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableScalar
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisReparamJet5
import Definitions.Def_CK_GeneralCK_Certificates_Jet5ReciprocalLog

-- ===== source module GeneralCK.Certificates.E8TAxisStableJet5 =====
section

/-!
# Exact raw order-five jets for the stable E8 parametrization

The expression graph follows the retained `xy_jets5` program, including its
reciprocal and logarithm nodes.  Soundness and the scalar inverse identity
identify the `qdata5` output with every component of the canonical `e8Q` jet.
-/

namespace GeneralCK.Certificates.E8TAxisStableJet5

open Set E8TAxisReparamJet5 E8InverseJet5Bridge



noncomputable def zJet : Jet5 := Jet5.expAffine 0 (-2)
noncomputable def onePlusZJet : Jet5 := (Jet5.const 1).add zJet
noncomputable def rJet : Jet5 :=
  ((Jet5.const 1).add zJet.neg).mul onePlusZJet.inv
noncomputable def qJet : Jet5 :=
  ((Jet5.const 4).mul zJet).mul (onePlusZJet.mul onePlusZJet).inv
noncomputable def l1Jet : Jet5 := onePlusZJet.log
noncomputable def ellJet : Jet5 := Jet5.variableJet.add l1Jet
noncomputable def hJet : Jet5 :=
  l1Jet.add ((((Jet5.const 2).mul Jet5.variableJet).mul zJet).mul onePlusZJet.inv)
noncomputable def log2Jet : Jet5 := Jet5.const (Real.log 2)
noncomputable def xJet : Jet5 :=
  (log2Jet.mul rJet).mul ((Jet5.const 2).mul hJet).inv
noncomputable def yJet : Jet5 :=
  ((Jet5.const 2).mul log2Jet.inv).mul
    (Jet5.variableJet.add ((rJet.mul hJet).mul (qJet.mul ellJet).inv))

@[simp] theorem zJet_d0 (a : ℝ) : zJet.d0 a = E8TAxisStableScalar.z a := by
  simp [zJet, Jet5.expAffine, E8TAxisStableScalar.z]

@[simp] theorem onePlusZJet_d0 (a : ℝ) : onePlusZJet.d0 a = 1 + E8TAxisStableScalar.z a := by
  simp [onePlusZJet, Jet5.add, Jet5.const]

@[simp] theorem rJet_d0 (a : ℝ) : rJet.d0 a = E8TAxisStableScalar.r a := by
  simp [rJet, Jet5.mul, Jet5.add, Jet5.neg, Jet5.const, Jet5.inv,
    E8TAxisStableScalar.r, sub_eq_add_neg, div_eq_mul_inv]

@[simp] theorem qJet_d0 (a : ℝ) : qJet.d0 a = E8TAxisStableScalar.q a := by
  simp [qJet, Jet5.mul, Jet5.const, Jet5.inv, E8TAxisStableScalar.q, pow_two, div_eq_mul_inv]

@[simp] theorem l1Jet_d0 (a : ℝ) : l1Jet.d0 a = E8TAxisStableScalar.l1 a := by
  simp [l1Jet, Jet5.log, E8TAxisStableScalar.l1]

@[simp] theorem ellJet_d0 (a : ℝ) : ellJet.d0 a = E8TAxisStableScalar.ell a := by
  simp [ellJet, Jet5.add, Jet5.variableJet, E8TAxisStableScalar.ell]

@[simp] theorem hJet_d0 (a : ℝ) : hJet.d0 a = E8TAxisStableScalar.h a := by
  simp [hJet, Jet5.add, Jet5.mul, Jet5.const, Jet5.variableJet, Jet5.inv,
    E8TAxisStableScalar.h, div_eq_mul_inv]

@[simp] theorem log2Jet_d0 (a : ℝ) : log2Jet.d0 a = Real.log 2 := rfl

@[simp] theorem xJet_d0 (a : ℝ) : xJet.d0 a = E8TAxisStableScalar.X a := by
  simp [xJet, Jet5.mul, Jet5.const, Jet5.inv, E8TAxisStableScalar.X, div_eq_mul_inv]

@[simp] theorem yJet_d0 (a : ℝ) : yJet.d0 a = E8TAxisStableScalar.Y a := by
  simp [yJet, Jet5.mul, Jet5.add, Jet5.const, Jet5.inv, Jet5.variableJet,
    E8TAxisStableScalar.Y, div_eq_mul_inv]

theorem zJet_soundAt (a : ℝ) : zJet.SoundAt a := Jet5.soundAt_expAffine 0 (-2) a

theorem onePlusZJet_soundAt (a : ℝ) : onePlusZJet.SoundAt a :=
  (Jet5.soundAt_const 1 a).add (zJet_soundAt a)

theorem rJet_soundAt (a : ℝ) : rJet.SoundAt a := by
  unfold rJet
  exact ((Jet5.soundAt_const 1 a).add (zJet_soundAt a).neg).mul
    ((onePlusZJet_soundAt a).inv (by
      rw [onePlusZJet_d0]
      exact (E8TAxisStableScalar.one_add_z_pos a).ne'))

theorem qJet_soundAt (a : ℝ) : qJet.SoundAt a := by
  unfold qJet
  exact ((Jet5.soundAt_const 4 a).mul (zJet_soundAt a)).mul
    (((onePlusZJet_soundAt a).mul (onePlusZJet_soundAt a)).inv (by
      change onePlusZJet.d0 a * onePlusZJet.d0 a ≠ 0
      rw [onePlusZJet_d0]
      exact mul_ne_zero (E8TAxisStableScalar.one_add_z_pos a).ne' (E8TAxisStableScalar.one_add_z_pos a).ne'))

theorem l1Jet_soundAt (a : ℝ) : l1Jet.SoundAt a := by
  exact (onePlusZJet_soundAt a).log (by
    rw [onePlusZJet_d0]
    exact (E8TAxisStableScalar.one_add_z_pos a).ne')

theorem ellJet_soundAt (a : ℝ) : ellJet.SoundAt a :=
  (Jet5.soundAt_variable a).add (l1Jet_soundAt a)

theorem hJet_soundAt (a : ℝ) : hJet.SoundAt a := by
  unfold hJet
  exact (l1Jet_soundAt a).add
    ((((Jet5.soundAt_const 2 a).mul (Jet5.soundAt_variable a)).mul
      (zJet_soundAt a)).mul ((onePlusZJet_soundAt a).inv (by
        rw [onePlusZJet_d0]
        exact (E8TAxisStableScalar.one_add_z_pos a).ne')))

theorem log2Jet_soundAt (a : ℝ) : log2Jet.SoundAt a :=
  Jet5.soundAt_const (Real.log 2) a

theorem xJet_soundAt {a : ℝ} (ha : 0 < a) : xJet.SoundAt a := by
  unfold xJet
  exact ((log2Jet_soundAt a).mul (rJet_soundAt a)).mul
    (((Jet5.soundAt_const 2 a).mul (hJet_soundAt a)).inv (by
      change (2 : ℝ) * hJet.d0 a ≠ 0
      rw [hJet_d0]
      exact mul_ne_zero (by norm_num) (E8TAxisStableScalar.h_pos ha).ne'))

theorem yJet_soundAt {a : ℝ} (ha : 0 < a) : yJet.SoundAt a := by
  unfold yJet
  exact ((Jet5.soundAt_const 2 a).mul ((log2Jet_soundAt a).inv (by
      rw [log2Jet_d0]
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'))).mul
    ((Jet5.soundAt_variable a).add
      (((rJet_soundAt a).mul (hJet_soundAt a)).mul
        (((qJet_soundAt a).mul (ellJet_soundAt a)).inv (by
          change qJet.d0 a * ellJet.d0 a ≠ 0
          rw [qJet_d0, ellJet_d0]
          exact mul_ne_zero (E8TAxisStableScalar.q_pos a).ne' (E8TAxisStableScalar.ell_pos ha).ne'))))

theorem xJet_soundOn : xJet.SoundOn (Ioi 0) := fun _ ha => xJet_soundAt ha

theorem yJet_soundOn : yJet.SoundOn (Ioi 0) := fun _ ha => yJet_soundAt ha

theorem Y_mem_e8SlopeRange {a : ℝ} (ha : 0 < a) : E8TAxisStableScalar.Y a ∈ e8SlopeRange :=
  ⟨E8TAxisStableScalar.X a, E8TAxisStableScalar.X_pos ha, E8TAxisStableScalar.e8Theta_X ha⟩

/-- The historical change-of-parameter recurrence applied to the exact graph. -/
noncomputable def inverseJet : Jet5 := qdata5 xJet yJet

/-- Every inverse derivative is identified once the first derivative of the
parameter map is nonzero.  This final premise can be checked by an interval. -/
theorem inverseJet_eq_canonical {a : ℝ} (ha : 0 < a) (hp : yJet.d1 a ≠ 0) :
    inverseJet.EqAt (atParam (e8QJet5 e8ThetaCanonicalJet5) yJet) a := by
  apply qdata5_eq_canonical isOpen_Ioi xJet_soundOn yJet_soundOn
  · intro b hb
    rw [yJet_d0]
    exact Y_mem_e8SlopeRange hb
  · intro b hb
    rw [xJet_d0, yJet_d0]
    exact (E8TAxisStableScalar.e8Q_Y hb).symm
  · exact ha
  · exact hp

/-- The six recurrence values are the raw derivatives at the scalar slope
`Y a`, with no higher derivative matching hypotheses. -/
theorem inverseJet_components {a : ℝ} (ha : 0 < a) (hp : yJet.d1 a ≠ 0) :
    inverseJet.d0 a = (e8QJet5 e8ThetaCanonicalJet5).d0 (E8TAxisStableScalar.Y a) ∧
    inverseJet.d1 a = (e8QJet5 e8ThetaCanonicalJet5).d1 (E8TAxisStableScalar.Y a) ∧
    inverseJet.d2 a = (e8QJet5 e8ThetaCanonicalJet5).d2 (E8TAxisStableScalar.Y a) ∧
    inverseJet.d3 a = (e8QJet5 e8ThetaCanonicalJet5).d3 (E8TAxisStableScalar.Y a) ∧
    inverseJet.d4 a = (e8QJet5 e8ThetaCanonicalJet5).d4 (E8TAxisStableScalar.Y a) ∧
    inverseJet.d5 a = (e8QJet5 e8ThetaCanonicalJet5).d5 (E8TAxisStableScalar.Y a) := by
  simpa only [Jet5.EqAt, atParam, Function.comp_def, yJet_d0] using
    inverseJet_eq_canonical ha hp

end GeneralCK.Certificates.E8TAxisStableJet5

end


