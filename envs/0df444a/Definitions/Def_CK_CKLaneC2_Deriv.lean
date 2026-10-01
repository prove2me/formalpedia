-- Prove2me | Definitions.Def_CK_CKLaneC2_Deriv
-- name    : CK_CKLaneC2_Deriv
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:40:07.758811+00:00
-- url     : https://prove2.me/theorems/dbf7aba9-1cfa-4925-bdfe-34b7558212a1
-- title:
--   Courtade–Kumar proof module `CKLaneC2.Deriv` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.Deriv` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.Deriv` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.Deriv (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/Deriv.lean)

import Definitions.Def_CK_CKLaneC2_Atoms
import Definitions.Def_CK_CKLaneC2_Forms

-- ===== source module CKLaneC2.Deriv =====
section
/-
Lane C2 — the monotonicity target `Gf` and its derivative.

`Gf c = Nf c / Dnf c` is the arctan-comparison slope `gfun` expressed in the contact coordinate `c`
(see `Bridge.gfun_xParam`):
    Nf  = 2L(1-c^2)^2 K^3 - E^3 (2K - c^2),     Dnf = 2 L c^2 E (2K - c^2).
With `E' = -A/2`, `K' = c/(1-c^2)` (Atoms), `Gf' = (Npf·Dnf - Nf·Dnpf)/Dnf^2`, and
    `(Npf·Dnf - Nf·Dnpf)(1-c^2) = Wt c := Ex.evalR [c, E, K, A, L] Wex`     (`W_identity`).
So `Wt < 0` on an interval makes `Gf` antitone there (`Gf_antitone_of_Wt_neg`).
-/

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

noncomputable def Nf (c : ℝ) : ℝ :=
  2 * Real.log 2 * (1 - c ^ 2) ^ 2 * Kf c ^ 3 - Ef c ^ 3 * (2 * Kf c - c ^ 2)
noncomputable def Dnf (c : ℝ) : ℝ := 2 * Real.log 2 * c ^ 2 * Ef c * (2 * Kf c - c ^ 2)
noncomputable def Gf (c : ℝ) : ℝ := Nf c / Dnf c

noncomputable def Npf (c : ℝ) : ℝ :=
  2 * Real.log 2 * (2 * (1 - c ^ 2) * (-(2 * c)) * Kf c ^ 3
      + (1 - c ^ 2) ^ 2 * (3 * Kf c ^ 2 * (c / (1 - c ^ 2))))
    - (3 * Ef c ^ 2 * (-(Af c) / 2) * (2 * Kf c - c ^ 2)
      + Ef c ^ 3 * (2 * (c / (1 - c ^ 2)) - 2 * c))
noncomputable def Dnpf (c : ℝ) : ℝ :=
  2 * Real.log 2 * (2 * c * Ef c * (2 * Kf c - c ^ 2)
    + c ^ 2 * (-(Af c) / 2) * (2 * Kf c - c ^ 2)
    + c ^ 2 * Ef c * (2 * (c / (1 - c ^ 2)) - 2 * c))

/-- The sign-carrying numerator of `Gf'`, as the certified expression `Wex`. -/
noncomputable def Wt (c : ℝ) : ℝ := Ex.evalR [c, Ef c, Kf c, Af c, Real.log 2] Wex

theorem Dnf_pos {c : ℝ} (h0 : 0 < c) (h1 : c < 1) : 0 < Dnf c := by
  have hE := Ef_pos h0.le h1
  have hK := two_Kf_sub_pos h0.le h1
  have hL := log_two_pos'
  unfold Dnf
  positivity

theorem hasDerivAt_Nf {c : ℝ} (h0 : -1 < c) (h1 : c < 1) : HasDerivAt Nf (Npf c) c := by
  have hK := hasDerivAt_Kf h0 h1
  have hE := hasDerivAt_Ef h0 h1
  have hsq : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * c)) c := by
    simpa using ((hasDerivAt_pow 2 c).const_sub 1)
  have hc2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * c) c := by
    simpa using hasDerivAt_pow 2 c
  have h := (((hsq.pow 2).mul (hK.pow 3)).const_mul (2 * Real.log 2)).sub
    ((hE.pow 3).mul ((hK.const_mul 2).sub hc2))
  have hfun : Nf = fun y => 2 * Real.log 2 * ((1 - y ^ 2) ^ 2 * Kf y ^ 3)
      - Ef y ^ 3 * (2 * Kf y - y ^ 2) := by
    funext y; unfold Nf; ring
  rw [hfun]
  refine h.congr_deriv ?_
  unfold Npf
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Nat.cast_ofNat]
  ring

theorem hasDerivAt_Dnf {c : ℝ} (h0 : -1 < c) (h1 : c < 1) : HasDerivAt Dnf (Dnpf c) c := by
  have hK := hasDerivAt_Kf h0 h1
  have hE := hasDerivAt_Ef h0 h1
  have hc2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * c) c := by
    simpa using hasDerivAt_pow 2 c
  have h := ((hc2.mul hE).mul ((hK.const_mul 2).sub hc2)).const_mul (2 * Real.log 2)
  have hfun : Dnf = fun y => 2 * Real.log 2 * (y ^ 2 * Ef y * (2 * Kf y - y ^ 2)) := by
    funext y; unfold Dnf; ring
  rw [hfun]
  refine h.congr_deriv ?_
  unfold Dnpf
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Nat.cast_ofNat]
  ring

theorem hasDerivAt_Gf {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    HasDerivAt Gf ((Npf c * Dnf c - Nf c * Dnpf c) / Dnf c ^ 2) c :=
  (hasDerivAt_Nf (by linarith) h1).div (hasDerivAt_Dnf (by linarith) h1) (Dnf_pos h0 h1).ne'

theorem W_identity {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    (Npf c * Dnf c - Nf c * Dnpf c) * (1 - c ^ 2) = Wt c := by
  have hne : (1 : ℝ) - c ^ 2 ≠ 0 := by nlinarith
  unfold Wt Npf Dnf Nf Dnpf
  simp only [Wex, Ex.evalR, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  field_simp
  ring

theorem Gf_deriv_neg {c : ℝ} (h0 : 0 < c) (h1 : c < 1) (hW : Wt c < 0) :
    (Npf c * Dnf c - Nf c * Dnpf c) / Dnf c ^ 2 < 0 := by
  have hpos : (0 : ℝ) < 1 - c ^ 2 := by nlinarith
  have hnum : Npf c * Dnf c - Nf c * Dnpf c < 0 := by
    have := W_identity h0 h1
    by_contra hc
    have hc' := le_of_not_gt hc
    have : 0 ≤ (Npf c * Dnf c - Nf c * Dnpf c) * (1 - c ^ 2) := mul_nonneg hc' hpos.le
    linarith
  exact div_neg_of_neg_of_pos hnum (by have := Dnf_pos h0 h1; positivity)

theorem Gf_antitone_of_Wt_neg {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hW : ∀ t : ℝ, a ≤ t → t ≤ b → Wt t < 0) : AntitoneOn Gf (Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (f' := fun c => (Npf c * Dnf c - Nf c * Dnpf c) / Dnf c ^ 2)
  · intro t ht
    exact (hasDerivAt_Gf (lt_of_lt_of_le ha ht.1) (lt_of_le_of_lt ht.2 hb)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_Gf (lt_trans ha ht.1) (lt_trans ht.2 hb)).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (Gf_deriv_neg (lt_trans ha ht.1) (lt_trans ht.2 hb) (hW t ht.1.le ht.2.le)).le

end CKLaneC2

end


