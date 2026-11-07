-- Prove2me | Definitions.Def_HWMaskLeak_energy
-- name    : HWMaskLeak_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:11.797209+00:00
-- url     : https://prove2.me/theorems/110c0e2f-037f-45b9-a37a-8a4d65c59bb8
-- title:
--   Energy proxy $F_m$, eq. (11)
-- statement:
--   For an integer $m\ge1$, the **energy proxy** is
--   $$
--   F_m:=\sum_{w\in W^m}\Bigl(\sum_{t\ne0}\prod_{j=1}^m\bigl|\hat S_{w_j}(t)\bigr|^2\Bigr)^{1/2},
--   $$
--   where $W=\mathrm{wt}(G)$ and $t$ runs over the nonzero residues of $G=\mathbb Z/N\mathbb Z$.
--
--   It is the secret-independent $L^2$ quantity to which Lemma 3.1 reduces the insecurity: $2E_k(s)\le 2\Delta_{k-1}\le F_{k-1}$.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §3, p.18, eq. (11)

import Mathlib
import Definitions.Def_HWMaskLeak_wt
import Definitions.Def_HWMaskLeak_fhat
import Definitions.Def_HWMaskLeak_slice

namespace HWMaskLeak

/-- **The energy proxy `F_m`, eq. (11)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their
Weight: From Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31,
2026, sha256 ab686360…), §3, p.18):
`F_m := Σ_{w ∈ W^m} ( Σ_{t ≠ 0} Π_{j=1}^m |Ŝ_{w_j}(t)|² )^{1/2}`, with `W = wt(G)` and `t` ranging over
the nonzero residues of `G = ℤ/Nℤ`. -/
noncomputable def energy (N : ℕ) [NeZero N] (m : ℕ) : ℝ :=
  ∑ w ∈ Fintype.piFinset (fun _ : Fin m => weights N),
    Real.sqrt (∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0),
      ∏ j, ‖fhat N (slice N (w j)) t‖ ^ 2)

end HWMaskLeak


