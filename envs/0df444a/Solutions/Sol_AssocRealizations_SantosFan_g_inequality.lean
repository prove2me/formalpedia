-- Prove2me | solution 1 for AssocRealizations.SantosFan.g_inequality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:24:42.513971+00:00
-- url     : https://prove2.me/submissions/afa8f3e0-d30e-40ac-8c53-6656d310a819

import Mathlib
import Definitions.Def_AssocRealizations_SantosFan_Setting

set_option autoImplicit false
open AssocRealizations.SantosFan ChvatalArtGallery.FanPartition

theorem solution (n : ℕ) (i j k l : ℤ) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (hkl : k < l) (hl : l ≤ (n : ℤ) + 3) :
    max (gW n i j + gW n k l) (gW n i l + gW n j k) < gW n i k + gW n j l := by
  have e1 : gW n i k + gW n j l - (gW n i j + gW n k l) = 2 * (k - j) * ((n : ℤ) + 3 + i - l) := by
    unfold gW; ring
  have e2 : gW n i k + gW n j l - (gW n i l + gW n j k) = 2 * (j - i) * (l - k) := by
    unfold gW; ring
  have p1 : 0 < 2 * (k - j) * ((n : ℤ) + 3 + i - l) := by
    have : 0 < (n : ℤ) + 3 + i - l := by linarith
    have : 0 < k - j := by linarith
    positivity
  have p2 : 0 < 2 * (j - i) * (l - k) := by
    have : 0 < j - i := by linarith
    have : 0 < l - k := by linarith
    positivity
  rw [max_lt_iff]
  constructor <;> linarith
