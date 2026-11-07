-- Prove2me | Definitions.Def_PrivLittlestone_epsS
-- name    : PrivLittlestone_epsS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:46.678766+00:00
-- url     : https://prove2.me/theorems/6089d96e-11ca-4740-a46d-a50265fe084e
-- title:
--   Per-release privacy parameter $\varepsilon_s = \varepsilon/(8\sqrt{2KmL_\delta})$
-- statement:
--   The per-release privacy parameter
--   $$
--   \varepsilon_s = \frac{\varepsilon}{8\sqrt{2 K m L_\delta}}
--   $$
--   of (5), for the phase cap $K$ and the number $m$ of samples per phase.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (5), p.8

import Mathlib
import Definitions.Def_PrivLittlestone_Ldelta

namespace PrivLittlestone

/-- The per-release privacy parameter `ε_s = ε/(8 √(2 K m L_δ))` (He–He, *Private Online Learning
of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), (5), p.8). -/
noncomputable def epsS (K m : ℕ) (ε δ : ℝ) : ℝ :=
  ε / (8 * Real.sqrt (2 * (K : ℝ) * (m : ℝ) * Ldelta δ))

end PrivLittlestone


