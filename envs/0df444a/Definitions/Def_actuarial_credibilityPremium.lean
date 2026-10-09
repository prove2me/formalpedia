-- Prove2me | Definitions.Def_actuarial_credibilityPremium
-- name    : actuarial_credibilityPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:52:14.223774+00:00
-- url     : https://prove2.me/theorems/9dbc0e01-9305-49d6-af7b-49ad3df13ae9
-- title:
--   Credibility-weighted observed and collective pure premium
-- statement:
--   The Bühlmann premium blends the observed average claim level and the collective expected claim level. The observed experience receives weight z, while the complementary weight belongs to the population mean, and the two weights sum to one.
--
--   **Mathematical statement**
--
--   $$
--   \hat\mu=Z\bar X+(1-Z)\mu
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib

namespace ActuarialValuation

noncomputable def credibilityPremium
  (collective experience z : ℝ) : ℝ :=
  z * experience + (1 - z) * collective

end ActuarialValuation


