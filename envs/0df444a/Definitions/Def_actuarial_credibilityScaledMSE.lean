-- Prove2me | Definitions.Def_actuarial_credibilityScaledMSE
-- name    : actuarial_credibilityScaledMSE
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:53:06.228633+00:00
-- url     : https://prove2.me/theorems/6e5fc6cf-b970-4fa0-a56b-73569a57e342
-- title:
--   Exposure-scaled mean squared credibility prediction error
-- statement:
--   For a risk mean with hypothetical-mean variance VHM and independent conditional observations with process variance EPV/totalExposure, the actual linear prediction MSE is VHM(1-z)^2+(EPV/totalExposure)z². Multiplication by positive total exposure gives this equivalent quadratic objective without a potentially singular division.
--
--   **Mathematical statement**
--
--   $$
--   P\,\mathrm{MSE}(z)=P\,\mathrm{VHM}(1-z)^2+\mathrm{EPV}z^2
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib

namespace ActuarialValuation

noncomputable def credibilityScaledMSE
  (totalExposure epv vhm z : ℝ) : ℝ :=
  totalExposure * vhm * (1 - z) ^ 2 + epv * z ^ 2

end ActuarialValuation


