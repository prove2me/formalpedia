-- Prove2me | Definitions.Def_Esgk_MaximallyCircularDegreeTwoCircle
-- name    : Esgk_MaximallyCircularDegreeTwoCircle
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:02:43.365993+00:00
-- url     : https://prove2.me/theorems/32c8713d-6bf2-456b-b17c-32c7f74ede69
-- title:
--   Translation center for a degree-two circular chart
-- statement:
--   This defines the planar translation center associated with a complex isotropic parameter in the degree-two circular setting.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCircleFactor
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

def bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter (ξ : ℂ) : _root_.Point2 :=
  WithLp.toLp 2 ![-ξ.re, -ξ.im]


end Esgk


