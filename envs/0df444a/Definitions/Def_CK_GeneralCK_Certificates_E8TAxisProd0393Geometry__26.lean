-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0393Geometry__26
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0393Geometry__26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:31:08.216136+00:00
-- url     : https://prove2.me/theorems/ef744798-f033-469a-9e32-de28f6deb19d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0393Geometry (+25 modules: GeneralCK.Certificates.E8TAxisProd0394Geometry, GeneralCK.Certificates.E8TAxisProd0395Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0393Geometry (+25 modules: GeneralCK.Certificates.E8TAxisProd0394Geometry, GeneralCK.Certificates.E8TAxisProd0395Geometry, GeneralCK.Certificates.E8TAxisProd0396Geometry, GeneralCK.Certificates.E8TAxisProd0397Geometry, GeneralCK.Certificates.E8TAxisProd0398Geometry, GeneralCK.Certificates.E8TAxisProd0399Geometry, GeneralCK.Certificates.E8TAxisProd0400Geometry, GeneralCK.Certificates.E8TAxisProd0401Geometry, GeneralCK.Certificates.E8TAxisProd0402Geometry, GeneralCK.Certificates.E8TAxisProd0403Geometry, GeneralCK.Certificates.E8TAxisProd0404Geometry, GeneralCK.Certificates.E8TAxisProd0405Geometry, GeneralCK.Certificates.E8TAxisProd0406Geometry, GeneralCK.Certificates.E8TAxisProd0407Geometry, GeneralCK.Certificates.E8TAxisProd0408Geometry, GeneralCK.Certificates.E8TAxisProd0409Geometry, GeneralCK.Certificates.E8TAxisProd0410Geometry, GeneralCK.Certificates.E8TAxisProd0411Geometry, GeneralCK.Certificates.E8TAxisProd0412Geometry, GeneralCK.Certificates.E8TAxisProd0413Geometry, GeneralCK.Certificates.E8TAxisProd0414Geometry, GeneralCK.Certificates.E8TAxisProd0415Geometry, GeneralCK.Certificates.E8TAxisProd0416Geometry, GeneralCK.Certificates.E8TAxisProd0417Geometry, GeneralCK.Certificates.E8TAxisProd0418Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0393Geometry (+25 modules: GeneralCK.Certificates.E8TAxisProd0394Geometry, GeneralCK.Certificates.E8TAxisProd0395Geometry, GeneralCK.Certificates.E8TAxisProd0396Geometry, GeneralCK.Certificates.E8TAxisProd0397Geometry, GeneralCK.Certificates.E8TAxisProd0398Geometry, GeneralCK.Certificates.E8TAxisProd0399Geometry, GeneralCK.Certificates.E8TAxisProd0400Geometry, GeneralCK.Certificates.E8TAxisProd0401Geometry, GeneralCK.Certificates.E8TAxisProd0402Geometry, GeneralCK.Certificates.E8TAxisProd0403Geometry, GeneralCK.Certificates.E8TAxisProd0404Geometry, GeneralCK.Certificates.E8TAxisProd0405Geometry, GeneralCK.Certificates.E8TAxisProd0406Geometry, GeneralCK.Certificates.E8TAxisProd0407Geometry, GeneralCK.Certificates.E8TAxisProd0408Geometry, GeneralCK.Certificates.E8TAxisProd0409Geometry, GeneralCK.Certificates.E8TAxisProd0410Geometry, GeneralCK.Certificates.E8TAxisProd0411Geometry, GeneralCK.Certificates.E8TAxisProd0412Geometry, GeneralCK.Certificates.E8TAxisProd0413Geometry, GeneralCK.Certificates.E8TAxisProd0414Geometry, GeneralCK.Certificates.E8TAxisProd0415Geometry, GeneralCK.Certificates.E8TAxisProd0416Geometry, GeneralCK.Certificates.E8TAxisProd0417Geometry, GeneralCK.Certificates.E8TAxisProd0418Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0393Geometry (+25 modules: GeneralCK.Certificates.E8TAxisProd0394Geometry, GeneralCK.Certificates.E8TAxisProd0395Geometry, GeneralCK.Certificates.E8TAxisProd0396Geometry, GeneralCK.Certificates.E8TAxisProd0397Geometry, GeneralCK.Certificates.E8TAxisProd0398Geometry, GeneralCK.Certificates.E8TAxisProd0399Geometry, GeneralCK.Certificates.E8TAxisProd0400Geometry, GeneralCK.Certificates.E8TAxisProd0401Geometry, GeneralCK.Certificates.E8TAxisProd0402Geometry, GeneralCK.Certificates.E8TAxisProd0403Geometry, GeneralCK.Certificates.E8TAxisProd0404Geometry, GeneralCK.Certificates.E8TAxisProd0405Geometry, GeneralCK.Certificates.E8TAxisProd0406Geometry, GeneralCK.Certificates.E8TAxisProd0407Geometry, GeneralCK.Certificates.E8TAxisProd0408Geometry, GeneralCK.Certificates.E8TAxisProd0409Geometry, GeneralCK.Certificates.E8TAxisProd0410Geometry, GeneralCK.Certificates.E8TAxisProd0411Geometry, GeneralCK.Certificates.E8TAxisProd0412Geometry, GeneralCK.Certificates.E8TAxisProd0413Geometry, GeneralCK.Certificates.E8TAxisProd0414Geometry, GeneralCK.Certificates.E8TAxisProd0415Geometry, GeneralCK.Certificates.E8TAxisProd0416Geometry, GeneralCK.Certificates.E8TAxisProd0417Geometry, GeneralCK.Certificates.E8TAxisProd0418Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0393Geometry (+25 modules: GeneralCK/Certificates/E8TAxisProd0394Geometry, GeneralCK/Certificates/E8TAxisProd0395Geometry, GeneralCK/Certificates/E8TAxisProd0396Geometry, GeneralCK/Certificates/E8TAxisProd0397Geometry, GeneralCK/Certificates/E8TAxisProd0398Geometry, GeneralCK/Certificates/E8TAxisProd0399Geometry, GeneralCK/Certificates/E8TAxisProd0400Geometry, GeneralCK/Certificates/E8TAxisProd0401Geometry, GeneralCK/Certificates/E8TAxisProd0402Geometry, GeneralCK/Certificates/E8TAxisProd0403Geometry, GeneralCK/Certificates/E8TAxisProd0404Geometry, GeneralCK/Certificates/E8TAxisProd0405Geometry, GeneralCK/Certificates/E8TAxisProd0406Geometry, GeneralCK/Certificates/E8TAxisProd0407Geometry, GeneralCK/Certificates/E8TAxisProd0408Geometry, GeneralCK/Certificates/E8TAxisProd0409Geometry, GeneralCK/Certificates/E8TAxisProd0410Geometry, GeneralCK/Certificates/E8TAxisProd0411Geometry, GeneralCK/Certificates/E8TAxisProd0412Geometry, GeneralCK/Certificates/E8TAxisProd0413Geometry, GeneralCK/Certificates/E8TAxisProd0414Geometry, GeneralCK/Certificates/E8TAxisProd0415Geometry, GeneralCK/Certificates/E8TAxisProd0416Geometry, GeneralCK/Certificates/E8TAxisProd0417Geometry, GeneralCK/Certificates/E8TAxisProd0418Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisProd0393Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0393Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (5617187500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (187499999999999999999999999999999999999999999999999999999995021587777711 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0393Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0394Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0394Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (28445312500000000000000000000000000000000000000000000000004460657351171 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (162500000000000000000000000000000000000000000000000000000003982729777831 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0394Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0395Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0395Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (5617187500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (162500000000000000000000000000000000000000000000000000000003982729777831 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0395Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0396Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0396Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27726562500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (187499999999999999999999999999999999999999999999999999999995021587777711 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0396Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0397Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0397Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (87 / 32 : ℝ)
noncomputable def sUpper : ℝ := (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27367187500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (187499999999999999999999999999999999999999999999999999999995021587777711 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0397Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0398Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0398Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27726562500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (162500000000000000000000000000000000000000000000000000000003982729777831 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0398Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0399Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0399Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (87 / 32 : ℝ)
noncomputable def sUpper : ℝ := (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27367187500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (162500000000000000000000000000000000000000000000000000000003982729777831 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0399Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0400Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0400Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (28445312500000000000000000000000000000000000000000000000004460657351171 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (68749999999999999999999999999999999999999999999999999999994025905333253 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0400Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0401Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0401Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (5617187500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (68749999999999999999999999999999999999999999999999999999994025905333253 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0401Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0402Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0402Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3578125000000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (28445312500000000000000000000000000000000000000000000000004460657351171 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (14062499999999999999999999999999999999999999999999999999998070865263863 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0402Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0403Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0403Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (14132812500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (5617187500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (14062499999999999999999999999999999999999999999999999999998070865263863 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0403Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0404Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0404Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27726562500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (68749999999999999999999999999999999999999999999999999999994025905333253 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0404Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0405Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0405Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (87 / 32 : ℝ)
noncomputable def sUpper : ℝ := (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27367187500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (68749999999999999999999999999999999999999999999999999999994025905333253 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0405Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0406Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0406Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6976562500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27726562500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (14062499999999999999999999999999999999999999999999999999998070865263863 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0406Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0407Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0407Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (87 / 32 : ℝ)
noncomputable def sUpper : ℝ := (13773437500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27367187500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (14062499999999999999999999999999999999999999999999999999998070865263863 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0407Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0408Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0408Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (87 / 32 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27007812499999999999999999999999999999999999999999999999999362763235547 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (187499999999999999999999999999999999999999999999999999999995021587777711 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0408Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0409Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0409Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (26648437499999999999999999999999999999999999999999999999998088289706641 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (187499999999999999999999999999999999999999999999999999999995021587777711 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0409Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0410Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0410Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (87 / 32 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27007812499999999999999999999999999999999999999999999999999362763235547 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (162500000000000000000000000000000000000000000000000000000003982729777831 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0410Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0411Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0411Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (26648437499999999999999999999999999999999999999999999999998088289706641 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (162500000000000000000000000000000000000000000000000000000003982729777831 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0411Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0412Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0412Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (673 / 256 : ℝ)
noncomputable def centerT : ℝ := (187499999999999999999999999999999999999999999999999999999995021587777711 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0412Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0413Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0413Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (25929687500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (187499999999999999999999999999999999999999999999999999999995021587777711 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0413Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0414Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0414Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (673 / 256 : ℝ)
noncomputable def centerT : ℝ := (162500000000000000000000000000000000000000000000000000000003982729777831 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0414Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0415Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0415Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6527343750000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (25929687500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (162500000000000000000000000000000000000000000000000000000003982729777831 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0415Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0416Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0416Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (87 / 32 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27007812499999999999999999999999999999999999999999999999999362763235547 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (68749999999999999999999999999999999999999999999999999999994025905333253 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0416Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0417Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0417Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6617187499999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (26648437499999999999999999999999999999999999999999999999998088289706641 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (68749999999999999999999999999999999999999999999999999999994025905333253 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0417Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0418Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0418Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13414062499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (87 / 32 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27007812499999999999999999999999999999999999999999999999999362763235547 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (14062499999999999999999999999999999999999999999999999999998070865263863 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-26261357545789661811472461837870710509442537882, 26261357545789661811472461837870710509442537882⟩
def dt : DyadicInterval 160 := ⟨-913438523331814323877303020447676887284957840, 913438523331814323877303020447676887284957840⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0418Geometry

end


