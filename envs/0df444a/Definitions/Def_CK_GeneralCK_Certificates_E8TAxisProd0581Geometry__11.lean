-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0581Geometry__11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0581Geometry__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:23:48.18564+00:00
-- url     : https://prove2.me/theorems/821f5198-f8f8-4550-aed9-30feecb82f55
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0581Geometry (+10 modules: GeneralCK.Certificates.E8TAxisProd0582Geometry, GeneralCK.Certificates.E8TAxisProd0583Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0581Geometry (+10 modules: GeneralCK.Certificates.E8TAxisProd0582Geometry, GeneralCK.Certificates.E8TAxisProd0583Geometry, GeneralCK.Certificates.E8TAxisProd0584Geometry, GeneralCK.Certificates.E8TAxisProd0585Geometry, GeneralCK.Certificates.E8TAxisProd0586Geometry, GeneralCK.Certificates.E8TAxisProd0587Geometry, GeneralCK.Certificates.E8TAxisProd0588Geometry, GeneralCK.Certificates.E8TAxisProd0589Geometry, GeneralCK.Certificates.E8TAxisProd0590Geometry, GeneralCK.Certificates.E8TAxisProd0591Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0581Geometry (+10 modules: GeneralCK.Certificates.E8TAxisProd0582Geometry, GeneralCK.Certificates.E8TAxisProd0583Geometry, GeneralCK.Certificates.E8TAxisProd0584Geometry, GeneralCK.Certificates.E8TAxisProd0585Geometry, GeneralCK.Certificates.E8TAxisProd0586Geometry, GeneralCK.Certificates.E8TAxisProd0587Geometry, GeneralCK.Certificates.E8TAxisProd0588Geometry, GeneralCK.Certificates.E8TAxisProd0589Geometry, GeneralCK.Certificates.E8TAxisProd0590Geometry, GeneralCK.Certificates.E8TAxisProd0591Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0581Geometry (+10 modules: GeneralCK.Certificates.E8TAxisProd0582Geometry, GeneralCK.Certificates.E8TAxisProd0583Geometry, GeneralCK.Certificates.E8TAxisProd0584Geometry, GeneralCK.Certificates.E8TAxisProd0585Geometry, GeneralCK.Certificates.E8TAxisProd0586Geometry, GeneralCK.Certificates.E8TAxisProd0587Geometry, GeneralCK.Certificates.E8TAxisProd0588Geometry, GeneralCK.Certificates.E8TAxisProd0589Geometry, GeneralCK.Certificates.E8TAxisProd0590Geometry, GeneralCK.Certificates.E8TAxisProd0591Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0581Geometry (+10 modules: GeneralCK/Certificates/E8TAxisProd0582Geometry, GeneralCK/Certificates/E8TAxisProd0583Geometry, GeneralCK/Certificates/E8TAxisProd0584Geometry, GeneralCK/Certificates/E8TAxisProd0585Geometry, GeneralCK/Certificates/E8TAxisProd0586Geometry, GeneralCK/Certificates/E8TAxisProd0587Geometry, GeneralCK/Certificates/E8TAxisProd0588Geometry, GeneralCK/Certificates/E8TAxisProd0589Geometry, GeneralCK/Certificates/E8TAxisProd0590Geometry, GeneralCK/Certificates/E8TAxisProd0591Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisProd0581Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0581Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (4898437500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0581Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0582Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0582Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24851562500000000000000000000000000000000000000000000000004460657351171 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0582Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0583Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0583Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (4898437500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0583Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0584Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0584Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (325 / 128 : ℝ)
noncomputable def sUpper : ℝ := (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (25570312500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0584Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0585Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0585Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (325 / 128 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (6302734375000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0585Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0586Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0586Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (325 / 128 : ℝ)
noncomputable def sUpper : ℝ := (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (25570312500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0586Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0587Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0587Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (325 / 128 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (6302734375000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0587Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0588Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0588Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24851562500000000000000000000000000000000000000000000000004460657351171 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0588Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0589Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0589Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (4898437500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0589Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0590Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0590Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24851562500000000000000000000000000000000000000000000000004460657351171 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0590Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0591Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0591Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (4898437500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0591Geometry

end


