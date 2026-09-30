-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0592Geometry__10
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0592Geometry__10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:24:10.657377+00:00
-- url     : https://prove2.me/theorems/de5d1c70-447a-4fa5-90a9-46b43cc1a547
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0592Geometry (+9 modules: GeneralCK.Certificates.E8TAxisProd0593Geometry, GeneralCK.Certificates.E8TAxisProd0594Geometry, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0592Geometry (+9 modules: GeneralCK.Certificates.E8TAxisProd0593Geometry, GeneralCK.Certificates.E8TAxisProd0594Geometry, GeneralCK.Certificates.E8TAxisProd0595Geometry, GeneralCK.Certificates.E8TAxisProd0596Geometry, GeneralCK.Certificates.E8TAxisProd0597Geometry, GeneralCK.Certificates.E8TAxisProd0598Geometry, GeneralCK.Certificates.E8TAxisProd0599Geometry, GeneralCK.Certificates.E8TAxisProd0600Geometry, GeneralCK.Certificates.E8TAxisProd0601Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0592Geometry (+9 modules: GeneralCK.Certificates.E8TAxisProd0593Geometry, GeneralCK.Certificates.E8TAxisProd0594Geometry, GeneralCK.Certificates.E8TAxisProd0595Geometry, GeneralCK.Certificates.E8TAxisProd0596Geometry, GeneralCK.Certificates.E8TAxisProd0597Geometry, GeneralCK.Certificates.E8TAxisProd0598Geometry, GeneralCK.Certificates.E8TAxisProd0599Geometry, GeneralCK.Certificates.E8TAxisProd0600Geometry, GeneralCK.Certificates.E8TAxisProd0601Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0592Geometry (+9 modules: GeneralCK.Certificates.E8TAxisProd0593Geometry, GeneralCK.Certificates.E8TAxisProd0594Geometry, GeneralCK.Certificates.E8TAxisProd0595Geometry, GeneralCK.Certificates.E8TAxisProd0596Geometry, GeneralCK.Certificates.E8TAxisProd0597Geometry, GeneralCK.Certificates.E8TAxisProd0598Geometry, GeneralCK.Certificates.E8TAxisProd0599Geometry, GeneralCK.Certificates.E8TAxisProd0600Geometry, GeneralCK.Certificates.E8TAxisProd0601Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0592Geometry (+9 modules: GeneralCK/Certificates/E8TAxisProd0593Geometry, GeneralCK/Certificates/E8TAxisProd0594Geometry, GeneralCK/Certificates/E8TAxisProd0595Geometry, GeneralCK/Certificates/E8TAxisProd0596Geometry, GeneralCK/Certificates/E8TAxisProd0597Geometry, GeneralCK/Certificates/E8TAxisProd0598Geometry, GeneralCK/Certificates/E8TAxisProd0599Geometry, GeneralCK/Certificates/E8TAxisProd0600Geometry, GeneralCK/Certificates/E8TAxisProd0601Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisProd0592Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0592Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24132812500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0592Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0593Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0593Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (151 / 64 : ℝ)
noncomputable def sUpper : ℝ := (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23773437500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0593Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0594Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0594Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24132812500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0594Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0595Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0595Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (151 / 64 : ℝ)
noncomputable def sUpper : ℝ := (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23773437500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0595Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0596Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0596Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (151 / 64 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23414062499999999999999999999999999999999999999999999999999362763235547 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0596Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0597Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0597Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23054687499999999999999999999999999999999999999999999999998088289706641 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0597Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0598Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0598Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (151 / 64 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23414062499999999999999999999999999999999999999999999999999362763235547 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0598Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0599Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0599Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (87500000000000000000000000000000000000000000000000000000005974094666747 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23054687499999999999999999999999999999999999999999999999998088289706641 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0599Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0600Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0600Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24132812500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0600Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0601Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0601Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (151 / 64 : ℝ)
noncomputable def sUpper : ℝ := (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (31249999999999999999999999999999999999999999999999999999995021587777711 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23773437500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0601Geometry

end


