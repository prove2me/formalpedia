-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0142Geometry__20
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0142Geometry__20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:23:18.680398+00:00
-- url     : https://prove2.me/theorems/f284e623-fac0-4379-a9c8-3fff28b48a18
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0142Geometry (+19 modules: GeneralCK.Certificates.E8TAxisProd0143Geometry, GeneralCK.Certificates.E8TAxisProd0144Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0142Geometry (+19 modules: GeneralCK.Certificates.E8TAxisProd0143Geometry, GeneralCK.Certificates.E8TAxisProd0144Geometry, GeneralCK.Certificates.E8TAxisProd0145Geometry, GeneralCK.Certificates.E8TAxisProd0146Geometry, GeneralCK.Certificates.E8TAxisProd0147Geometry, GeneralCK.Certificates.E8TAxisProd0148Geometry, GeneralCK.Certificates.E8TAxisProd0149Geometry, GeneralCK.Certificates.E8TAxisProd0150Geometry, GeneralCK.Certificates.E8TAxisProd0151Geometry, GeneralCK.Certificates.E8TAxisProd0152Geometry, GeneralCK.Certificates.E8TAxisProd0153Geometry, GeneralCK.Certificates.E8TAxisProd0154Geometry, GeneralCK.Certificates.E8TAxisProd0155Geometry, GeneralCK.Certificates.E8TAxisProd0156Geometry, GeneralCK.Certificates.E8TAxisProd0157Geometry, GeneralCK.Certificates.E8TAxisProd0158Geometry, GeneralCK.Certificates.E8TAxisProd0159Geometry, GeneralCK.Certificates.E8TAxisProd0160Geometry, GeneralCK.Certificates.E8TAxisProd0161Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0142Geometry (+19 modules: GeneralCK.Certificates.E8TAxisProd0143Geometry, GeneralCK.Certificates.E8TAxisProd0144Geometry, GeneralCK.Certificates.E8TAxisProd0145Geometry, GeneralCK.Certificates.E8TAxisProd0146Geometry, GeneralCK.Certificates.E8TAxisProd0147Geometry, GeneralCK.Certificates.E8TAxisProd0148Geometry, GeneralCK.Certificates.E8TAxisProd0149Geometry, GeneralCK.Certificates.E8TAxisProd0150Geometry, GeneralCK.Certificates.E8TAxisProd0151Geometry, GeneralCK.Certificates.E8TAxisProd0152Geometry, GeneralCK.Certificates.E8TAxisProd0153Geometry, GeneralCK.Certificates.E8TAxisProd0154Geometry, GeneralCK.Certificates.E8TAxisProd0155Geometry, GeneralCK.Certificates.E8TAxisProd0156Geometry, GeneralCK.Certificates.E8TAxisProd0157Geometry, GeneralCK.Certificates.E8TAxisProd0158Geometry, GeneralCK.Certificates.E8TAxisProd0159Geometry, GeneralCK.Certificates.E8TAxisProd0160Geometry, GeneralCK.Certificates.E8TAxisProd0161Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0142Geometry (+19 modules: GeneralCK.Certificates.E8TAxisProd0143Geometry, GeneralCK.Certificates.E8TAxisProd0144Geometry, GeneralCK.Certificates.E8TAxisProd0145Geometry, GeneralCK.Certificates.E8TAxisProd0146Geometry, GeneralCK.Certificates.E8TAxisProd0147Geometry, GeneralCK.Certificates.E8TAxisProd0148Geometry, GeneralCK.Certificates.E8TAxisProd0149Geometry, GeneralCK.Certificates.E8TAxisProd0150Geometry, GeneralCK.Certificates.E8TAxisProd0151Geometry, GeneralCK.Certificates.E8TAxisProd0152Geometry, GeneralCK.Certificates.E8TAxisProd0153Geometry, GeneralCK.Certificates.E8TAxisProd0154Geometry, GeneralCK.Certificates.E8TAxisProd0155Geometry, GeneralCK.Certificates.E8TAxisProd0156Geometry, GeneralCK.Certificates.E8TAxisProd0157Geometry, GeneralCK.Certificates.E8TAxisProd0158Geometry, GeneralCK.Certificates.E8TAxisProd0159Geometry, GeneralCK.Certificates.E8TAxisProd0160Geometry, GeneralCK.Certificates.E8TAxisProd0161Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0142Geometry (+19 modules: GeneralCK/Certificates/E8TAxisProd0143Geometry, GeneralCK/Certificates/E8TAxisProd0144Geometry, GeneralCK/Certificates/E8TAxisProd0145Geometry, GeneralCK/Certificates/E8TAxisProd0146Geometry, GeneralCK/Certificates/E8TAxisProd0147Geometry, GeneralCK/Certificates/E8TAxisProd0148Geometry, GeneralCK/Certificates/E8TAxisProd0149Geometry, GeneralCK/Certificates/E8TAxisProd0150Geometry, GeneralCK/Certificates/E8TAxisProd0151Geometry, GeneralCK/Certificates/E8TAxisProd0152Geometry, GeneralCK/Certificates/E8TAxisProd0153Geometry, GeneralCK/Certificates/E8TAxisProd0154Geometry, GeneralCK/Certificates/E8TAxisProd0155Geometry, GeneralCK/Certificates/E8TAxisProd0156Geometry, GeneralCK/Certificates/E8TAxisProd0157Geometry, GeneralCK/Certificates/E8TAxisProd0158Geometry, GeneralCK/Certificates/E8TAxisProd0159Geometry, GeneralCK/Certificates/E8TAxisProd0160Geometry, GeneralCK/Certificates/E8TAxisProd0161Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisProd0142Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0142Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (27 / 16 : ℝ)
noncomputable def sUpper : ℝ := (7 / 4 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (55 / 32 : ℝ)
noncomputable def centerT : ℝ := (62499999999999999999999999999999999999999999999999999999996266190833283 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0142Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0143Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0143Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13 / 8 : ℝ)
noncomputable def sUpper : ℝ := (27 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (53 / 32 : ℝ)
noncomputable def centerT : ℝ := (62499999999999999999999999999999999999999999999999999999996266190833283 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0143Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0144Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0144Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (25 / 16 : ℝ)
noncomputable def sUpper : ℝ := (13 / 8 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (51 / 32 : ℝ)
noncomputable def centerT : ℝ := (5468749999999999999999999999999999999999999999999999999999595504006939 / 625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0144Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0145Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0145Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3 / 2 : ℝ)
noncomputable def sUpper : ℝ := (25 / 16 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (49 / 32 : ℝ)
noncomputable def centerT : ℝ := (5468749999999999999999999999999999999999999999999999999999595504006939 / 625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0145Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0146Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0146Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (25 / 16 : ℝ)
noncomputable def sUpper : ℝ := (13 / 8 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (51 / 32 : ℝ)
noncomputable def centerT : ℝ := (62499999999999999999999999999999999999999999999999999999996266190833283 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0146Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0147Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0147Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3 / 2 : ℝ)
noncomputable def sUpper : ℝ := (25 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (49 / 32 : ℝ)
noncomputable def centerT : ℝ := (62499999999999999999999999999999999999999999999999999999996266190833283 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0147Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0148Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0148Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (27 / 16 : ℝ)
noncomputable def sUpper : ℝ := (7 / 4 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (55 / 32 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0148Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0149Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0149Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13 / 8 : ℝ)
noncomputable def sUpper : ℝ := (27 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (53 / 32 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0149Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0150Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0150Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (25 / 16 : ℝ)
noncomputable def sUpper : ℝ := (13 / 8 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (51 / 32 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0150Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0151Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0151Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3 / 2 : ℝ)
noncomputable def sUpper : ℝ := (25 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (49 / 32 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0151Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0152Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0152Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (23 / 16 : ℝ)
noncomputable def sUpper : ℝ := (3 / 2 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (47 / 32 : ℝ)
noncomputable def centerT : ℝ := (37500000000000000000000000000000000000000000000000000000001194818933349 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0152Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0153Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0153Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11 / 8 : ℝ)
noncomputable def sUpper : ℝ := (23 / 16 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (45 / 32 : ℝ)
noncomputable def centerT : ℝ := (37500000000000000000000000000000000000000000000000000000001194818933349 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0153Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0154Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0154Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (23 / 16 : ℝ)
noncomputable def sUpper : ℝ := (3 / 2 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (47 / 32 : ℝ)
noncomputable def centerT : ℝ := (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0154Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0155Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0155Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11 / 8 : ℝ)
noncomputable def sUpper : ℝ := (23 / 16 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (45 / 32 : ℝ)
noncomputable def centerT : ℝ := (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0155Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0156Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0156Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (21 / 16 : ℝ)
noncomputable def sUpper : ℝ := (11 / 8 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (43 / 32 : ℝ)
noncomputable def centerT : ℝ := (37500000000000000000000000000000000000000000000000000000001194818933349 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0156Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0157Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0157Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5 / 4 : ℝ)
noncomputable def sUpper : ℝ := (21 / 16 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (41 / 32 : ℝ)
noncomputable def centerT : ℝ := (37500000000000000000000000000000000000000000000000000000001194818933349 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0157Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0158Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0158Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (21 / 16 : ℝ)
noncomputable def sUpper : ℝ := (11 / 8 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (43 / 32 : ℝ)
noncomputable def centerT : ℝ := (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0158Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0159Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0159Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5 / 4 : ℝ)
noncomputable def sUpper : ℝ := (21 / 16 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (41 / 32 : ℝ)
noncomputable def centerT : ℝ := (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0159Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0160Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0160Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (23 / 16 : ℝ)
noncomputable def sUpper : ℝ := (3 / 2 : ℝ)
noncomputable def tLower : ℝ := (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (47 / 32 : ℝ)
noncomputable def centerT : ℝ := (27499999999999999999999999999999999999999999999999999999997610362133301 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0160Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0161Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0161Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11 / 8 : ℝ)
noncomputable def sUpper : ℝ := (23 / 16 : ℝ)
noncomputable def tLower : ℝ := (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (45 / 32 : ℝ)
noncomputable def centerT : ℝ := (27499999999999999999999999999999999999999999999999999999997610362133301 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-1826877046663628647754606040895353774569915679, 1826877046663628647754606040895353774569915679⟩
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

end GeneralCK.Certificates.E8TAxisProd0161Geometry

end


