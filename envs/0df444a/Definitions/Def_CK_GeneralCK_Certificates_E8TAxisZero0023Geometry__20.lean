-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0023Geometry__20
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0023Geometry__20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T01:15:35.230643+00:00
-- url     : https://prove2.me/theorems/3f57df63-ad06-4b67-9cd0-09d8139f2b8f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0023Geometry (+19 modules: GeneralCK.Certificates.E8TAxisZero0024Geometry, GeneralCK.Certificates.E8TAxisZero0025Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0023Geometry (+19 modules: GeneralCK.Certificates.E8TAxisZero0024Geometry, GeneralCK.Certificates.E8TAxisZero0025Geometry, GeneralCK.Certificates.E8TAxisZero0026Geometry, GeneralCK.Certificates.E8TAxisZero0027Geometry, GeneralCK.Certificates.E8TAxisZero0028Geometry, GeneralCK.Certificates.E8TAxisZero0029Geometry, GeneralCK.Certificates.E8TAxisZero0030Geometry, GeneralCK.Certificates.E8TAxisZero0031Geometry, GeneralCK.Certificates.E8TAxisZero0032Geometry, GeneralCK.Certificates.E8TAxisZero0033Geometry, GeneralCK.Certificates.E8TAxisZero0034Geometry, GeneralCK.Certificates.E8TAxisZero0035Geometry, GeneralCK.Certificates.E8TAxisZero0036Geometry, GeneralCK.Certificates.E8TAxisZero0037Geometry, GeneralCK.Certificates.E8TAxisZero0038Geometry, GeneralCK.Certificates.E8TAxisZero0039Geometry, GeneralCK.Certificates.E8TAxisZero0040Geometry, GeneralCK.Certificates.E8TAxisZero0041Geometry, GeneralCK.Certificates.E8TAxisZero0042Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0023Geometry (+19 modules: GeneralCK.Certificates.E8TAxisZero0024Geometry, GeneralCK.Certificates.E8TAxisZero0025Geometry, GeneralCK.Certificates.E8TAxisZero0026Geometry, GeneralCK.Certificates.E8TAxisZero0027Geometry, GeneralCK.Certificates.E8TAxisZero0028Geometry, GeneralCK.Certificates.E8TAxisZero0029Geometry, GeneralCK.Certificates.E8TAxisZero0030Geometry, GeneralCK.Certificates.E8TAxisZero0031Geometry, GeneralCK.Certificates.E8TAxisZero0032Geometry, GeneralCK.Certificates.E8TAxisZero0033Geometry, GeneralCK.Certificates.E8TAxisZero0034Geometry, GeneralCK.Certificates.E8TAxisZero0035Geometry, GeneralCK.Certificates.E8TAxisZero0036Geometry, GeneralCK.Certificates.E8TAxisZero0037Geometry, GeneralCK.Certificates.E8TAxisZero0038Geometry, GeneralCK.Certificates.E8TAxisZero0039Geometry, GeneralCK.Certificates.E8TAxisZero0040Geometry, GeneralCK.Certificates.E8TAxisZero0041Geometry, GeneralCK.Certificates.E8TAxisZero0042Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0023Geometry (+19 modules: GeneralCK.Certificates.E8TAxisZero0024Geometry, GeneralCK.Certificates.E8TAxisZero0025Geometry, GeneralCK.Certificates.E8TAxisZero0026Geometry, GeneralCK.Certificates.E8TAxisZero0027Geometry, GeneralCK.Certificates.E8TAxisZero0028Geometry, GeneralCK.Certificates.E8TAxisZero0029Geometry, GeneralCK.Certificates.E8TAxisZero0030Geometry, GeneralCK.Certificates.E8TAxisZero0031Geometry, GeneralCK.Certificates.E8TAxisZero0032Geometry, GeneralCK.Certificates.E8TAxisZero0033Geometry, GeneralCK.Certificates.E8TAxisZero0034Geometry, GeneralCK.Certificates.E8TAxisZero0035Geometry, GeneralCK.Certificates.E8TAxisZero0036Geometry, GeneralCK.Certificates.E8TAxisZero0037Geometry, GeneralCK.Certificates.E8TAxisZero0038Geometry, GeneralCK.Certificates.E8TAxisZero0039Geometry, GeneralCK.Certificates.E8TAxisZero0040Geometry, GeneralCK.Certificates.E8TAxisZero0041Geometry, GeneralCK.Certificates.E8TAxisZero0042Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0023Geometry (+19 modules: GeneralCK/Certificates/E8TAxisZero0024Geometry, GeneralCK/Certificates/E8TAxisZero0025Geometry, GeneralCK/Certificates/E8TAxisZero0026Geometry, GeneralCK/Certificates/E8TAxisZero0027Geometry, GeneralCK/Certificates/E8TAxisZero0028Geometry, GeneralCK/Certificates/E8TAxisZero0029Geometry, GeneralCK/Certificates/E8TAxisZero0030Geometry, GeneralCK/Certificates/E8TAxisZero0031Geometry, GeneralCK/Certificates/E8TAxisZero0032Geometry, GeneralCK/Certificates/E8TAxisZero0033Geometry, GeneralCK/Certificates/E8TAxisZero0034Geometry, GeneralCK/Certificates/E8TAxisZero0035Geometry, GeneralCK/Certificates/E8TAxisZero0036Geometry, GeneralCK/Certificates/E8TAxisZero0037Geometry, GeneralCK/Certificates/E8TAxisZero0038Geometry, GeneralCK/Certificates/E8TAxisZero0039Geometry, GeneralCK/Certificates/E8TAxisZero0040Geometry, GeneralCK/Certificates/E8TAxisZero0041Geometry, GeneralCK/Certificates/E8TAxisZero0042Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisZero0023Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0023Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (9 / 32 : ℝ)
noncomputable def sUpper : ℝ := (5 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (19 / 64 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-22835963083295358096932575511191922182123945984, 22835963083295358096932575511191922182123945984⟩
def dt : DyadicInterval 160 := ⟨-3653754093327257295509212081790707549139831358, 3653754093327257295509212081790707549139831358⟩

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
end GeneralCK.Certificates.E8TAxisZero0023Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0024Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0024Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (1 / 4 : ℝ)
noncomputable def sUpper : ℝ := (9 / 32 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (17 / 64 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-22835963083295358096932575511191922182123945984, 22835963083295358096932575511191922182123945984⟩
def dt : DyadicInterval 160 := ⟨-3653754093327257295509212081790707549139831358, 3653754093327257295509212081790707549139831358⟩

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
end GeneralCK.Certificates.E8TAxisZero0024Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0025Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0025Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (15 / 16 : ℝ)
noncomputable def sUpper : ℝ := (1 / 1 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (31 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-3653754093327257295509212081790707549139831358, 3653754093327257295509212081790707549139831358⟩

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
end GeneralCK.Certificates.E8TAxisZero0025Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0026Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0026Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (7 / 8 : ℝ)
noncomputable def sUpper : ℝ := (15 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (29 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-3653754093327257295509212081790707549139831358, 3653754093327257295509212081790707549139831358⟩

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
end GeneralCK.Certificates.E8TAxisZero0026Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0027Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0027Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (13 / 16 : ℝ)
noncomputable def sUpper : ℝ := (7 / 8 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-3653754093327257295509212081790707549139831358, 3653754093327257295509212081790707549139831358⟩

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
end GeneralCK.Certificates.E8TAxisZero0027Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0028Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0028Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3 / 4 : ℝ)
noncomputable def sUpper : ℝ := (13 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (25 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-3653754093327257295509212081790707549139831358, 3653754093327257295509212081790707549139831358⟩

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
end GeneralCK.Certificates.E8TAxisZero0028Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0029Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0029Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (11 / 16 : ℝ)
noncomputable def sUpper : ℝ := (3 / 4 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-3653754093327257295509212081790707549139831358, 3653754093327257295509212081790707549139831358⟩

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
end GeneralCK.Certificates.E8TAxisZero0029Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0030Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0030Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (5 / 8 : ℝ)
noncomputable def sUpper : ℝ := (11 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (21 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-45671926166590716193865151022383844364247891968, 45671926166590716193865151022383844364247891968⟩
def dt : DyadicInterval 160 := ⟨-3653754093327257295509212081790707549139831358, 3653754093327257295509212081790707549139831358⟩

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
end GeneralCK.Certificates.E8TAxisZero0030Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0031Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0031Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (19 / 32 : ℝ)
noncomputable def sUpper : ℝ := (5 / 8 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (39 / 64 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-22835963083295358096932575511191922182123945984, 22835963083295358096932575511191922182123945984⟩
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
end GeneralCK.Certificates.E8TAxisZero0031Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0032Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0032Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (9 / 16 : ℝ)
noncomputable def sUpper : ℝ := (19 / 32 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (37 / 64 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-22835963083295358096932575511191922182123945984, 22835963083295358096932575511191922182123945984⟩
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
end GeneralCK.Certificates.E8TAxisZero0032Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0033Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0033Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (17 / 32 : ℝ)
noncomputable def sUpper : ℝ := (9 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (35 / 64 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-22835963083295358096932575511191922182123945984, 22835963083295358096932575511191922182123945984⟩
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
end GeneralCK.Certificates.E8TAxisZero0033Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0034Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0034Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (1 / 2 : ℝ)
noncomputable def sUpper : ℝ := (17 / 32 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (33 / 64 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-22835963083295358096932575511191922182123945984, 22835963083295358096932575511191922182123945984⟩
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
end GeneralCK.Certificates.E8TAxisZero0034Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0035Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0035Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (31 / 16 : ℝ)
noncomputable def sUpper : ℝ := (2 / 1 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (63 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0035Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0036Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0036Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (15 / 8 : ℝ)
noncomputable def sUpper : ℝ := (31 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (61 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0036Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0037Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0037Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (29 / 16 : ℝ)
noncomputable def sUpper : ℝ := (15 / 8 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (59 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0037Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0038Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0038Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (7 / 4 : ℝ)
noncomputable def sUpper : ℝ := (29 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (57 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0038Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0039Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0039Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (27 / 16 : ℝ)
noncomputable def sUpper : ℝ := (7 / 4 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (55 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0039Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0040Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0040Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (13 / 8 : ℝ)
noncomputable def sUpper : ℝ := (27 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (53 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0040Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0041Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0041Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (25 / 16 : ℝ)
noncomputable def sUpper : ℝ := (13 / 8 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (51 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0041Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0042Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0042Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3 / 2 : ℝ)
noncomputable def sUpper : ℝ := (25 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (49 / 32 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0042Geometry

end


