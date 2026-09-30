-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000Geometry__22
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0000Geometry__22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:24:42.759565+00:00
-- url     : https://prove2.me/theorems/1599d3e1-d924-4905-aa09-27ce723f3bbb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0000Geometry (+21 modules: GeneralCK.Certificates.E8TAxisZero0001Geometry, GeneralCK.Certificates.E8TAxisZero0002Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0000Geometry (+21 modules: GeneralCK.Certificates.E8TAxisZero0001Geometry, GeneralCK.Certificates.E8TAxisZero0002Geometry, GeneralCK.Certificates.E8TAxisZero0003Geometry, GeneralCK.Certificates.E8TAxisZero0004Geometry, GeneralCK.Certificates.E8TAxisZero0005Geometry, GeneralCK.Certificates.E8TAxisZero0006Geometry, GeneralCK.Certificates.E8TAxisZero0007Geometry, GeneralCK.Certificates.E8TAxisZero0008Geometry, GeneralCK.Certificates.E8TAxisZero0009Geometry, GeneralCK.Certificates.E8TAxisZero0010Geometry, GeneralCK.Certificates.E8TAxisZero0011Geometry, GeneralCK.Certificates.E8TAxisZero0012Geometry, GeneralCK.Certificates.E8TAxisZero0013Geometry, GeneralCK.Certificates.E8TAxisZero0015Geometry, GeneralCK.Certificates.E8TAxisZero0016Geometry, GeneralCK.Certificates.E8TAxisZero0017Geometry, GeneralCK.Certificates.E8TAxisZero0018Geometry, GeneralCK.Certificates.E8TAxisZero0019Geometry, GeneralCK.Certificates.E8TAxisZero0020Geometry, GeneralCK.Certificates.E8TAxisZero0021Geometry, GeneralCK.Certificates.E8TAxisZero0022Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0000Geometry (+21 modules: GeneralCK.Certificates.E8TAxisZero0001Geometry, GeneralCK.Certificates.E8TAxisZero0002Geometry, GeneralCK.Certificates.E8TAxisZero0003Geometry, GeneralCK.Certificates.E8TAxisZero0004Geometry, GeneralCK.Certificates.E8TAxisZero0005Geometry, GeneralCK.Certificates.E8TAxisZero0006Geometry, GeneralCK.Certificates.E8TAxisZero0007Geometry, GeneralCK.Certificates.E8TAxisZero0008Geometry, GeneralCK.Certificates.E8TAxisZero0009Geometry, GeneralCK.Certificates.E8TAxisZero0010Geometry, GeneralCK.Certificates.E8TAxisZero0011Geometry, GeneralCK.Certificates.E8TAxisZero0012Geometry, GeneralCK.Certificates.E8TAxisZero0013Geometry, GeneralCK.Certificates.E8TAxisZero0015Geometry, GeneralCK.Certificates.E8TAxisZero0016Geometry, GeneralCK.Certificates.E8TAxisZero0017Geometry, GeneralCK.Certificates.E8TAxisZero0018Geometry, GeneralCK.Certificates.E8TAxisZero0019Geometry, GeneralCK.Certificates.E8TAxisZero0020Geometry, GeneralCK.Certificates.E8TAxisZero0021Geometry, GeneralCK.Certificates.E8TAxisZero0022Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0000Geometry (+21 modules: GeneralCK.Certificates.E8TAxisZero0001Geometry, GeneralCK.Certificates.E8TAxisZero0002Geometry, GeneralCK.Certificates.E8TAxisZero0003Geometry, GeneralCK.Certificates.E8TAxisZero0004Geometry, GeneralCK.Certificates.E8TAxisZero0005Geometry, GeneralCK.Certificates.E8TAxisZero0006Geometry, GeneralCK.Certificates.E8TAxisZero0007Geometry, GeneralCK.Certificates.E8TAxisZero0008Geometry, GeneralCK.Certificates.E8TAxisZero0009Geometry, GeneralCK.Certificates.E8TAxisZero0010Geometry, GeneralCK.Certificates.E8TAxisZero0011Geometry, GeneralCK.Certificates.E8TAxisZero0012Geometry, GeneralCK.Certificates.E8TAxisZero0013Geometry, GeneralCK.Certificates.E8TAxisZero0015Geometry, GeneralCK.Certificates.E8TAxisZero0016Geometry, GeneralCK.Certificates.E8TAxisZero0017Geometry, GeneralCK.Certificates.E8TAxisZero0018Geometry, GeneralCK.Certificates.E8TAxisZero0019Geometry, GeneralCK.Certificates.E8TAxisZero0020Geometry, GeneralCK.Certificates.E8TAxisZero0021Geometry, GeneralCK.Certificates.E8TAxisZero0022Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0000Geometry (+21 modules: GeneralCK/Certificates/E8TAxisZero0001Geometry, GeneralCK/Certificates/E8TAxisZero0002Geometry, GeneralCK/Certificates/E8TAxisZero0003Geometry, GeneralCK/Certificates/E8TAxisZero0004Geometry, GeneralCK/Certificates/E8TAxisZero0005Geometry, GeneralCK/Certificates/E8TAxisZero0006Geometry, GeneralCK/Certificates/E8TAxisZero0007Geometry, GeneralCK/Certificates/E8TAxisZero0008Geometry, GeneralCK/Certificates/E8TAxisZero0009Geometry, GeneralCK/Certificates/E8TAxisZero0010Geometry, GeneralCK/Certificates/E8TAxisZero0011Geometry, GeneralCK/Certificates/E8TAxisZero0012Geometry, GeneralCK/Certificates/E8TAxisZero0013Geometry, GeneralCK/Certificates/E8TAxisZero0015Geometry, GeneralCK/Certificates/E8TAxisZero0016Geometry, GeneralCK/Certificates/E8TAxisZero0017Geometry, GeneralCK/Certificates/E8TAxisZero0018Geometry, GeneralCK/Certificates/E8TAxisZero0019Geometry, GeneralCK/Certificates/E8TAxisZero0020Geometry, GeneralCK/Certificates/E8TAxisZero0021Geometry, GeneralCK/Certificates/E8TAxisZero0022Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisZero0000Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0000Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (17812500000000000000000000000000000000000000000000000000001393955422241 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3 / 40 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (36562500000000000000000000000000000000000000000000000000001393955422241 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-2740315569995442971631909061343030661854873519, 2740315569995442971631909061343030661854873519⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

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
end GeneralCK.Certificates.E8TAxisZero0000Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0001Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0001Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (13500000000000000000000000000000000000000000000000000000000637236764453 / 200000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (17812500000000000000000000000000000000000000000000000000001393955422241 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (138750000000000000000000000000000000000000000000000000000008762005511229 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-2740315569995442971631909061343030661854873519, 2740315569995442971631909061343030661854873519⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

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
end GeneralCK.Certificates.E8TAxisZero0001Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0002Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0002Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (31875000000000000000000000000000000000000000000000000000000398272977783 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (13500000000000000000000000000000000000000000000000000000000637236764453 / 200000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (131250000000000000000000000000000000000000000000000000000003982729777831 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-2740315569995442971631909061343030661854873519, 2740315569995442971631909061343030661854873519⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

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
end GeneralCK.Certificates.E8TAxisZero0002Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0003Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0003Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3 / 50 : ℝ)
noncomputable def sUpper : ℝ := (31875000000000000000000000000000000000000000000000000000000398272977783 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (61875000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-2740315569995442971631909061343030661854873519, 2740315569995442971631909061343030661854873519⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

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
end GeneralCK.Certificates.E8TAxisZero0003Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0004Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0004Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3 / 32 : ℝ)
noncomputable def sUpper : ℝ := (1 / 10 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (31 / 320 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-4567192616659071619386515102238384436424789197, 4567192616659071619386515102238384436424789197⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

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
end GeneralCK.Certificates.E8TAxisZero0004Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0005Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0005Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3500000000000000000000000000000000000000000000000000000000637236764453 / 40000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3 / 32 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (7250000000000000000000000000000000000000000000000000000000637236764453 / 80000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-4567192616659071619386515102238384436424789197, 4567192616659071619386515102238384436424789197⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

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
end GeneralCK.Certificates.E8TAxisZero0005Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0006Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0006Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (81250000000000000000000000000000000000000000000000000000011948189333493 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3500000000000000000000000000000000000000000000000000000000637236764453 / 40000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (84375000000000000000000000000000000000000000000000000000013939554222409 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-4567192616659071619386515102238384436424789197, 4567192616659071619386515102238384436424789197⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

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
end GeneralCK.Certificates.E8TAxisZero0006Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0007Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0007Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3 / 40 : ℝ)
noncomputable def sUpper : ℝ := (81250000000000000000000000000000000000000000000000000000011948189333493 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (156250000000000000000000000000000000000000000000000000000011948189333493 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-4567192616659071619386515102238384436424789197, 4567192616659071619386515102238384436424789197⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

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
end GeneralCK.Certificates.E8TAxisZero0007Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0008Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0008Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (1 / 4 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24062500000000000000000000000000000000000000000000000000000398272977783 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-13701577849977214858159545306715153309274367591, 13701577849977214858159545306715153309274367591⟩
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
end GeneralCK.Certificates.E8TAxisZero0008Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0009Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0009Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (22187500000000000000000000000000000000000000000000000000001194818933349 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-13701577849977214858159545306715153309274367591, 13701577849977214858159545306715153309274367591⟩
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
end GeneralCK.Certificates.E8TAxisZero0009Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0010Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0010Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (13 / 64 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-13701577849977214858159545306715153309274367591, 13701577849977214858159545306715153309274367591⟩
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
end GeneralCK.Certificates.E8TAxisZero0010Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0011Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0011Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (18437499999999999999999999999999999999999999999999999999998805181066651 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-13701577849977214858159545306715153309274367591, 13701577849977214858159545306715153309274367591⟩
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
end GeneralCK.Certificates.E8TAxisZero0011Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0012Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0012Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (5 / 32 : ℝ)
noncomputable def sUpper : ℝ := (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (16562499999999999999999999999999999999999999999999999999999601727022217 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-13701577849977214858159545306715153309274367591, 13701577849977214858159545306715153309274367591⟩
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
end GeneralCK.Certificates.E8TAxisZero0012Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0013Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0013Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5 / 32 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (14687500000000000000000000000000000000000000000000000000000398272977783 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-13701577849977214858159545306715153309274367591, 13701577849977214858159545306715153309274367591⟩
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
end GeneralCK.Certificates.E8TAxisZero0013Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0015Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0015Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (7 / 64 : ℝ)
noncomputable def sUpper : ℝ := (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (5703125000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-6850788924988607429079772653357576654637183796, 6850788924988607429079772653357576654637183796⟩
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
end GeneralCK.Certificates.E8TAxisZero0015Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0016Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0016Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (1 / 10 : ℝ)
noncomputable def sUpper : ℝ := (7 / 64 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (67 / 640 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-6850788924988607429079772653357576654637183796, 6850788924988607429079772653357576654637183796⟩
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
end GeneralCK.Certificates.E8TAxisZero0016Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0017Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0017Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (15 / 32 : ℝ)
noncomputable def sUpper : ℝ := (1 / 2 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (31 / 64 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0017Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0018Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0018Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (7 / 16 : ℝ)
noncomputable def sUpper : ℝ := (15 / 32 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (29 / 64 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0018Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0019Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0019Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (13 / 32 : ℝ)
noncomputable def sUpper : ℝ := (7 / 16 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27 / 64 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0019Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0020Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0020Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3 / 8 : ℝ)
noncomputable def sUpper : ℝ := (13 / 32 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (25 / 64 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0020Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0021Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0021Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (11 / 32 : ℝ)
noncomputable def sUpper : ℝ := (3 / 8 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23 / 64 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0021Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0022Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0022Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (5 / 16 : ℝ)
noncomputable def sUpper : ℝ := (11 / 32 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (21 / 64 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0022Geometry

end


