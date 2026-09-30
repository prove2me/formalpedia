-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0068Geometry__15
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0068Geometry__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:17:58.946308+00:00
-- url     : https://prove2.me/theorems/43867cd9-8c6e-4a4b-a6c4-ab5ab5c706ab
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0068Geometry (+14 modules: GeneralCK.Certificates.E8TAxisZero0069Geometry, GeneralCK.Certificates.E8TAxisZero0070Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0068Geometry (+14 modules: GeneralCK.Certificates.E8TAxisZero0069Geometry, GeneralCK.Certificates.E8TAxisZero0070Geometry, GeneralCK.Certificates.E8TAxisZero0071Geometry, GeneralCK.Certificates.E8TAxisZero0072Geometry, GeneralCK.Certificates.E8TAxisZero0073Geometry, GeneralCK.Certificates.E8TAxisZero0074Geometry, GeneralCK.Certificates.E8TAxisZero0075Geometry, GeneralCK.Certificates.E8TAxisZero0076Geometry, GeneralCK.Certificates.E8TAxisZero0077Geometry, GeneralCK.Certificates.E8TAxisZero0078Geometry, GeneralCK.Certificates.E8TAxisZero0079Geometry, GeneralCK.Certificates.E8TAxisZero0080Geometry, GeneralCK.Certificates.E8TAxisZero0081Geometry, GeneralCK.Certificates.E8TAxisZero0082Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0068Geometry (+14 modules: GeneralCK.Certificates.E8TAxisZero0069Geometry, GeneralCK.Certificates.E8TAxisZero0070Geometry, GeneralCK.Certificates.E8TAxisZero0071Geometry, GeneralCK.Certificates.E8TAxisZero0072Geometry, GeneralCK.Certificates.E8TAxisZero0073Geometry, GeneralCK.Certificates.E8TAxisZero0074Geometry, GeneralCK.Certificates.E8TAxisZero0075Geometry, GeneralCK.Certificates.E8TAxisZero0076Geometry, GeneralCK.Certificates.E8TAxisZero0077Geometry, GeneralCK.Certificates.E8TAxisZero0078Geometry, GeneralCK.Certificates.E8TAxisZero0079Geometry, GeneralCK.Certificates.E8TAxisZero0080Geometry, GeneralCK.Certificates.E8TAxisZero0081Geometry, GeneralCK.Certificates.E8TAxisZero0082Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0068Geometry (+14 modules: GeneralCK.Certificates.E8TAxisZero0069Geometry, GeneralCK.Certificates.E8TAxisZero0070Geometry, GeneralCK.Certificates.E8TAxisZero0071Geometry, GeneralCK.Certificates.E8TAxisZero0072Geometry, GeneralCK.Certificates.E8TAxisZero0073Geometry, GeneralCK.Certificates.E8TAxisZero0074Geometry, GeneralCK.Certificates.E8TAxisZero0075Geometry, GeneralCK.Certificates.E8TAxisZero0076Geometry, GeneralCK.Certificates.E8TAxisZero0077Geometry, GeneralCK.Certificates.E8TAxisZero0078Geometry, GeneralCK.Certificates.E8TAxisZero0079Geometry, GeneralCK.Certificates.E8TAxisZero0080Geometry, GeneralCK.Certificates.E8TAxisZero0081Geometry, GeneralCK.Certificates.E8TAxisZero0082Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0068Geometry (+14 modules: GeneralCK/Certificates/E8TAxisZero0069Geometry, GeneralCK/Certificates/E8TAxisZero0070Geometry, GeneralCK/Certificates/E8TAxisZero0071Geometry, GeneralCK/Certificates/E8TAxisZero0072Geometry, GeneralCK/Certificates/E8TAxisZero0073Geometry, GeneralCK/Certificates/E8TAxisZero0074Geometry, GeneralCK/Certificates/E8TAxisZero0075Geometry, GeneralCK/Certificates/E8TAxisZero0076Geometry, GeneralCK/Certificates/E8TAxisZero0077Geometry, GeneralCK/Certificates/E8TAxisZero0078Geometry, GeneralCK/Certificates/E8TAxisZero0079Geometry, GeneralCK/Certificates/E8TAxisZero0080Geometry, GeneralCK/Certificates/E8TAxisZero0081Geometry, GeneralCK/Certificates/E8TAxisZero0082Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisZero0068Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0068Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (325 / 128 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (6302734375000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0068Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0069Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0069Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3128906250000000000000000000000000000000000000000000000000637236764453 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24851562500000000000000000000000000000000000000000000000004460657351171 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0069Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0070Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0070Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (12335937500000000000000000000000000000000000000000000000001911710293359 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (4898437500000000000000000000000000000000000000000000000000637236764453 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0070Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0071Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0071Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6078125000000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24132812500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0071Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0072Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0072Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (151 / 64 : ℝ)
noncomputable def sUpper : ℝ := (11976562500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23773437500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0072Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0073Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0073Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (151 / 64 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23414062499999999999999999999999999999999999999999999999999362763235547 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0073Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0074Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0074Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23054687499999999999999999999999999999999999999999999999998088289706641 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0074Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0075Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0075Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (4539062499999999999999999999999999999999999999999999999999362763235547 / 2000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0075Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0076Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0076Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (22335937499999999999999999999999999999999999999999999999995539342648829 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0076Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0077Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0077Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (279 / 128 : ℝ)
noncomputable def sUpper : ℝ := (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (5494140624999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0077Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0078Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0078Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (279 / 128 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (21617187499999999999999999999999999999999999999999999999999362763235547 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0078Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0079Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0079Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (21257812499999999999999999999999999999999999999999999999998088289706641 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0079Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0080Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0080Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (535 / 256 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0080Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0081Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0081Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (20539062500000000000000000000000000000000000000000000000001911710293359 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0081Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0082Geometry =====
section
namespace GeneralCK.Certificates.E8TAxisZero0082Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (2 / 1 : ℝ)
noncomputable def sUpper : ℝ := (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (20179687500000000000000000000000000000000000000000000000000637236764453 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (12499999999999999999999999999999999999999999999999999999998630936638871 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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
end GeneralCK.Certificates.E8TAxisZero0082Geometry

end


