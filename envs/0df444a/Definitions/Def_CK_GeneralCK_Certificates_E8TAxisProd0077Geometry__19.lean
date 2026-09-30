-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0077Geometry__19
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0077Geometry__19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:07:35.25922+00:00
-- url     : https://prove2.me/theorems/5f41caed-6150-4850-a28f-7dc71ee0a578
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0077Geometry (+18 modules: GeneralCK.Certificates.E8TAxisProd0078Geometry, GeneralCK.Certificates.E8TAxisProd0081Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0077Geometry (+18 modules: GeneralCK.Certificates.E8TAxisProd0078Geometry, GeneralCK.Certificates.E8TAxisProd0081Geometry, GeneralCK.Certificates.E8TAxisProd0082Geometry, GeneralCK.Certificates.E8TAxisProd0083Geometry, GeneralCK.Certificates.E8TAxisProd0084Geometry, GeneralCK.Certificates.E8TAxisProd0085Geometry, GeneralCK.Certificates.E8TAxisProd0086Geometry, GeneralCK.Certificates.E8TAxisProd0089Geometry, GeneralCK.Certificates.E8TAxisProd0090Geometry, GeneralCK.Certificates.E8TAxisProd0091Geometry, GeneralCK.Certificates.E8TAxisProd0092Geometry, GeneralCK.Certificates.E8TAxisProd0094Geometry, GeneralCK.Certificates.E8TAxisProd0095Geometry, GeneralCK.Certificates.E8TAxisProd0096Geometry, GeneralCK.Certificates.E8TAxisProd0097Geometry, GeneralCK.Certificates.E8TAxisProd0098Geometry, GeneralCK.Certificates.E8TAxisProd0099Geometry, GeneralCK.Certificates.E8TAxisProd0100Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0077Geometry (+18 modules: GeneralCK.Certificates.E8TAxisProd0078Geometry, GeneralCK.Certificates.E8TAxisProd0081Geometry, GeneralCK.Certificates.E8TAxisProd0082Geometry, GeneralCK.Certificates.E8TAxisProd0083Geometry, GeneralCK.Certificates.E8TAxisProd0084Geometry, GeneralCK.Certificates.E8TAxisProd0085Geometry, GeneralCK.Certificates.E8TAxisProd0086Geometry, GeneralCK.Certificates.E8TAxisProd0089Geometry, GeneralCK.Certificates.E8TAxisProd0090Geometry, GeneralCK.Certificates.E8TAxisProd0091Geometry, GeneralCK.Certificates.E8TAxisProd0092Geometry, GeneralCK.Certificates.E8TAxisProd0094Geometry, GeneralCK.Certificates.E8TAxisProd0095Geometry, GeneralCK.Certificates.E8TAxisProd0096Geometry, GeneralCK.Certificates.E8TAxisProd0097Geometry, GeneralCK.Certificates.E8TAxisProd0098Geometry, GeneralCK.Certificates.E8TAxisProd0099Geometry, GeneralCK.Certificates.E8TAxisProd0100Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0077Geometry (+18 modules: GeneralCK.Certificates.E8TAxisProd0078Geometry, GeneralCK.Certificates.E8TAxisProd0081Geometry, GeneralCK.Certificates.E8TAxisProd0082Geometry, GeneralCK.Certificates.E8TAxisProd0083Geometry, GeneralCK.Certificates.E8TAxisProd0084Geometry, GeneralCK.Certificates.E8TAxisProd0085Geometry, GeneralCK.Certificates.E8TAxisProd0086Geometry, GeneralCK.Certificates.E8TAxisProd0089Geometry, GeneralCK.Certificates.E8TAxisProd0090Geometry, GeneralCK.Certificates.E8TAxisProd0091Geometry, GeneralCK.Certificates.E8TAxisProd0092Geometry, GeneralCK.Certificates.E8TAxisProd0094Geometry, GeneralCK.Certificates.E8TAxisProd0095Geometry, GeneralCK.Certificates.E8TAxisProd0096Geometry, GeneralCK.Certificates.E8TAxisProd0097Geometry, GeneralCK.Certificates.E8TAxisProd0098Geometry, GeneralCK.Certificates.E8TAxisProd0099Geometry, GeneralCK.Certificates.E8TAxisProd0100Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0077Geometry (+18 modules: GeneralCK/Certificates/E8TAxisProd0078Geometry, GeneralCK/Certificates/E8TAxisProd0081Geometry, GeneralCK/Certificates/E8TAxisProd0082Geometry, GeneralCK/Certificates/E8TAxisProd0083Geometry, GeneralCK/Certificates/E8TAxisProd0084Geometry, GeneralCK/Certificates/E8TAxisProd0085Geometry, GeneralCK/Certificates/E8TAxisProd0086Geometry, GeneralCK/Certificates/E8TAxisProd0089Geometry, GeneralCK/Certificates/E8TAxisProd0090Geometry, GeneralCK/Certificates/E8TAxisProd0091Geometry, GeneralCK/Certificates/E8TAxisProd0092Geometry, GeneralCK/Certificates/E8TAxisProd0094Geometry, GeneralCK/Certificates/E8TAxisProd0095Geometry, GeneralCK/Certificates/E8TAxisProd0096Geometry, GeneralCK/Certificates/E8TAxisProd0097Geometry, GeneralCK/Certificates/E8TAxisProd0098Geometry, GeneralCK/Certificates/E8TAxisProd0099Geometry, GeneralCK/Certificates/E8TAxisProd0100Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisProd0077Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0077Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (17 / 32 : ℝ)
noncomputable def sUpper : ℝ := (9 / 16 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (35 / 64 : ℝ)
noncomputable def centerT : ℝ := (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0077Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0078Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0078Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 2 : ℝ)
noncomputable def sUpper : ℝ := (17 / 32 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (33 / 64 : ℝ)
noncomputable def centerT : ℝ := (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0078Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0081Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0081Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (17 / 32 : ℝ)
noncomputable def sUpper : ℝ := (9 / 16 : ℝ)
noncomputable def tLower : ℝ := (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (35 / 64 : ℝ)
noncomputable def centerT : ℝ := (27499999999999999999999999999999999999999999999999999999997610362133301 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0081Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0082Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0082Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 2 : ℝ)
noncomputable def sUpper : ℝ := (17 / 32 : ℝ)
noncomputable def tLower : ℝ := (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (33 / 64 : ℝ)
noncomputable def centerT : ℝ := (27499999999999999999999999999999999999999999999999999999997610362133301 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0082Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0083Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0083Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (17 / 32 : ℝ)
noncomputable def sUpper : ℝ := (9 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (35 / 64 : ℝ)
noncomputable def centerT : ℝ := (56249999999999999999999999999999999999999999999999999999992283461055451 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0083Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0084Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0084Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 2 : ℝ)
noncomputable def sUpper : ℝ := (17 / 32 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (33 / 64 : ℝ)
noncomputable def centerT : ℝ := (56249999999999999999999999999999999999999999999999999999992283461055451 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0084Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0085Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0085Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11 / 16 : ℝ)
noncomputable def sUpper : ℝ := (3 / 4 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23 / 32 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0085Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0086Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0086Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5 / 8 : ℝ)
noncomputable def sUpper : ℝ := (11 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (21 / 32 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0086Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0089Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0089Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (17 / 32 : ℝ)
noncomputable def sUpper : ℝ := (9 / 16 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (35 / 64 : ℝ)
noncomputable def centerT : ℝ := (5468749999999999999999999999999999999999999999999999999999595504006939 / 625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0089Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0090Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0090Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 2 : ℝ)
noncomputable def sUpper : ℝ := (17 / 32 : ℝ)
noncomputable def tLower : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (33 / 64 : ℝ)
noncomputable def centerT : ℝ := (5468749999999999999999999999999999999999999999999999999999595504006939 / 625000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0090Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0091Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0091Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (17 / 32 : ℝ)
noncomputable def sUpper : ℝ := (9 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (35 / 64 : ℝ)
noncomputable def centerT : ℝ := (62499999999999999999999999999999999999999999999999999999996266190833283 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0091Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0092Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0092Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 2 : ℝ)
noncomputable def sUpper : ℝ := (17 / 32 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (33 / 64 : ℝ)
noncomputable def centerT : ℝ := (62499999999999999999999999999999999999999999999999999999996266190833283 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0092Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0094Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0094Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (17 / 32 : ℝ)
noncomputable def sUpper : ℝ := (9 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (35 / 64 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0094Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0095Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0095Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 2 : ℝ)
noncomputable def sUpper : ℝ := (17 / 32 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (33 / 64 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 20000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0095Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0096Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0096Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (31 / 16 : ℝ)
noncomputable def sUpper : ℝ := 2
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (63 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0096Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0097Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0097Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (15 / 8 : ℝ)
noncomputable def sUpper : ℝ := (31 / 16 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (61 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0097Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0098Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0098Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (31 / 16 : ℝ)
noncomputable def sUpper : ℝ := 2
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (63 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0098Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0099Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0099Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (15 / 8 : ℝ)
noncomputable def sUpper : ℝ := (31 / 16 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (61 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0099Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0100Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0100Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (29 / 16 : ℝ)
noncomputable def sUpper : ℝ := (15 / 8 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (59 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0100Geometry

end


