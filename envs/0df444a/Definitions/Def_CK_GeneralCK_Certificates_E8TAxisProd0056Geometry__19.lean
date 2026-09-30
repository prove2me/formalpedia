-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0056Geometry__19
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0056Geometry__19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T02:30:30.652036+00:00
-- url     : https://prove2.me/theorems/997e29e1-63b5-474e-9a96-c99824100ad3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0056Geometry (+18 modules: GeneralCK.Certificates.E8TAxisProd0057Geometry, GeneralCK.Certificates.E8TAxisProd0058Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0056Geometry (+18 modules: GeneralCK.Certificates.E8TAxisProd0057Geometry, GeneralCK.Certificates.E8TAxisProd0058Geometry, GeneralCK.Certificates.E8TAxisProd0059Geometry, GeneralCK.Certificates.E8TAxisProd0060Geometry, GeneralCK.Certificates.E8TAxisProd0061Geometry, GeneralCK.Certificates.E8TAxisProd0062Geometry, GeneralCK.Certificates.E8TAxisProd0063Geometry, GeneralCK.Certificates.E8TAxisProd0064Geometry, GeneralCK.Certificates.E8TAxisProd0065Geometry, GeneralCK.Certificates.E8TAxisProd0066Geometry, GeneralCK.Certificates.E8TAxisProd0067Geometry, GeneralCK.Certificates.E8TAxisProd0068Geometry, GeneralCK.Certificates.E8TAxisProd0069Geometry, GeneralCK.Certificates.E8TAxisProd0070Geometry, GeneralCK.Certificates.E8TAxisProd0071Geometry, GeneralCK.Certificates.E8TAxisProd0072Geometry, GeneralCK.Certificates.E8TAxisProd0075Geometry, GeneralCK.Certificates.E8TAxisProd0076Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0056Geometry (+18 modules: GeneralCK.Certificates.E8TAxisProd0057Geometry, GeneralCK.Certificates.E8TAxisProd0058Geometry, GeneralCK.Certificates.E8TAxisProd0059Geometry, GeneralCK.Certificates.E8TAxisProd0060Geometry, GeneralCK.Certificates.E8TAxisProd0061Geometry, GeneralCK.Certificates.E8TAxisProd0062Geometry, GeneralCK.Certificates.E8TAxisProd0063Geometry, GeneralCK.Certificates.E8TAxisProd0064Geometry, GeneralCK.Certificates.E8TAxisProd0065Geometry, GeneralCK.Certificates.E8TAxisProd0066Geometry, GeneralCK.Certificates.E8TAxisProd0067Geometry, GeneralCK.Certificates.E8TAxisProd0068Geometry, GeneralCK.Certificates.E8TAxisProd0069Geometry, GeneralCK.Certificates.E8TAxisProd0070Geometry, GeneralCK.Certificates.E8TAxisProd0071Geometry, GeneralCK.Certificates.E8TAxisProd0072Geometry, GeneralCK.Certificates.E8TAxisProd0075Geometry, GeneralCK.Certificates.E8TAxisProd0076Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0056Geometry (+18 modules: GeneralCK.Certificates.E8TAxisProd0057Geometry, GeneralCK.Certificates.E8TAxisProd0058Geometry, GeneralCK.Certificates.E8TAxisProd0059Geometry, GeneralCK.Certificates.E8TAxisProd0060Geometry, GeneralCK.Certificates.E8TAxisProd0061Geometry, GeneralCK.Certificates.E8TAxisProd0062Geometry, GeneralCK.Certificates.E8TAxisProd0063Geometry, GeneralCK.Certificates.E8TAxisProd0064Geometry, GeneralCK.Certificates.E8TAxisProd0065Geometry, GeneralCK.Certificates.E8TAxisProd0066Geometry, GeneralCK.Certificates.E8TAxisProd0067Geometry, GeneralCK.Certificates.E8TAxisProd0068Geometry, GeneralCK.Certificates.E8TAxisProd0069Geometry, GeneralCK.Certificates.E8TAxisProd0070Geometry, GeneralCK.Certificates.E8TAxisProd0071Geometry, GeneralCK.Certificates.E8TAxisProd0072Geometry, GeneralCK.Certificates.E8TAxisProd0075Geometry, GeneralCK.Certificates.E8TAxisProd0076Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0056Geometry (+18 modules: GeneralCK/Certificates/E8TAxisProd0057Geometry, GeneralCK/Certificates/E8TAxisProd0058Geometry, GeneralCK/Certificates/E8TAxisProd0059Geometry, GeneralCK/Certificates/E8TAxisProd0060Geometry, GeneralCK/Certificates/E8TAxisProd0061Geometry, GeneralCK/Certificates/E8TAxisProd0062Geometry, GeneralCK/Certificates/E8TAxisProd0063Geometry, GeneralCK/Certificates/E8TAxisProd0064Geometry, GeneralCK/Certificates/E8TAxisProd0065Geometry, GeneralCK/Certificates/E8TAxisProd0066Geometry, GeneralCK/Certificates/E8TAxisProd0067Geometry, GeneralCK/Certificates/E8TAxisProd0068Geometry, GeneralCK/Certificates/E8TAxisProd0069Geometry, GeneralCK/Certificates/E8TAxisProd0070Geometry, GeneralCK/Certificates/E8TAxisProd0071Geometry, GeneralCK/Certificates/E8TAxisProd0072Geometry, GeneralCK/Certificates/E8TAxisProd0075Geometry, GeneralCK/Certificates/E8TAxisProd0076Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisProd0056Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0056Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 4 : ℝ)
noncomputable def sUpper : ℝ := (9 / 32 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (17 / 64 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0056Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0057Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0057Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (15 / 16 : ℝ)
noncomputable def sUpper : ℝ := 1
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (31 / 32 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0057Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0058Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0058Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (7 / 8 : ℝ)
noncomputable def sUpper : ℝ := (15 / 16 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (29 / 32 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0058Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0059Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0059Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (15 / 16 : ℝ)
noncomputable def sUpper : ℝ := 1
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (31 / 32 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0059Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0060Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0060Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (7 / 8 : ℝ)
noncomputable def sUpper : ℝ := (15 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (29 / 32 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0060Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0061Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0061Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13 / 16 : ℝ)
noncomputable def sUpper : ℝ := (7 / 8 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (27 / 32 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0061Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0062Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0062Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3 / 4 : ℝ)
noncomputable def sUpper : ℝ := (13 / 16 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (25 / 32 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0062Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0063Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0063Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13 / 16 : ℝ)
noncomputable def sUpper : ℝ := (7 / 8 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27 / 32 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0063Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0064Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0064Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3 / 4 : ℝ)
noncomputable def sUpper : ℝ := (13 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (25 / 32 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0064Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0065Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0065Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (15 / 16 : ℝ)
noncomputable def sUpper : ℝ := 1
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (31 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0065Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0066Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0066Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (7 / 8 : ℝ)
noncomputable def sUpper : ℝ := (15 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (29 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0066Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0067Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0067Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (13 / 16 : ℝ)
noncomputable def sUpper : ℝ := (7 / 8 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (27 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0067Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0068Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0068Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3 / 4 : ℝ)
noncomputable def sUpper : ℝ := (13 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (25 / 32 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0068Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0069Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0069Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11 / 16 : ℝ)
noncomputable def sUpper : ℝ := (3 / 4 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (23 / 32 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0069Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0070Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0070Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5 / 8 : ℝ)
noncomputable def sUpper : ℝ := (11 / 16 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (21 / 32 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0070Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0071Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0071Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11 / 16 : ℝ)
noncomputable def sUpper : ℝ := (3 / 4 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (23 / 32 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0071Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0072Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0072Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5 / 8 : ℝ)
noncomputable def sUpper : ℝ := (11 / 16 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (21 / 32 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0072Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0075Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0075Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (17 / 32 : ℝ)
noncomputable def sUpper : ℝ := (9 / 16 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (35 / 64 : ℝ)
noncomputable def centerT : ℝ := (37500000000000000000000000000000000000000000000000000000001194818933349 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0075Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0076Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0076Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 2 : ℝ)
noncomputable def sUpper : ℝ := (17 / 32 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (33 / 64 : ℝ)
noncomputable def centerT : ℝ := (37500000000000000000000000000000000000000000000000000000001194818933349 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0076Geometry

end


