-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001Geometry__22
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0001Geometry__22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:24:32.308525+00:00
-- url     : https://prove2.me/theorems/33e7dc7d-82f2-42ff-92fb-3a34f0c648db
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0001Geometry (+21 modules: GeneralCK.Certificates.E8TAxisProd0002Geometry, GeneralCK.Certificates.E8TAxisProd0003Geometry, G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0001Geometry (+21 modules: GeneralCK.Certificates.E8TAxisProd0002Geometry, GeneralCK.Certificates.E8TAxisProd0003Geometry, GeneralCK.Certificates.E8TAxisProd0004Geometry, GeneralCK.Certificates.E8TAxisProd0005Geometry, GeneralCK.Certificates.E8TAxisProd0006Geometry, GeneralCK.Certificates.E8TAxisProd0007Geometry, GeneralCK.Certificates.E8TAxisProd0008Geometry, GeneralCK.Certificates.E8TAxisProd0009Geometry, GeneralCK.Certificates.E8TAxisProd0010Geometry, GeneralCK.Certificates.E8TAxisProd0011Geometry, GeneralCK.Certificates.E8TAxisProd0012Geometry, GeneralCK.Certificates.E8TAxisProd0013Geometry, GeneralCK.Certificates.E8TAxisProd0014Geometry, GeneralCK.Certificates.E8TAxisProd0015Geometry, GeneralCK.Certificates.E8TAxisProd0016Geometry, GeneralCK.Certificates.E8TAxisProd0017Geometry, GeneralCK.Certificates.E8TAxisProd0018Geometry, GeneralCK.Certificates.E8TAxisProd0019Geometry, GeneralCK.Certificates.E8TAxisProd0020Geometry, GeneralCK.Certificates.E8TAxisProd0021Geometry, GeneralCK.Certificates.E8TAxisProd0022Geometry)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0001Geometry (+21 modules: GeneralCK.Certificates.E8TAxisProd0002Geometry, GeneralCK.Certificates.E8TAxisProd0003Geometry, GeneralCK.Certificates.E8TAxisProd0004Geometry, GeneralCK.Certificates.E8TAxisProd0005Geometry, GeneralCK.Certificates.E8TAxisProd0006Geometry, GeneralCK.Certificates.E8TAxisProd0007Geometry, GeneralCK.Certificates.E8TAxisProd0008Geometry, GeneralCK.Certificates.E8TAxisProd0009Geometry, GeneralCK.Certificates.E8TAxisProd0010Geometry, GeneralCK.Certificates.E8TAxisProd0011Geometry, GeneralCK.Certificates.E8TAxisProd0012Geometry, GeneralCK.Certificates.E8TAxisProd0013Geometry, GeneralCK.Certificates.E8TAxisProd0014Geometry, GeneralCK.Certificates.E8TAxisProd0015Geometry, GeneralCK.Certificates.E8TAxisProd0016Geometry, GeneralCK.Certificates.E8TAxisProd0017Geometry, GeneralCK.Certificates.E8TAxisProd0018Geometry, GeneralCK.Certificates.E8TAxisProd0019Geometry, GeneralCK.Certificates.E8TAxisProd0020Geometry, GeneralCK.Certificates.E8TAxisProd0021Geometry, GeneralCK.Certificates.E8TAxisProd0022Geometry)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0001Geometry (+21 modules: GeneralCK.Certificates.E8TAxisProd0002Geometry, GeneralCK.Certificates.E8TAxisProd0003Geometry, GeneralCK.Certificates.E8TAxisProd0004Geometry, GeneralCK.Certificates.E8TAxisProd0005Geometry, GeneralCK.Certificates.E8TAxisProd0006Geometry, GeneralCK.Certificates.E8TAxisProd0007Geometry, GeneralCK.Certificates.E8TAxisProd0008Geometry, GeneralCK.Certificates.E8TAxisProd0009Geometry, GeneralCK.Certificates.E8TAxisProd0010Geometry, GeneralCK.Certificates.E8TAxisProd0011Geometry, GeneralCK.Certificates.E8TAxisProd0012Geometry, GeneralCK.Certificates.E8TAxisProd0013Geometry, GeneralCK.Certificates.E8TAxisProd0014Geometry, GeneralCK.Certificates.E8TAxisProd0015Geometry, GeneralCK.Certificates.E8TAxisProd0016Geometry, GeneralCK.Certificates.E8TAxisProd0017Geometry, GeneralCK.Certificates.E8TAxisProd0018Geometry, GeneralCK.Certificates.E8TAxisProd0019Geometry, GeneralCK.Certificates.E8TAxisProd0020Geometry, GeneralCK.Certificates.E8TAxisProd0021Geometry, GeneralCK.Certificates.E8TAxisProd0022Geometry) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0001Geometry (+21 modules: GeneralCK/Certificates/E8TAxisProd0002Geometry, GeneralCK/Certificates/E8TAxisProd0003Geometry, GeneralCK/Certificates/E8TAxisProd0004Geometry, GeneralCK/Certificates/E8TAxisProd0005Geometry, GeneralCK/Certificates/E8TAxisProd0006Geometry, GeneralCK/Certificates/E8TAxisProd0007Geometry, GeneralCK/Certificates/E8TAxisProd0008Geometry, GeneralCK/Certificates/E8TAxisProd0009Geometry, GeneralCK/Certificates/E8TAxisProd0010Geometry, GeneralCK/Certificates/E8TAxisProd0011Geometry, GeneralCK/Certificates/E8TAxisProd0012Geometry, GeneralCK/Certificates/E8TAxisProd0013Geometry, GeneralCK/Certificates/E8TAxisProd0014Geometry, GeneralCK/Certificates/E8TAxisProd0015Geometry, GeneralCK/Certificates/E8TAxisProd0016Geometry, GeneralCK/Certificates/E8TAxisProd0017Geometry, GeneralCK/Certificates/E8TAxisProd0018Geometry, GeneralCK/Certificates/E8TAxisProd0019Geometry, GeneralCK/Certificates/E8TAxisProd0020Geometry, GeneralCK/Certificates/E8TAxisProd0021Geometry, GeneralCK/Certificates/E8TAxisProd0022Geometry).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema
import Definitions.Def_GeneralCK_E8_Prod0001_inputs

-- ===== source module GeneralCK.Certificates.E8TAxisProd0001Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0001Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel













theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0001Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0002Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0002Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (3 / 40 : ℝ)
noncomputable def sUpper : ℝ := (81250000000000000000000000000000000000000000000000000000011948189333493 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (156250000000000000000000000000000000000000000000000000000011948189333493 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0002Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0003Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0003Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (1 / 4 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (24062500000000000000000000000000000000000000000000000000000398272977783 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0003Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0004Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0004Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (22187500000000000000000000000000000000000000000000000000001194818933349 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0004Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0005Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0005Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (1 / 4 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24062500000000000000000000000000000000000000000000000000000398272977783 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0005Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0006Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0006Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (22187500000000000000000000000000000000000000000000000000001194818933349 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0006Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0007Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0007Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (13 / 64 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0007Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0008Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0008Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (18437499999999999999999999999999999999999999999999999999998805181066651 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0008Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0009Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0009Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (13 / 64 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0009Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0010Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0010Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (18437499999999999999999999999999999999999999999999999999998805181066651 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0010Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0011Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0011Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (1 / 4 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (24062500000000000000000000000000000000000000000000000000000398272977783 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0011Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0012Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0012Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (22187500000000000000000000000000000000000000000000000000001194818933349 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0012Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0013Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0013Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (13 / 64 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0013Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0014Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0014Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (18437499999999999999999999999999999999999999999999999999998805181066651 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999991785619833223 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0014Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0015Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0015Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5 / 32 : ℝ)
noncomputable def sUpper : ℝ := (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (16562499999999999999999999999999999999999999999999999999999601727022217 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0015Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0016Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0016Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5 / 32 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (14687500000000000000000000000000000000000000000000000000000398272977783 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0016Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0017Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0017Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (5 / 32 : ℝ)
noncomputable def sUpper : ℝ := (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (16562499999999999999999999999999999999999999999999999999999601727022217 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0017Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0018Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0018Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (5 / 32 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (14687500000000000000000000000000000000000000000000000000000398272977783 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0018Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0019Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0019Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (12812500000000000000000000000000000000000000000000000000001194818933349 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (34999999999999999999999999999999999999999999999999999999999601727022217 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0019Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0020Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0020Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 10 : ℝ)
noncomputable def sUpper : ℝ := (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (5468750000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (37500000000000000000000000000000000000000000000000000000001194818933349 / 2000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-13701577849977214858159545306715153309274367591, 13701577849977214858159545306715153309274367591⟩
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

end GeneralCK.Certificates.E8TAxisProd0020Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0021Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0021Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (1 / 10 : ℝ)
noncomputable def sUpper : ℝ := (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (5468750000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-13701577849977214858159545306715153309274367591, 13701577849977214858159545306715153309274367591⟩
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

end GeneralCK.Certificates.E8TAxisProd0021Geometry

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0022Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisProd0022Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (12812500000000000000000000000000000000000000000000000000001194818933349 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (124999999999999999999999999999999999999999999999999999999992532381666567 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
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

end GeneralCK.Certificates.E8TAxisProd0022Geometry

end


