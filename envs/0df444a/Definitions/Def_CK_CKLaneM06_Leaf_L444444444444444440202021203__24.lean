-- Prove2me | Definitions.Def_CK_CKLaneM06_Leaf_L444444444444444440202021203__24
-- name    : CK_CKLaneM06_Leaf_L444444444444444440202021203__24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T00:39:07.936891+00:00
-- url     : https://prove2.me/theorems/0f8e8ee6-e18e-40ce-88d2-1ff741f6055c
-- title:
--   Courtade–Kumar proof module `CKLaneM06.Leaf.L444444444444444440202021203 (+23 modules: CKLaneM06.Leaf.L444444444444444440202021213, CKLaneM06.Leaf.L444444444444444440202120203, CKLaneM06.…
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.Leaf.L444444444444444440202021203 (+23 modules: CKLaneM06.Leaf.L444444444444444440202021213, CKLaneM06.Leaf.L444444444444444440202120203, CKLaneM06.Leaf.L4444444444444444402021203, CKLaneM06.Leaf.L4444444444444444402021213, CKLaneM06.Leaf.L4444444444444444402120203, CKLaneM06.Leaf.L4444444444444444402120213, CKLaneM06.Leaf.L44444444444444444021203, CKLaneM06.Leaf.L4444444444444444402121203, CKLaneM06.Leaf.L44444444444444444021213, CKLaneM06.Leaf.L444444444444444440213, CKLaneM06.Leaf.L44444444444444444031, CKLaneM06.Leaf.L44444444444444444120203, CKLaneM06.Leaf.L44444444444444444120213, CKLaneM06.Leaf.L444444444444444441203, CKLaneM06.Leaf.L44444444444444444121203, CKLaneM06.Leaf.L444444444444444441213, CKLaneM06.Leaf.L4444444444444444413, CKLaneM06.Leaf.L444444444444444450300012, CKLaneM06.Leaf.L444444444444444450300013, CKLaneM06.Leaf.L4444444444444444513, CKLaneM06.Leaf.L444444444444444503000142, CKLaneM06.Leaf.L444444444444444503000143, CKLaneM06.Leaf.L444444444444444503000153)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.Leaf.L444444444444444440202021203 (+23 modules: CKLaneM06.Leaf.L444444444444444440202021213, CKLaneM06.Leaf.L444444444444444440202120203, CKLaneM06.Leaf.L4444444444444444402021203, CKLaneM06.Leaf.L4444444444444444402021213, CKLaneM06.Leaf.L4444444444444444402120203, CKLaneM06.Leaf.L4444444444444444402120213, CKLaneM06.Leaf.L44444444444444444021203, CKLaneM06.Leaf.L4444444444444444402121203, CKLaneM06.Leaf.L44444444444444444021213, CKLaneM06.Leaf.L444444444444444440213, CKLaneM06.Leaf.L44444444444444444031, CKLaneM06.Leaf.L44444444444444444120203, CKLaneM06.Leaf.L44444444444444444120213, CKLaneM06.Leaf.L444444444444444441203, CKLaneM06.Leaf.L44444444444444444121203, CKLaneM06.Leaf.L444444444444444441213, CKLaneM06.Leaf.L4444444444444444413, CKLaneM06.Leaf.L444444444444444450300012, CKLaneM06.Leaf.L444444444444444450300013, CKLaneM06.Leaf.L4444444444444444513, CKLaneM06.Leaf.L444444444444444503000142, CKLaneM06.Leaf.L444444444444444503000143, CKLaneM06.Leaf.L444444444444444503000153)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.Leaf.L444444444444444440202021203 (+23 modules: CKLaneM06.Leaf.L444444444444444440202021213, CKLaneM06.Leaf.L444444444444444440202120203, CKLaneM06.Leaf.L4444444444444444402021203, CKLaneM06.Leaf.L4444444444444444402021213, CKLaneM06.Leaf.L4444444444444444402120203, CKLaneM06.Leaf.L4444444444444444402120213, CKLaneM06.Leaf.L44444444444444444021203, CKLaneM06.Leaf.L4444444444444444402121203, CKLaneM06.Leaf.L44444444444444444021213, CKLaneM06.Leaf.L444444444444444440213, CKLaneM06.Leaf.L44444444444444444031, CKLaneM06.Leaf.L44444444444444444120203, CKLaneM06.Leaf.L44444444444444444120213, CKLaneM06.Leaf.L444444444444444441203, CKLaneM06.Leaf.L44444444444444444121203, CKLaneM06.Leaf.L444444444444444441213, CKLaneM06.Leaf.L4444444444444444413, CKLaneM06.Leaf.L444444444444444450300012, CKLaneM06.Leaf.L444444444444444450300013, CKLaneM06.Leaf.L4444444444444444513, CKLaneM06.Leaf.L444444444444444503000142, CKLaneM06.Leaf.L444444444444444503000143, CKLaneM06.Leaf.L444444444444444503000153) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/Leaf/L444444444444444440202021203 (+23 modules: CKLaneM06/Leaf/L444444444444444440202021213, CKLaneM06/Leaf/L444444444444444440202120203, CKLaneM06/Leaf/L4444444444444444402021203, CKLaneM06/Leaf/L4444444444444444402021213, CKLaneM06/Leaf/L4444444444444444402120203, CKLaneM06/Leaf/L4444444444444444402120213, CKLaneM06/Leaf/L44444444444444444021203, CKLaneM06/Leaf/L4444444444444444402121203, CKLaneM06/Leaf/L44444444444444444021213, CKLaneM06/Leaf/L444444444444444440213, CKLaneM06/Leaf/L44444444444444444031, CKLaneM06/Leaf/L44444444444444444120203, CKLaneM06/Leaf/L44444444444444444120213, CKLaneM06/Leaf/L444444444444444441203, CKLaneM06/Leaf/L44444444444444444121203, CKLaneM06/Leaf/L444444444444444441213, CKLaneM06/Leaf/L4444444444444444413, CKLaneM06/Leaf/L444444444444444450300012, CKLaneM06/Leaf/L444444444444444450300013, CKLaneM06/Leaf/L4444444444444444513, CKLaneM06/Leaf/L444444444444444503000142, CKLaneM06/Leaf/L444444444444444503000143, CKLaneM06/Leaf/L444444444444444503000153).lean)

import Definitions.Def_CK_CKLaneM06_Checker

-- ===== source module CKLaneM06.Leaf.L444444444444444440202021203 =====
section

/-! Archived same-side leaf `444444444444444440202021203` (owner `parent_tail`, archived lower `[0.053550236282899199129`):
exact box `x ∈ [2,3]`, `b ∈ [47/1024,31/512]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444440202021203

open CKLaneM06

/-- Archived path `444444444444444440202021203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 1, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 8 : ℚ), rhi := (1 / 4 : ℚ),
    Ehi := (237724925 / 140737488355328 : ℚ), u := (123233576251 / 549755813888 : ℚ) }

theorem box_eq : pathBox path = ⟨2, 3, 47 / 1024, 31 / 512, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444440202021203

end

-- ===== source module CKLaneM06.Leaf.L444444444444444440202021213 =====
section

/-! Archived same-side leaf `444444444444444440202021213` (owner `parent_tail`, archived lower `[0.085235535980249619982`):
exact box `x ∈ [3,4]`, `b ∈ [47/1024,31/512]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444440202021213

open CKLaneM06

/-- Archived path `444444444444444440202021213` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 1, 2, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 16 : ℚ), rhi := (1 / 8 : ℚ),
    Ehi := (211427593 / 140737488355328 : ℚ), u := (64439079515 / 274877906944 : ℚ) }

theorem box_eq : pathBox path = ⟨3, 4, 47 / 1024, 31 / 512, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444440202021213

end

-- ===== source module CKLaneM06.Leaf.L444444444444444440202120203 =====
section

/-! Archived same-side leaf `444444444444444440202120203` (owner `parent_tail`, archived lower `[0.102481920037792515981`):
exact box `x ∈ [4,5]`, `b ∈ [47/1024,31/512]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444440202120203

open CKLaneM06

/-- Archived path `444444444444444440202120203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 1, 2, 0, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 32 : ℚ), rhi := (1 / 16 : ℚ),
    Ehi := (392461051 / 281474976710656 : ℚ), u := (263764787921 / 1099511627776 : ℚ) }

theorem box_eq : pathBox path = ⟨4, 5, 47 / 1024, 31 / 512, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444440202120203

end

-- ===== source module CKLaneM06.Leaf.L4444444444444444402021203 =====
section

/-! Archived same-side leaf `4444444444444444402021203` (owner `parent_tail`, archived lower `[0.038919674650203815540`):
exact box `x ∈ [4,6]`, `b ∈ [31/512,23/256]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L4444444444444444402021203

open CKLaneM06

/-- Archived path `4444444444444444402021203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 1, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 64 : ℚ), rhi := (1 / 16 : ℚ),
    Ehi := (260923717 / 140737488355328 : ℚ), u := (27584104473 / 137438953472 : ℚ) }

theorem box_eq : pathBox path = ⟨4, 6, 31 / 512, 23 / 256, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L4444444444444444402021203

end

-- ===== source module CKLaneM06.Leaf.L4444444444444444402021213 =====
section

/-! Archived same-side leaf `4444444444444444402021213` (owner `parent_tail`, archived lower `[0.074136096529581786786`):
exact box `x ∈ [6,8]`, `b ∈ [31/512,23/256]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L4444444444444444402021213

open CKLaneM06

/-- Archived path `4444444444444444402021213` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 1, 2, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 256 : ℚ), rhi := (1 / 64 : ℚ),
    Ehi := (484552853 / 281474976710656 : ℚ), u := (112890175607 / 549755813888 : ℚ) }

theorem box_eq : pathBox path = ⟨6, 8, 31 / 512, 23 / 256, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L4444444444444444402021213

end

-- ===== source module CKLaneM06.Leaf.L4444444444444444402120203 =====
section

/-! Archived same-side leaf `4444444444444444402120203` (owner `parent_tail`, archived lower `[0.083473562341930641600`):
exact box `x ∈ [8,10]`, `b ∈ [31/512,23/256]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L4444444444444444402120203

open CKLaneM06

/-- Archived path `4444444444444444402120203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 1, 2, 0, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 1024 : ℚ), rhi := (1 / 256 : ℚ),
    Ehi := (472963913 / 281474976710656 : ℚ), u := (56771759465 / 274877906944 : ℚ) }

theorem box_eq : pathBox path = ⟨8, 10, 31 / 512, 23 / 256, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L4444444444444444402120203

end

-- ===== source module CKLaneM06.Leaf.L4444444444444444402120213 =====
section

/-! Archived same-side leaf `4444444444444444402120213` (owner `parent_tail`, archived lower `[0.085923226223738565632`):
exact box `x ∈ [10,12]`, `b ∈ [31/512,23/256]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L4444444444444444402120213

open CKLaneM06

/-- Archived path `4444444444444444402120213` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 1, 2, 0, 2, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4096 : ℚ), rhi := (1 / 1024 : ℚ),
    Ehi := (469501161 / 281474976710656 : ℚ), u := (227415632495 / 1099511627776 : ℚ) }

theorem box_eq : pathBox path = ⟨10, 12, 31 / 512, 23 / 256, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L4444444444444444402120213

end

-- ===== source module CKLaneM06.Leaf.L44444444444444444021203 =====
section

/-! Archived same-side leaf `44444444444444444021203` (owner `parent_tail`, archived lower `[0.058380876155861590350`):
exact box `x ∈ [8,12]`, `b ∈ [23/256,19/128]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L44444444444444444021203

open CKLaneM06

/-- Archived path `44444444444444444021203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 1, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4096 : ℚ), rhi := (1 / 256 : ℚ),
    Ehi := (658189773 / 281474976710656 : ℚ), u := (168303068329 / 1099511627776 : ℚ) }

theorem box_eq : pathBox path = ⟨8, 12, 23 / 256, 19 / 128, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L44444444444444444021203

end

-- ===== source module CKLaneM06.Leaf.L4444444444444444402121203 =====
section

/-! Archived same-side leaf `4444444444444444402121203` (owner `parent_tail`, archived lower `[0.086562839502231729099`):
exact box `x ∈ [12,14]`, `b ∈ [31/512,23/256]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L4444444444444444402121203

open CKLaneM06

/-- Archived path `4444444444444444402121203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 1, 2, 1, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 16384 : ℚ), rhi := (1 / 4096 : ℚ),
    Ehi := (7320221 / 4398046511104 : ℚ), u := (113748951157 / 549755813888 : ℚ) }

theorem box_eq : pathBox path = ⟨12, 14, 31 / 512, 23 / 256, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L4444444444444444402121203

end

-- ===== source module CKLaneM06.Leaf.L44444444444444444021213 =====
section

/-! Archived same-side leaf `44444444444444444021213` (owner `parent_tail`, archived lower `[0.064422728065721339907`):
exact box `x ∈ [12,16]`, `b ∈ [23/256,19/128]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L44444444444444444021213

open CKLaneM06

/-- Archived path `44444444444444444021213` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 1, 2, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 65536 : ℚ), rhi := (1 / 4096 : ℚ),
    Ehi := (651227839 / 281474976710656 : ℚ), u := (42185981347 / 274877906944 : ℚ) }

theorem box_eq : pathBox path = ⟨12, 16, 23 / 256, 19 / 128, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L44444444444444444021213

end

-- ===== source module CKLaneM06.Leaf.L444444444444444440213 =====
section

/-! Archived same-side leaf `444444444444444440213` (owner `parent_tail`, archived lower `[0.099968730217710098146`):
exact box `x ∈ [8,16]`, `b ∈ [19/128,17/64]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444440213

open CKLaneM06

/-- Archived path `444444444444444440213` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 65536 : ℚ), rhi := (1 / 256 : ℚ),
    Ehi := (909349675 / 281474976710656 : ℚ), u := (24494687641 / 274877906944 : ℚ) }

theorem box_eq : pathBox path = ⟨8, 16, 19 / 128, 17 / 64, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444440213

end

-- ===== source module CKLaneM06.Leaf.L44444444444444444031 =====
section

/-! Archived same-side leaf `44444444444444444031` (owner `parent_tail`, archived lower `[0.242407363497150610344`):
exact box `x ∈ [8,16]`, `b ∈ [17/64,1/2]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L44444444444444444031

open CKLaneM06

/-- Archived path `44444444444444444031` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 1]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 65536 : ℚ), rhi := (1 / 256 : ℚ),
    Ehi := (1095638787 / 281474976710656 : ℚ), u := (15707467765 / 549755813888 : ℚ) }

theorem box_eq : pathBox path = ⟨8, 16, 17 / 64, 1 / 2, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L44444444444444444031

end

-- ===== source module CKLaneM06.Leaf.L44444444444444444120203 =====
section

/-! Archived same-side leaf `44444444444444444120203` (owner `parent_tail`, archived lower `[0.064830000485551942208`):
exact box `x ∈ [16,20]`, `b ∈ [23/256,19/128]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L44444444444444444120203

open CKLaneM06

/-- Archived path `44444444444444444120203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 2, 0, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 1048576 : ℚ), rhi := (1 / 65536 : ℚ),
    Ehi := (650646783 / 281474976710656 : ℚ), u := (168771528389 / 1099511627776 : ℚ) }

theorem box_eq : pathBox path = ⟨16, 20, 23 / 256, 19 / 128, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L44444444444444444120203

end

-- ===== source module CKLaneM06.Leaf.L44444444444444444120213 =====
section

/-! Archived same-side leaf `44444444444444444120213` (owner `parent_tail`, archived lower `[0.064857276305971841636`):
exact box `x ∈ [20,24]`, `b ∈ [23/256,19/128]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L44444444444444444120213

open CKLaneM06

/-- Archived path `44444444444444444120213` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 2, 0, 2, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 16777216 : ℚ), rhi := (1 / 1048576 : ℚ),
    Ehi := (650601347 / 281474976710656 : ℚ), u := (84386626885 / 549755813888 : ℚ) }

theorem box_eq : pathBox path = ⟨20, 24, 23 / 256, 19 / 128, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L44444444444444444120213

end

-- ===== source module CKLaneM06.Leaf.L444444444444444441203 =====
section

/-! Archived same-side leaf `444444444444444441203` (owner `parent_tail`, archived lower `[0.111776454729767136479`):
exact box `x ∈ [16,24]`, `b ∈ [19/128,17/64]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444441203

open CKLaneM06

/-- Archived path `444444444444444441203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 16777216 : ℚ), rhi := (1 / 65536 : ℚ),
    Ehi := (896783743 / 281474976710656 : ℚ), u := (98437341405 / 1099511627776 : ℚ) }

theorem box_eq : pathBox path = ⟨16, 24, 19 / 128, 17 / 64, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444441203

end

-- ===== source module CKLaneM06.Leaf.L44444444444444444121203 =====
section

/-! Archived same-side leaf `44444444444444444121203` (owner `parent_tail`, archived lower `[0.064859094663828366235`):
exact box `x ∈ [24,28]`, `b ∈ [23/256,19/128]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L44444444444444444121203

open CKLaneM06

/-- Archived path `44444444444444444121203` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 2, 1, 2, 0, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 268435456 : ℚ), rhi := (1 / 16777216 : ℚ),
    Ehi := (650597937 / 281474976710656 : ℚ), u := (168773361607 / 1099511627776 : ℚ) }

theorem box_eq : pathBox path = ⟨24, 28, 23 / 256, 19 / 128, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L44444444444444444121203

end

-- ===== source module CKLaneM06.Leaf.L444444444444444441213 =====
section

/-! Archived same-side leaf `444444444444444441213` (owner `parent_tail`, archived lower `[0.111830950893794772108`):
exact box `x ∈ [24,32]`, `b ∈ [19/128,17/64]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444441213

open CKLaneM06

/-- Archived path `444444444444444441213` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 2, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4294967296 : ℚ), rhi := (1 / 16777216 : ℚ),
    Ehi := (448349987 / 140737488355328 : ℚ), u := (49219568457 / 549755813888 : ℚ) }

theorem box_eq : pathBox path = ⟨24, 32, 19 / 128, 17 / 64, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444441213

end

-- ===== source module CKLaneM06.Leaf.L4444444444444444413 =====
section

/-! Archived same-side leaf `4444444444444444413` (owner `parent_tail`, archived lower `[0.267849784086167753462`):
exact box `x ∈ [16,32]`, `b ∈ [17/64,1/2]`, `t ∈ [0,1/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L4444444444444444413

open CKLaneM06

/-- Archived path `4444444444444444413` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4294967296 : ℚ), rhi := (1 / 65536 : ℚ),
    Ehi := (1073892907 / 281474976710656 : ℚ), u := (15873933679 / 549755813888 : ℚ) }

theorem box_eq : pathBox path = ⟨16, 32, 17 / 64, 1 / 2, 0, 1 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L4444444444444444413

end

-- ===== source module CKLaneM06.Leaf.L444444444444444450300012 =====
section

/-! Archived same-side leaf `444444444444444450300012` (owner `parent_tail`, archived lower `[0.247054701219996875651`):
exact box `x ∈ [1,2]`, `b ∈ [17/64,49/128]`, `t ∈ [1/131072,1/65536]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444450300012

open CKLaneM06

/-- Archived path `444444444444444450300012` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 2]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4 : ℚ), rhi := (1 / 2 : ℚ),
    Ehi := (1787144677 / 140737488355328 : ℚ), u := (20746639171 / 1099511627776 : ℚ) }

theorem box_eq : pathBox path = ⟨1, 2, 17 / 64, 49 / 128, 1 / 131072, 1 / 65536⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444450300012

end

-- ===== source module CKLaneM06.Leaf.L444444444444444450300013 =====
section

/-! Archived same-side leaf `444444444444444450300013` (owner `parent_tail`, archived lower `[0.648670994282296789251`):
exact box `x ∈ [1,2]`, `b ∈ [49/128,1/2]`, `t ∈ [1/131072,1/65536]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444450300013

open CKLaneM06

/-- Archived path `444444444444444450300013` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4 : ℚ), rhi := (1 / 2 : ℚ),
    Ehi := (3889690155 / 281474976710656 : ℚ), u := (1379837749 / 274877906944 : ℚ) }

theorem box_eq : pathBox path = ⟨1, 2, 49 / 128, 1 / 2, 1 / 131072, 1 / 65536⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444450300013

end

-- ===== source module CKLaneM06.Leaf.L4444444444444444513 =====
section

/-! Archived same-side leaf `4444444444444444513` (owner `parent_tail`, archived lower `[0.002159194820727916739`):
exact box `x ∈ [16,32]`, `b ∈ [17/64,1/2]`, `t ∈ [1/131072,1/65536]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L4444444444444444513

open CKLaneM06

/-- Archived path `4444444444444444513` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4294967296 : ℚ), rhi := (1 / 65536 : ℚ),
    Ehi := (1073892907 / 140737488355328 : ℚ), u := (15873933679 / 549755813888 : ℚ) }

theorem box_eq : pathBox path = ⟨16, 32, 17 / 64, 1 / 2, 1 / 131072, 1 / 65536⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L4444444444444444513

end

-- ===== source module CKLaneM06.Leaf.L444444444444444503000142 =====
section

/-! Archived same-side leaf `444444444444444503000142` (owner `parent_tail`, archived lower `[0.052728873381969331377`):
exact box `x ∈ [1,2]`, `b ∈ [17/64,49/128]`, `t ∈ [1/65536,3/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444503000142

open CKLaneM06

/-- Archived path `444444444444444503000142` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4 : ℚ), rhi := (1 / 2 : ℚ),
    Ehi := (5361434031 / 281474976710656 : ℚ), u := (20746639171 / 1099511627776 : ℚ) }

theorem box_eq : pathBox path = ⟨1, 2, 17 / 64, 49 / 128, 1 / 65536, 3 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444503000142

end

-- ===== source module CKLaneM06.Leaf.L444444444444444503000143 =====
section

/-! Archived same-side leaf `444444444444444503000143` (owner `parent_tail`, archived lower `[0.368648589049075843253`):
exact box `x ∈ [1,2]`, `b ∈ [49/128,1/2]`, `t ∈ [1/65536,3/131072]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444503000143

open CKLaneM06

/-- Archived path `444444444444444503000143` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4 : ℚ), rhi := (1 / 2 : ℚ),
    Ehi := (91164613 / 4398046511104 : ℚ), u := (1379837749 / 274877906944 : ℚ) }

theorem box_eq : pathBox path = ⟨1, 2, 49 / 128, 1 / 2, 1 / 65536, 3 / 131072⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444503000143

end

-- ===== source module CKLaneM06.Leaf.L444444444444444503000153 =====
section

/-! Archived same-side leaf `444444444444444503000153` (owner `parent_tail`, archived lower `[0.169941339343465659508`):
exact box `x ∈ [1,2]`, `b ∈ [49/128,1/2]`, `t ∈ [3/131072,1/32768]`.  Generated by M06/work/gen_leaves.py. -/

set_option autoImplicit false

namespace CKLaneM06.Leaf.L444444444444444503000153

open CKLaneM06

/-- Archived path `444444444444444503000153` as digits. -/
def path : List ℕ := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3]

/-- Witness (rounding points only; every field re-verified by `check`). -/
def wit : Witness :=
  { rlo := (1 / 4 : ℚ), rhi := (1 / 2 : ℚ),
    Ehi := (7779380309 / 281474976710656 : ℚ), u := (1379837749 / 274877906944 : ℚ) }

theorem box_eq : pathBox path = ⟨1, 2, 49 / 128, 1 / 2, 3 / 131072, 1 / 32768⟩ := by
  decide +kernel

theorem check_ok : checkLeaf path wit = true := by decide +kernel

theorem dominance : ParentDominance (pathBox path) := checkLeaf_sound check_ok

theorem owner : PsiOwnerOn (pathBox path) := checkLeaf_owner check_ok

end CKLaneM06.Leaf.L444444444444444503000153

end


