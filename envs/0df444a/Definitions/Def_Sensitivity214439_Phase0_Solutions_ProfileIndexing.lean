-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_ProfileIndexing
-- name    : Sensitivity214439_Phase0_Solutions_ProfileIndexing
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:12:03.07285+00:00
-- url     : https://prove2.me/theorems/6f2fdecc-9e74-4184-8d8f-9b0622ce3629
-- title:
--   Flattening the 456 sensitivity coordinates
-- statement:
--   For an ordered rank pair $0\le i\le j<12$, define its triangular offset
--   $$
--   \tau(i,j)=12i-\frac{i(i-1)}2+(j-i),
--   $$
--   which lies below $78$. The four triangular blocks have offsets $78b+\tau(i,j)$ for $b=0,1,2,3$, and the switching block has offset $312+12i+j$.
--
--   The included bounds put every offset below $456$, yielding a finite index map. Pulling a real-valued vector on $\{0,\ldots,455\}$ back along this map produces a typed sensitivity profile.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/ProfileIndexing.lean lines 10–70; SHA256 2d3059a511a17662bc5ea71f00405187ba27150bfdaa6930a4938f0377cf4f9d; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic

namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityProfileIndexing
end SensitivityProfileIndexing



/-! Exact index order used by matched.Profile.flatten in the source archive. -/
namespace SensitivityProfileIndexing

open SensitivityProfile456
set_option autoImplicit false

def pairOffset (p : RankPair 12) : ℕ :=
  p.val.1.val * 12 - p.val.1.val * (p.val.1.val - 1) / 2 +
    (p.val.2.val - p.val.1.val)

set_option maxRecDepth 20000 in
theorem pairOffset_lt : ∀ p : RankPair 12, pairOffset p < 78 := by decide



def flatNat : ProfileIndex 12 → ℕ
  | .inl (kind,p) => kind.val * 78 + pairOffset p
  | .inr (i,j) => 312 + i.val * 12 + j.val

theorem flatNat_lt (index : ProfileIndex 12) : flatNat index < 456 := by
  rcases index with ⟨kind,p⟩ | ⟨i,j⟩
  · have hk := kind.isLt
    have hp := pairOffset_lt p
    simp only [flatNat]
    omega
  · have hi := i.isLt
    have hj := j.isLt
    simp only [flatNat]
    omega



def flattenIndex (index : ProfileIndex 12) : Fin 456 :=
  ⟨flatNat index,flatNat_lt index⟩



def fromFlat (values : Fin 456 → ℝ) : Profile 12 :=
  fun index => values (flattenIndex index)



end SensitivityProfileIndexing


