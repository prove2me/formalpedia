-- Prove2me | Definitions.Def_DetDLP_M3B_ECFits
-- name    : DetDLP_M3B_ECFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:38:17.38375+00:00
-- url     : https://prove2.me/theorems/9d738227-ac12-433d-8081-8e519b421e2d
-- title:
--   EC block fits relation
-- statement:
--   The correspondence between executable EC polynomial network rows and named EC block rows.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_S8H0_AnchoredLayout
import Definitions.Def_DetDLP_S8H0_NamedBlocks

set_option autoImplicit false
namespace DetDLP.M3B.ECFits
open S8H0 RegisterMap NamedBlocks

def EBit {s : Shape} (r : Ref s) : ECPolyDefs.Bit :=
  (r.source.val, r.read false, r.read true)

structure Fits {q : ℕ} (a : ECPolyDefs.N) (b : NamedBlocks.B q) : Prop where
  g : ECPolyDefs.ng a = b.core.A.ng
  e : ECPolyDefs.ne a = b.core.A.ne
  own : ∀ i : Fin b.core.A.ne, ECPolyDefs.gate a i.val = (b.core.A.gate i).val
  name : ∀ i : Fin b.core.A.ne, ECPolyDefs.signal a i.val = (b.name i).val
  chk : ∀ (i : Fin b.core.A.ng) (x : Fin b.core.A.ne → Bool), ECPolyDefs.check a i.val
    (((List.finRange b.core.A.ne).filter (fun j => decide (b.core.A.gate j = i))).map x) =
    b.core.t i (fun j => x j.val)

def FitsCore {q : ℕ} (a : ECPolyDefs.N) (b : NamedBlocks.B q) : Prop :=
  Fits a ⟨AnchoredLayout.block b.core q, AnchoredLayout.signal b.core b.name⟩

end DetDLP.M3B.ECFits


