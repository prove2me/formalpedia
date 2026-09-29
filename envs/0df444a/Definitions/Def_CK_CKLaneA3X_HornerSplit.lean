-- Prove2me | Definitions.Def_CK_CKLaneA3X_HornerSplit
-- name    : CK_CKLaneA3X_HornerSplit
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:24:56.109152+00:00
-- url     : https://prove2.me/theorems/947a6593-3f0c-4483-9676-672e13b49997
-- title:
--   Courtade–Kumar proof module `CKLaneA3X.HornerSplit` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3X.HornerSplit` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3X.HornerSplit` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3X.HornerSplit (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/HornerSplit.lean)

import Definitions.Def_CK_CKLaneA3X_TMFun

/-!
# CKLaneA3X.HornerSplit — one Horner iteration per theorem

`tmHorner_good` checks a whole Horner evaluation inside one kernel `decide`, which at order 24 needs
~30 GB. These lemmas perform one iteration `H ↦ c + X·H` with an intermediate literal accumulator `H`,
so each iteration is a separate (small) kernel check.
-/

namespace CKLaneA3X

theorem hornerSplit_good {x : ℝ → ℝ → ℝ} {X H : TMd} (hx : Good x X) (vx n : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n) (hn : n ≤ X.n)
    (c : ℚ) (cs cs' : List ℚ) (hcs : cs = c :: cs')
    (hH : Good (fun t ρ => hornerR cs' (x t ρ)) H) (hHn : H.n = n) :
    Good (fun t ρ => hornerR cs (x t ρ)) (TMd.add (TMd.const c n) (TMd.mul X H vx 0 n)) := by
  subst hcs
  have hm := TMd.mul_good hx hH vx 0 n hz (zeroPrefix_zero _) hvx (by omega) (by omega)
  exact TMd.add_good (TMd.const_good c n) hm

theorem hornerSplitLast_good {x : ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) (vx n : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n) (hn : n ≤ X.n)
    (c : ℚ) (cs : List ℚ) (hcs : cs = [c]) :
    Good (fun t ρ => hornerR cs (x t ρ)) (TMd.add (TMd.const c n) (TMd.mul X (TMd.zero n) vx 0 n)) :=
  hornerSplit_good hx vx n hz hvx hn c cs [] hcs (TMd.zero_good n) rfl

end CKLaneA3X


