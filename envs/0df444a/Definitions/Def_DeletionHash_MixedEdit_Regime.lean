-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Regime
-- name    : DeletionHash_MixedEdit_Regime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:07.080598+00:00
-- url     : https://prove2.me/theorems/e84ca5f1-502a-4592-8cf8-509a167491ec
-- title:
--   Standing proof regime and separated records
-- statement:
--   For the proof sections set $k=2\lceil\log_q n\rceil+2$, $L=3(k+b+1)$, with $q\ge2$, $t\ge2$, $b\ge1$, $k>b$ and $n\ge L$. A record is separated when its successive current-word positions obey
--   $$D_0\le p_i,\quad p_i+D_0\le n,\quad |p_i-p_j|\ge D_0\ (i\ne j),\qquad D_0=8(L+tb).$$
--   The additive right boundary avoids truncated subtraction. Separation is imposed only in proof lemmas, never on channel reachability, final codewords or received words. It refers to indexed edit occurrences, so repeated positions cannot bypass the pairwise condition.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §2.2, equation (3) and standing regime, printed p. 6 (PDF p. 8); §2.4, D₀ and separation, printed p. 8 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Definitions.Def_DeletionHash_MixedEdit_Edits

namespace DeletionHash.MixedEdit

universe u

noncomputable def gramLength (q n b : ℕ) : ℕ := 3 * (uniqueLength q n + b + 1)

/-- Standing conventions from §2.2, equation (3), excluding no sufficiently large n. -/
def Regime (q n t b k L : ℕ) : Prop :=
  2 ≤ q ∧ 2 ≤ t ∧ 1 ≤ b ∧ k = uniqueLength q n ∧ L = 3*(k+b+1) ∧ b < k ∧ L ≤ n

/-- Positions refer to successive current words; additive boundary avoids Nat truncation. -/
def Separated {α : Type u} (n t b L : ℕ) (record : List (Edit α)) : Prop :=
  let D := 8*(L+t*b)
  (∀ e ∈ record, D ≤ e.position ∧ e.position + D ≤ n) ∧
  (∀ i j : Fin record.length, i ≠ j →
    D ≤ Nat.dist (record.get i).position (record.get j).position)

end DeletionHash.MixedEdit


