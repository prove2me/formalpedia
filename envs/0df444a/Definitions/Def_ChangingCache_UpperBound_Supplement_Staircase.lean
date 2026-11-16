-- Prove2me | Definitions.Def_ChangingCache_UpperBound_Supplement_Staircase
-- name    : ChangingCache_UpperBound_Supplement_Staircase
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:24:56.857762+00:00
-- url     : https://prove2.me/theorems/d4913bfc-679e-40b8-9373-a630aaaec593
-- title:
--   Section 6 staircase parameters and profile completions
-- statement:
--   The Section 6 staircase begins with $m(0)=1$ and $m(j)=j$ for $1\le j\le16$. Its parameters are
--   $$b_i=16+3i,\quad R_i=\lceil b_i/2\rceil,\quad K_1=16,\quad
--   K_{i+1}=K_i+R_i,\quad H_i=K_i-R_i+2.$$
--   With $T_0=16$, its stage endpoints and request positions are
--   $$F_i=T_{i-1}+H_i,\qquad T_i=F_i+R_i,\qquad r_i=2T_i-b_i.$$
--   For $i\ge1$, stage $i$ consists of $H_i$ entries at height $K_i$ followed by $R_i$ entries rising by one. A finite list records exactly the entries through $T_N$. The predicate that a profile follows the staircase through $N$ constrains those entries and leaves all later entries free. The first-drop completion is constant at an integer height $h$ after $T_N$. The final-drop completion replaces entries $p,p+1,\ldots$ by one.
--
--   All arithmetic for the parameters is in the integers before conversion to list lengths and indices. The unused padding values $K_0=16$ and $F_0=0$ have no source meaning and enter no theorem clause. No invariant about requests or cache contents is part of these definitions.
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), p. 17, Equation (10), and pp. 19–20, Section 6.2

import Mathlib

namespace ChangingCache.UpperBound.Supplement

/-! Section 6, Eq. (10), p. 17. Heights, lengths, times and offsets are computed in ℤ.
Conversion to a list index/length uses `toNat`; the theorems certify the source domain.
`stageK 0` and `stageF 0` are unused padding, since K and F start at 1. -/

def stageB (i : ℕ) : ℤ := 16 + 3 * (i : ℤ)

def halfCeil (z : ℤ) : ℤ := (z + 1) / 2

def stageR (i : ℕ) : ℤ := halfCeil (stageB i)

def stageK : ℕ → ℤ
  | 0 => 16
  | i + 1 => 16 + ∑ j ∈ Finset.range i, stageR (j + 1)

def stageH (i : ℕ) : ℤ := stageK i - stageR i + 2

def stageT (i : ℕ) : ℤ :=
  16 + ∑ j ∈ Finset.range i, (stageH (j + 1) + stageR (j + 1))

def stageF : ℕ → ℤ
  | 0 => 0
  | i + 1 => stageT i + stageH (i + 1)

def stageRequest (i : ℕ) : ℤ := 2 * stageT i - stageB i

/-- Entries 0 through T_N, including m(0)=1 and the cold rise m(j)=j, 1≤j≤16. -/
def staircaseEntries : ℕ → List ℕ
  | 0 => 1 :: (List.range 16).map (fun j => j + 1)
  | i + 1 => staircaseEntries i ++
      List.replicate (stageH (i + 1)).toNat (stageK (i + 1)).toNat ++
      (List.range (stageR (i + 1)).toNat).map
        (fun j => (stageK (i + 1) + (j : ℤ) + 1).toNat)

/-- Only the entries already specified by the staircase are constrained. -/
def StaircaseThrough (m : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ j ≤ (stageT N).toNat, m j = (staircaseEntries N)[j]?.getD 1

/-- First-drop completion, constant at h strictly after T_N. -/
def firstDropProfile (N : ℕ) (h : ℤ) (j : ℕ) : ℕ :=
  if j ≤ (stageT N).toNat then (staircaseEntries N)[j]?.getD 1 else h.toNat

/-- Replace only the as-yet unread suffix, starting at entry p, by height 1. -/
def finalDrop (m : ℕ → ℕ) (p j : ℕ) : ℕ := if j < p then m j else 1

end ChangingCache.UpperBound.Supplement


