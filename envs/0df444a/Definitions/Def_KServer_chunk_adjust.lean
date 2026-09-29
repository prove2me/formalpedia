-- Prove2me | Definitions.Def_KServer_chunk_adjust
-- name    : KServer_chunk_adjust
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T20:39:57.381973+00:00
-- url     : https://prove2.me/theorems/c665dfdc-5b59-46c7-97f3-a86d3f9b6952
-- title:
--   Chunk system parameter weakening (adjust)
-- statement:
--   A parameter-weakening combinator for chunk systems: given a chunk system with size floor cLo, ceiling cHi, total T, price pe, and count bound mLo, one may lower the floor, raise the ceiling, lower the total, raise the price, and lower the count bound, keeping all carrier data (sample space, probabilities, chunks, histories, sizes) unchanged. The cost inequality is preserved because the evader bail cost is monotone in the price parameter.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound: plumbing for the level recursion

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cLo' cHi cHi' T T' pe pe' : ℝ} {mLo mLo' : ℕ}

/-- Weakening the parameters of a chunk system: lower the size floor,
raise the size ceiling, lower the total, raise the price, lower the
count bound. -/
noncomputable def ChunkSystemB.adjust
    (C : ChunkSystemB X s t cLo cHi T pe mLo)
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ T)
    (hpe : pe ≤ pe') (hm : mLo' ≤ mLo) :
    ChunkSystemB X s t cLo' cHi' T' pe' mLo' where
  Ω := C.Ω
  instFin := C.instFin
  instDec := C.instDec
  P := C.P
  m := C.m
  hist := C.hist
  chunk := C.chunk
  size := C.size
  hP := C.hP
  hPsum := C.hPsum
  hm := le_trans hm C.hm
  hm0 := C.hm0
  href := C.href
  hadapt := C.hadapt
  hsmeas := C.hsmeas
  hne := C.hne
  hlast := C.hlast
  hopt := C.hopt
  hsize := fun ω i => ⟨le_trans hLo (C.hsize ω i).1,
    le_trans (C.hsize ω i).2 hHi⟩
  hcost := by
    intro i ω₀ E bail
    refine le_trans (C.hcost i ω₀ E bail) ?_
    refine Finset.sum_le_sum fun ω hω => ?_
    refine mul_le_mul_of_nonneg_left ?_ (C.hP ω).le
    unfold EvaderAlgorithm.bailCost
    rcases hq : bailTime bail
      (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten) (C.chunk ω i)
      with - | q
    · exact le_refl _
    · linarith
  htotal := le_trans hT C.htotal

/-- The carrier data of the adjusted system is unchanged. -/
theorem ChunkSystemB.adjust_eq
    (C : ChunkSystemB X s t cLo cHi T pe mLo)
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ T)
    (hpe : pe ≤ pe') (hm : mLo' ≤ mLo) :
    (C.adjust hLo hHi hT hpe hm).Ω = C.Ω := rfl

theorem ChunkSystemB.adjust_P
    (C : ChunkSystemB X s t cLo cHi T pe mLo)
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ T)
    (hpe : pe ≤ pe') (hm : mLo' ≤ mLo) :
    (C.adjust hLo hHi hT hpe hm).P = C.P := rfl

theorem ChunkSystemB.adjust_size
    (C : ChunkSystemB X s t cLo cHi T pe mLo)
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ T)
    (hpe : pe ≤ pe') (hm : mLo' ≤ mLo) :
    (C.adjust hLo hHi hT hpe hm).size = C.size := rfl

theorem ChunkSystemB.adjust_chunk
    (C : ChunkSystemB X s t cLo cHi T pe mLo)
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ T)
    (hpe : pe ≤ pe') (hm : mLo' ≤ mLo) :
    (C.adjust hLo hHi hT hpe hm).chunk = C.chunk := rfl

theorem ChunkSystemB.adjust_hist
    (C : ChunkSystemB X s t cLo cHi T pe mLo)
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ T)
    (hpe : pe ≤ pe') (hm : mLo' ≤ mLo) :
    (C.adjust hLo hHi hT hpe hm).hist = C.hist := rfl

theorem ChunkSystemB.adjust_m
    (C : ChunkSystemB X s t cLo cHi T pe mLo)
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ T)
    (hpe : pe ≤ pe') (hm : mLo' ≤ mLo) :
    (C.adjust hLo hHi hT hpe hm).m = C.m := rfl

end KServer


