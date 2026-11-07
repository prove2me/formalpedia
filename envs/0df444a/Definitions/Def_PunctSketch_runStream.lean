-- Prove2me | Definitions.Def_PunctSketch_runStream
-- name    : PunctSketch_runStream
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:49.013445+00:00
-- url     : https://prove2.me/theorems/d5089f7b-30d5-411d-8547-465486bece7d
-- title:
--   The memory after a stream
-- statement:
--   Starting from a memory $s_0$, each update of the stream is fed to the update machine together with $n$, $k$ and the current memory. The result is the memory at the end of the stream.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.3, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_PunctSketch_UpdInput
import Definitions.Def_PunctSketch_Update

namespace PunctSketch

/-- **The memory after processing a stream.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.18. Each update of `σ` is fed to the
machine `upd` together with `n`, `k` and the current memory, starting from `s₀`. -/
def runStream (upd : UpdInput → List Bool) (n k : ℕ) (s₀ : List Bool) (σ : List (Update n)) :
    List Bool :=
  σ.foldl (fun s e => upd ⟨n, k, s, e.u, e.v, e.insert⟩) s₀

end PunctSketch


