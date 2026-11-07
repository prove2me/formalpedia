-- Prove2me | Definitions.Def_PunctSketch_IsValidStream
-- name    : PunctSketch_IsValidStream
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:53.724702+00:00
-- url     : https://prove2.me/theorems/5a563c7c-f805-4f7d-b556-61dbdacd3093
-- title:
--   A valid turnstile stream
-- statement:
--   A stream is valid when each of its updates has two distinct endpoints, an insertion only adds an edge absent from the current graph and a deletion only removes a present one. The graph starts out empty and the stream may have any length.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_PunctSketch_Update

namespace PunctSketch

/-- **A valid turnstile stream.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §1, p.1. Each update has two distinct endpoints; an insertion
only of an edge absent from the current graph, a deletion only of a present one, from the empty
graph. The stream may have any length. -/
def IsValidStream {n : ℕ} (σ : List (Update n)) : Prop :=
  ∀ (i : ℕ) (h : i < σ.length),
    σ[i].u ≠ σ[i].v ∧
      (σ[i].insert = true → ¬ (streamGraph (σ.take i)).Adj σ[i].u σ[i].v) ∧
      (σ[i].insert = false → (streamGraph (σ.take i)).Adj σ[i].u σ[i].v)

end PunctSketch


