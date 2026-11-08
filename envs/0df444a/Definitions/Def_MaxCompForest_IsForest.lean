-- Prove2me | Definitions.Def_MaxCompForest_IsForest
-- name    : MaxCompForest_IsForest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:24.440344+00:00
-- url     : https://prove2.me/theorems/55cf27d8-c9ce-4312-aeca-d9fd5b73062c
-- title:
--   Label-sensitive forest
-- statement:
--   A set $F$ of edge labels is a **forest** when it contains no cycle; two parallel labels form a cycle. Equivalently,
--   $$
--   |F|+\#\{\text{components of }(V,F)\}=|V| .
--   $$
--   The left side is at least $|V|$ for every label set, with equality exactly for forests.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.1, p.15, p.19

import Mathlib
import Definitions.Def_MaxCompForest_spanSub
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

/-- **`F` is a forest of labelled edges**: `|F|` plus the number of components of `(V, F)` equals `|V|`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.1, p.15, p.19.

**Formalization Note.** Always `|F| + #components ≥ |V|`, with equality exactly when `F` has no cycle,
counting two parallel labels as a cycle (the sanity file proves a parallel pair is not a forest).
Mathlib's `IsAcyclic` on the underlying simple graph would forget labels. -/
def IsForest (G : WGraph V E) (F : Finset E) : Prop :=
  F.card + Nat.card (spanSub G F).ConnectedComponent = Fintype.card V

end MaxCompForest


