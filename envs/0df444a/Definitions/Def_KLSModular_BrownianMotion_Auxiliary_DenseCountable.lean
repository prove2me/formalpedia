-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_DenseCountable
-- name    : KLSModular_BrownianMotion_Auxiliary_DenseCountable
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:34:02.937308+00:00
-- url     : https://prove2.me/theorems/86708a73-524c-4b6a-a05f-5beb74544abe
-- title:
--   Chosen countable dense subset
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. For a second-countable topological space `T`, `denseCountable T` is a chosen countable dense subset, with `dense_denseCountable` and `countable_denseCountable` recording its density and countability.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Topology.Bases
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def denseCountable (T : Type*) [TopologicalSpace T] [SecondCountableTopology T] : Set T :=
--     (TopologicalSpace.exists_countable_dense T).choose
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/DenseCountable.lean) · `BrownianMotion.Auxiliary.DenseCountable` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/DenseCountable.lean#L17-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.DenseCountable`, definition bundle `KLSModular_BrownianMotion_Auxiliary_DenseCountable`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Topology.Bases

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/DenseCountable.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
/-- A countable dense subset of a second-countable topological space. -/
def denseCountable (T : Type*) [TopologicalSpace T] [SecondCountableTopology T] : Set T :=
  (TopologicalSpace.exists_countable_dense T).choose
lemma dense_denseCountable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] :
    Dense (denseCountable T) :=
  (TopologicalSpace.exists_countable_dense T).choose_spec.2
lemma countable_denseCountable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] :
    (denseCountable T).Countable :=
  (TopologicalSpace.exists_countable_dense T).choose_spec.1


