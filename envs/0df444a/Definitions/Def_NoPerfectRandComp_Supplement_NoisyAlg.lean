-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_NoisyAlg
-- name    : NoPerfectRandComp_Supplement_NoisyAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:16:31.645667+00:00
-- url     : https://prove2.me/theorems/28d22af6-f990-4b38-a77b-504e92f32aab
-- title:
--   Noisy query algorithm
-- statement:
--   A randomised **noisy query algorithm** is an adaptive strategy: it maps the history of returned bits (answers to its noisy queries and outcomes of its internal coins, in order) to its next step. The randomness of each noisy answer is independent of everything else.
--
--   **Formalization Note** This is a possibly infinite adaptive tree with explicit fair-coin nodes. It contains every distribution over noisy decision trees, including those with unbounded but almost surely finite stopping time.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4, p.11

import Mathlib
import Definitions.Def_NoPerfectRandComp_Supplement_NoisyAct

namespace NoPerfectRandComp

namespace Supplement

/-- A randomised noisy query algorithm (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4, p.11): an adaptive strategy that maps
the history of returned bits (answers to noisy queries and outcomes of internal fair coins, in
order) to its next step.

**Formalization Note** This is a possibly infinite adaptive tree whose internal randomness is
given by explicit fair-coin nodes; it covers distributions over noisy decision trees, including
trees with unbounded (almost surely finite) stopping time. Histories that cannot occur are
irrelevant. -/
abbrev NoisyAlg (ι : Type) : Type := List Bool → NoisyAct ι

end Supplement

end NoPerfectRandComp


