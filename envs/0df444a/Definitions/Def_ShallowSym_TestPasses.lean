-- Prove2me | Definitions.Def_ShallowSym_TestPasses
-- name    : ShallowSym_TestPasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:57.235211+00:00
-- url     : https://prove2.me/theorems/f2c11d8d-5cc7-4f1d-8121-d1060a5b9746
-- title:
--   A test passes: the shifted block weights are distinct modulo $k$
-- statement:
--   For a partition into $k$ blocks and shifts $s_i$, the test **passes** at $x$ if the shifted block weights
--
--   $$w_1(x)+s_1,\ \dots,\ w_k(x)+s_k$$
--
--   are pairwise distinct modulo $k$, i.e. they are the $k$ residues modulo $k$ in some order.
--
--   **Formalization Note** Stated as injectivity of $i\mapsto w_i(x)+s_i$ from `Fin k` to `ZMod k`.
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §3 'Anatomy of a test', p.8; §4, p.11

import Mathlib
import Definitions.Def_ShallowSym_blockWeight

namespace ShallowSym

/-- A test with partition `β : Fin n → Fin k` and shifts `s : Fin k → ZMod k` passes at `x`
when the shifted block weights `w_1 + s_1, …, w_k + s_k` are all distinct modulo `k`, i.e. when
`i ↦ w_i(x) + s_i` is injective into `ZMod k`.

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §4 p.11: "The test passes if w1 + s1, . . . , wk + sk are all distinct modulo k"; §3 p.8:
"check whether w1 + s1, . . . , wk + sk are all distinct modulo k." -/
def TestPasses {n k : ℕ} (β : Fin n → Fin k) (s : Fin k → ZMod k) (x : Cube n) : Prop :=
  Function.Injective (fun i : Fin k => ((blockWeight β x i : ℕ) : ZMod k) + s i)

end ShallowSym


