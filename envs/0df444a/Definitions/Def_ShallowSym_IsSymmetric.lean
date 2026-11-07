-- Prove2me | Definitions.Def_ShallowSym_IsSymmetric
-- name    : ShallowSym_IsSymmetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:00.235297+00:00
-- url     : https://prove2.me/theorems/93edf694-142f-4db5-bdfa-e59dc90039c7
-- title:
--   Symmetric Boolean functions
-- statement:
--   A Boolean function $f:\{0,1\}^n\to\{0,1\}$ is **symmetric** if its output depends only on the Hamming weight of its input:
--
--   $$|x| = |y| \implies f(x) = f(y)\qquad\text{for all } x,y\in\{0,1\}^n.$$
--
--   Majority $1[|x|\ge n/2]$, Parity $|x| \bmod 2$, every threshold function and every exact-weight function $1[|x|=t]$ are symmetric. Theorem 1 of the mission is a statement about all symmetric functions.
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §2 'Functions', p.4

import Mathlib
import Definitions.Def_ShallowSym_weight

namespace ShallowSym

/-- A Boolean function `f : {0,1}^n → {0,1}` is symmetric when its output depends only on the
Hamming weight of its input: `|x| = |y| → f x = f y`.

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §2 "Functions", p.4: "A Boolean function is symmetric if its output depends only on the
weight of its input." -/
def IsSymmetric {n : ℕ} (f : Cube n → Bool) : Prop :=
  ∀ x y : Cube n, weight x = weight y → f x = f y

end ShallowSym


