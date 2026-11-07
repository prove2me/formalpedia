-- Prove2me | Definitions.Def_DetCCHard_pow2
-- name    : DetCCHard_pow2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:06.06434+00:00
-- url     : https://prove2.me/theorems/d3c722ad-f331-4fbc-8a79-569a2607e760
-- title:
--   $\mathrm{pow2}(a)$, the least power of two at least $a$
-- statement:
--   For $a \ge 1$, $\mathrm{pow2}(a) = 2^{\lceil \log a\rceil}$ is the **least power of two at least $a$**; logarithms are binary.
--
--   It fixes the padded coordinate count $q_0 = \mathrm{pow2}(4s|E|)$ of Definition 6.2 and the side $p_0 = \mathrm{pow2}(64(L+1))$ of the initial matrix (Lemma 5.4).
--
--   **Formalization Note** $\lceil \log_2 a \rceil$ is `Nat.clog 2 a`.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), §4.1, p.13

import Mathlib

namespace DetCCHard

/-- `pow2(a) = 2^{⌈log a⌉}`, the **least power of two at least `a`** (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, §4.1, p.13; logarithms are binary).

**Formalization Note** `Nat.clog 2 a` is `⌈log₂ a⌉` for `a ≥ 1`. -/
def pow2 (a : ℕ) : ℕ := 2 ^ Nat.clog 2 a

end DetCCHard


