-- Prove2me | Definitions.Def_ApproxVI_IsMarchaud
-- name    : ApproxVI_IsMarchaud
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:19.320801+00:00
-- url     : https://prove2.me/theorems/4e2cbb00-dbd3-41cc-86db-f758ecedb3d1
-- title:
--   Marchaud set-valued map
-- statement:
--   A set-valued map $H:\mathbb R^{d_1}\to\{\text{subsets of }\mathbb R^{d_2}\}$ is **Marchaud** if
--
--   1. for each $x$, $H(x)$ is convex and compact;
--   2. (point-wise boundedness) there is $K>0$ such that for each $x$, $\sup_{w\in H(x)}\|w\|<K(1+\|x\|)$;
--   3. $H$ is upper-semicontinuous.
--
--   Here $\|\cdot\|$ is the Euclidean norm. Marchaud maps are the standard right-hand sides of differential inclusions $\dot x\in H(x)$ for which solutions exist; Lemma 2 shows that the perturbed Bellman operator is one.
--
--   **Formalization Note** The page writes "for each $x$ … for some $K>0$"; the constant is taken uniform in $x$ (linear growth), the stronger reading and the one the proof of Lemma 2 establishes. The supremum condition is written point-wise, $\|w\|<K(1+\|x\|)$ for all $w\in H(x)$, which is equivalent on compact nonempty sets and avoids a junk value on the empty set. Nonemptiness of $H(x)$ is not required, as on the page.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §2, p.5

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ApproxVI_IsUSC

namespace ApproxVI

/-- Marchaud map, Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*,
arXiv:1709.04673v5, §2, p.5: `H : ℝ^{d₁} → {subsets of ℝ^{d₂}}` is Marchaud if
(i) for each `x`, `H(x)` is convex and compact; (ii) (point-wise boundedness) for each `x`,
`sup_{w ∈ H(x)} ‖w‖ < K(1 + ‖x‖)` for some `K > 0`; (iii) `H` is upper-semicontinuous.

**Formalization Note** `‖·‖` is the Euclidean norm. In (ii) one constant `K > 0` serves every
`x` (linear growth; the stronger of the two readings of "for some K > 0", and the one the
proof of Lemma 2 establishes). The supremum condition is written pointwise,
`∀ w ∈ H x, ‖w‖ < K(1 + ‖x‖)`: on a compact nonempty set the supremum is attained, so the two
agree, and the pointwise form avoids the junk value of a real `sSup` of the empty set.
Nonemptiness of `H(x)` is not required, as on the page. -/
def IsMarchaud {d₁ d₂ : ℕ} (H : (Fin d₁ → ℝ) → Set (Fin d₂ → ℝ)) : Prop :=
  (∀ x, Convex ℝ (H x) ∧ IsCompact (H x)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ x, ∀ w ∈ H x, euclNorm w < K * (1 + euclNorm x)) ∧
    IsUSC H

end ApproxVI


