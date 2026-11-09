-- Prove2me | Definitions.Def_MMSImpossibility_Goods_Code
-- name    : MMSImpossibility_Goods_Code
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:09:57.517651+00:00
-- url     : https://prove2.me/theorems/458acc31-b2ca-4e0e-b39c-7a6a046bd2d2
-- title:
--   §1.4, §2.1 — balanced words $L_k$ and label sets $S(a)$
-- statement:
--   A binary word of length $k$ is $a = (a_0,\dots,a_{k-1}) \in \{0,1\}^k$. For even $k$, the **balanced words** are
--
--   $$L_k = \Big\{a \in \{0,1\}^k : \sum_{h=0}^{k-1} a_h = \tfrac k2\Big\}.$$
--
--   The **label set** of a word $a$ is
--
--   $$S(a) = \{2h + a_h : 0 \le h < k\} \subseteq \{0,\dots,2k-1\}.$$
--
--   Label sets are the agent types of the construction of §2.1: an agent with label set $S$ regards the goods $X_j$, $Y_j$ with $j \in S$ as labeled.
--
--   **Formalization Note** Words are maps `Fin k → Fin 2`, labels are elements of `Fin (2k)`. The Hamming distance of §1.4 is Mathlib's `hammingDist`.
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, §1.4 Preliminaries and §2.1, PDF p. 7 (printed p. 6)

import Mathlib

namespace MMSImpossibility.Goods

/-- §1.4 (PDF p. 7): the balanced binary words of length `k`,
`L_k = {a ∈ {0,1}^k : ∑_{h=0}^{k-1} a_h = k/2}` (the paper uses it for even `k`).
Coordinates are indexed by `0, …, k-1` (`Fin k`), letters by `Fin 2 = {0, 1}`. -/
def balancedWords (k : ℕ) : Finset (Fin k → Fin 2) :=
  Finset.univ.filter (fun a => ∑ h : Fin k, ((a h : Fin 2) : ℕ) = k / 2)

/-- §2.1 (PDF p. 7): the label set of a word `a`,
`S(a) = {2h + a_h : 0 ≤ h < k} ⊆ {0, …, 2k-1}`. -/
def labelSet {k : ℕ} (a : Fin k → Fin 2) : Finset (Fin (2 * k)) :=
  Finset.univ.image (fun h : Fin k =>
    (⟨2 * h.val + (a h).val, by have := h.isLt; have := (a h).isLt; omega⟩ : Fin (2 * k)))

end MMSImpossibility.Goods


