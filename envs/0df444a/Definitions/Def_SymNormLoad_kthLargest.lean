-- Prove2me | Definitions.Def_SymNormLoad_kthLargest
-- name    : SymNormLoad_kthLargest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:46.565564+00:00
-- url     : https://prove2.me/theorems/8db67ac4-a175-4865-8e8a-f79a8e120f3e
-- title:
--   $k$-th largest coordinate $x^{\downarrow}_k$
-- statement:
--   For $x\in\mathbb R^M$ and $k\in[M]=\{1,\dots,M\}$, $x^{\downarrow}_k$ is the $k$-th largest coordinate of $x$: if $x_{\pi(1)}\ge\dots\ge x_{\pi(M)}$ is a decreasing rearrangement, $x^{\downarrow}_k=x_{\pi(k)}$.
--
--   **Formalization Note** Computed from Mathlib's ascending sort `Tuple.sort x` as the entry at sorted position $M-k$ (0-based). The value for $k\notin[1,M]$ is $0$ and never used.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Lemma 2.2, p.9

import Mathlib

namespace SymNormLoad

/-- **`k`-th largest coordinate `x↓_k`.** Chen–Im–Sirri, *Online Load Balancing under Symmetric
Norms*, manuscript (STOC 2027 submission), Lemma 2.2, p.9: `x↓_k` is the `k`-th largest coordinate
of `x`, for `k ∈ [M] = {1, …, M}`.

**Formalization Note** `Tuple.sort x` sorts `x` ascendingly, so `x↓_k` is the entry at sorted
position `M − k` (0-based). Outside `1 ≤ k ≤ M` the value is `0` (never used). -/
noncomputable def kthLargest {M : ℕ} (x : Fin M → ℝ) (k : ℕ) : ℝ :=
  if h : 1 ≤ k ∧ k ≤ M then x (Tuple.sort x ⟨M - k, by omega⟩) else 0

end SymNormLoad


