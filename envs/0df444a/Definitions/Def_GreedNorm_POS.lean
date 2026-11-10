-- Prove2me | Definitions.Def_GreedNorm_POS
-- name    : GreedNorm_POS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:45.946768+00:00
-- url     : https://prove2.me/theorems/4448aba4-16e7-4fac-8e47-b25cb13b701d
-- title:
--   Index set $\mathrm{POS}_{m,\epsilon}$
-- statement:
--   For $m\in\mathbb N$ and $\epsilon>0$,
--
--   $$
--   \mathrm{POS}_{m,\epsilon}=\bigl\{\min\{\lceil(1+\epsilon)^s\rceil,\,m\}: s\in\mathbb Z_{\ge0}\bigr\}.
--   $$
--
--   For $m\ge1$ it is a set of $O(\epsilon^{-1}\log m)$ indices in $\{1,\dots,m\}$ containing $1$ and $m$. Threshold vectors are indexed by it.
--
--   **Formalization Note** A `Finset ℕ` of 1-based indices, written as the members of $\{0,\dots,m\}$ of this form (every such value lies there).
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §2 Threshold vectors, p.5 (PDF 7)

import Mathlib

namespace GreedNorm

/-- **The index set** `POS_{m,ϵ} = {min{⌈(1+ϵ)^s⌉, m} : s ∈ ℤ_{≥0}}`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §2 "Threshold vectors", p.5 (PDF 7): "Fix ϵ > 0. We define POSm,ϵ := {min{⌈(1 + ϵ)^s⌉, m} :
s ∈ Z≥0}."

**Formalization Note** POS is a `Finset ℕ` of 1-based indices. Every `min{⌈(1+ϵ)^s⌉, m}` lies
in `{0, …, m}`, so the set is written as the members of `range (m+1)` that are of this form;
this is exactly the paper's set, for every `s : ℕ`. For `m ≥ 1` and `ϵ > 0` it contains `1`
(`s = 0`) and `m`; for `m = 0` it is `{0}`. `⌈·⌉` is `Nat.ceil`. -/
noncomputable def POS (m : ℕ) (ε : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (m + 1)).filter (fun ℓ => ∃ s : ℕ, min ⌈(1 + ε) ^ s⌉₊ m = ℓ)

end GreedNorm


