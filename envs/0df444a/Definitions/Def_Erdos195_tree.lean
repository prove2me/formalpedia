-- Prove2me | Definitions.Def_Erdos195_tree
-- name    : Erdos195_tree
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:11:39.410012+00:00
-- url     : https://prove2.me/theorems/eec7777d-6862-4ebf-8d6e-9579be44d630
-- title:
--   Erdős #195: tree-witness $2$-adic orders on $\mathbb{Z}$
-- statement:
--   A **tree witness** is a function $\theta(k,r)\in\{0,1\}$ defined on the nodes $(k,r)$, $k\ge0$, $0\le r<2^k$, of the infinite binary tree of residues modulo powers of $2$. For distinct integers $x,y$ let $k=\nu_2(y-x)$, the lowest binary position where the two's-complement expansions of $x$ and $y$ differ, so that $x\equiv y\pmod{2^k}$. Define
--   $$x\prec_\theta y\iff x\neq y\ \text{and}\ \mathrm{bit}_k(x)=\theta\bigl(k,\ x \bmod 2^k\bigr).$$
--   Thus at each node of the binary tree, $\theta$ chooses which child subtree comes first. The $\varepsilon$-orders $\prec_\varepsilon$ of `Def_Erdos195_defs` are the special case $\theta(k,r)=\varepsilon_k$, independent of $r$. These orders are used as tail orders for Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195).
--
--   Formalization note: `θ : ℕ → ℤ → Bool`; only the values at `0 ≤ r < 2^k` matter, since the second argument is always `x % 2^k`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness orders suggested by GPT 6 Astra, formalized by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_defs

/-!
# Erdős Problem 195 — tree-witness orders on ℤ

A tree witness `θ : ℕ → ℤ → Bool` assigns a preferred bit `θ k r` to each node `(k, r)` of the
binary tree of residues (`r` is used modulo `2^k`; only `0 ≤ r < 2^k` matters).
For `x ≠ y` with `k = ν₂(y - x)`, `x ≺_θ y` iff the `k`-th two's-complement digit of `x` is `1`
exactly when `θ k (x mod 2^k) = true`. The ε-orders `epsLt ε` are the case `θ k _ = ε k`.
-/

namespace Erdos195

/-- The tree-witness order on ℤ. -/
def treeLt (θ : ℕ → ℤ → Bool) (x y : ℤ) : Prop :=
  x ≠ y ∧ (bitOne x (padicValInt 2 (y - x)) ↔
    θ (padicValInt 2 (y - x)) (x % 2 ^ padicValInt 2 (y - x)) = true)

end Erdos195


