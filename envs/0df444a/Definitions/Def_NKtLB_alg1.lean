-- Prove2me | Definitions.Def_NKtLB_alg1
-- name    : NKtLB_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:03:51.209636+00:00
-- url     : https://prove2.me/theorems/fbe9f684-04ce-4f0a-9f3a-edc5a448b500
-- title:
--   The strings $s_i$ of Algorithm 1
-- statement:
--   Algorithm 1 builds, with oracle access to a language $L$, a sequence of strings $s_1,s_2,\dots$:
--
--   1. $s_1$ is the lexicographically first $s'\in\{0,1\}^n$ with $s'\in L$;
--   2. for $i\ge2$, with $\varepsilon_i=(n+N_{i-1})^{-b}/2$, let $G_1:\{0,1\}^n\times\{0,1\}^{d_1}\to\{0,1\}^{m_{i,1}}$ and $G_2:\{0,1\}^{N_{i-1}}\times\{0,1\}^{d_2}\to\{0,1\}^{m_{i,2}}$ be the generators of Lemma 31 with security parameter $\varepsilon_i$. Then $s_i=G_1(x;z_1)\circ G_2(s_{i-1};z_2)$ for the lexicographically first $(x,z_1,z_2)\in\{0,1\}^n\times\{0,1\}^{d_1}\times\{0,1\}^{d_2}$ with this string in $L$.
--
--   If no candidate lies in $L$, then $s_i=\bot$, and $s_i=\bot$ whenever $s_{i-1}=\bot$.
--
--   **Formalization Note** This is the mathematical recursion, not a machine. The generators come from a family $F$ at $k_i=1/\varepsilon_i=2(n+N_{i-1})^b$, and $s_i$ is defined for every $i$; the stopping rule is `alg1Out`. The lexicographic order on triples is the order on $x\circ z_1\circ z_2$; the lengths are fixed, so the two orders agree.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75

import Mathlib
import Definitions.Def_NKtLB_alg1N
import Definitions.Def_NKtLB_allStrs
import Definitions.Def_NKtLB_PRGFamily

namespace NKtLB

open Classical

/-- **The strings `s_i` of Algorithm 1** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75):
```
1: procedure A^L(γ, 1^n)
2:   s0 := ⊥, N1 := n, θ1 := γn.
3:   for s′ ∈ {0,1}^n by lexicographical order do
4:     if s′ ∈ L then
5:       s1 ← s′.
6:       break
7:   γ′ := (γ + 1/2)/2.
8:   for i = 2, 3, · · · do
9:     m_{i,1} := ⌈γ′n/γ⌉, m_{i,2} := ⌈γ′θ_{i−1}/γ⌉.
10:    N_i := m_{i,1} + m_{i,2}, ε_i := (n + N_{i−1})^{−b}/2.
11:    θ_i := γN_i.
12:    Instantiate G1 : {0,1}^n × {0,1}^{d1} → {0,1}^{m_{i,1}} in Lemma 31 with security parameter ε_i.
13:    Instantiate G2 : {0,1}^{N_{i−1}} × {0,1}^{d2} → {0,1}^{m_{i,2}} in Lemma 31 with security parameter ε_i.
14:    s_i := ⊥.
15:    for x ∈ {0,1}^n, z1 ∈ {0,1}^{d1}, z2 ∈ {0,1}^{d2} by lexicographical order do
16:      if G1(x; z1) ◦ G2(s_{i−1}; z2) ∈ L then
17:        s_i := G1(x; z1) ◦ G2(s_{i−1}; z2).
18:        break
19:    if θ_i > n/(2 − 2γ′) then
20:      Output s_i.
21:      return
22: Output ⊥.
```
`alg1 F L γ b n i` is `s_i` (`none` for `⊥`), with the generators taken from the family `F` at
security parameter `ε_i = 1/k_i`, `k_i = 2(n + N_{i−1})^b`.

**Formalization Note.** This is the mathematical recursion, not a machine: `s_i` is defined for
every `i` (the stopping test of lines 19–21 is `alg1Out`), and `s_i = ⊥` when `s_{i−1} = ⊥`.
"Lexicographical order" on `(x, z1, z2)` is the order of `allStrs` on `x ∘ z1 ∘ z2`, the same order
since the three lengths are fixed. -/
noncomputable def alg1 (F : PRGFamily) (L : Set (List Bool)) (γ : ℝ) (b n : ℕ) :
    ℕ → Option (List Bool)
  | 0 => none
  | 1 => (allStrs n).find? (fun s => decide (s ∈ L))
  | i + 2 =>
    match alg1 F L γ b n (i + 1) with
    | none => none
    | some s =>
      let γ' : ℝ := (γ + 1 / 2) / 2
      let N' := alg1N γ n (i + 1)
      let m1 := ⌈γ' * n / γ⌉₊
      let m2 := ⌈γ' * (γ * N') / γ⌉₊
      let k := 2 * (n + N') ^ b
      let d1 := F.d n m1 k
      let d2 := F.d N' m2 k
      ((allStrs (n + d1 + d2)).map (fun v =>
          F.G n m1 k (v.take n) ((v.drop n).take d1) ++ F.G N' m2 k s (v.drop (n + d1)))).find?
          (fun s' => decide (s' ∈ L))

end NKtLB


