-- Prove2me | Definitions.Def_Erdos261_defs
-- name    : Erdos261_defs
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:45:30.04842+00:00
-- url     : https://prove2.me/theorems/274fa770-2997-42e3-bc9f-a2857f945a7d
-- title:
--   Erdős Problem 261: the representation property $n/2^n=\sum a_k/2^{a_k}$ and the greedy carry
-- statement:
--   **Erdős261Prop.** A natural number $n$ has property `Erdos261Prop` if there exist $t\ge2$ pairwise distinct positive integers $a_1,\dots,a_t$ with
--
--   $$\frac{n}{2^n}=\sum_{k=1}^{t}\frac{a_k}{2^{a_k}}.$$
--
--   This is copied verbatim from Google DeepMind's Formal Conjectures file for Erdős Problem 261 (the open part asks whether every $n\ge1$ has the property).
--
--   **Greedy carry.** $g_0=n$ and $g_{j+1}=2g_j-(n+j+1)$ if $2g_j\ge n+j+1$, otherwise $g_{j+1}=2g_j$. This is the greedy digit iteration of Borwein–Loring and Tengely–Ulas–Zygadło started at $(n,n)$; $g_j=0$ for some $j$ means the greedy algorithm finds a finite representation.
-- source:
--   Erdős Problem 261, https://www.erdosproblems.com/261; Formal Conjectures FormalConjectures/ErdosProblems/261.lean (def Erdos261Prop); greedy: Tengely, Ulas, Zygadło, J. Number Theory 217 (2020), arXiv:2008.01501, §3

import Mathlib

namespace Erdos261

/-- Verbatim from Formal Conjectures `FormalConjectures/ErdosProblems/261.lean`. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- The greedy carry from `(n, n)`: `g₀ = n`, `g_{j+1} = 2 g_j - (n+j+1)` if `2 g_j ≥ n+j+1`,
otherwise `g_{j+1} = 2 g_j` (the Borwein–Loring / Tengely–Ulas–Zygadło greedy iteration). -/
def greedy (n : ℕ) : ℕ → ℤ
  | 0 => n
  | j + 1 => if ((n + j + 1 : ℕ) : ℤ) ≤ 2 * greedy n j
      then 2 * greedy n j - ((n + j + 1 : ℕ) : ℤ) else 2 * greedy n j

end Erdos261


