-- Prove2me | Definitions.Def_ContractionLemma_aSlot
-- name    : ContractionLemma_aSlot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:26.584205+00:00
-- url     : https://prove2.me/theorems/54f504e2-d467-485c-8108-ee7c7c0bbd47
-- title:
--   The recursion parameters $\lambda,H,\varepsilon,u_d,a_d,\Delta,h,p_t$
-- statement:
--   Fix the scale $s$. The parameters of a call at depth $d$ with $M$ edges are $\lambda=\lceil\log_2 s\rceil$, the leaf size $H=\lceil s/\lfloor\sqrt\lambda\rfloor\rceil$, $\varepsilon=2^{-17}$, $u_d=\lfloor\varepsilon\lambda/2^d\rfloor$, $a_d=2\sum_{j\le d}u_j$ with $a_{-1}=0$, the packet size $L=2^{a_d}$, the number of edge classes $Q=64^{2a_d}$, the degree cap $\Delta=\lceil s^{9/10}\rceil$, $h=\lceil 3M/u_d\rceil$, and the child precision at an easy point of level $i$,
--
--   $$
--   p_t=p+8hD_i+8M(a_d+1),\qquad D_i=2^{a_d-i}.
--   $$
--
--   **Formalization Note** $\lfloor\varepsilon\lambda/2^d\rfloor$ is the natural-number quotient $\lambda/2^{d+17}$. For $s\le 1$ the leaf size divides by $\lfloor\sqrt\lambda\rfloor=0$; the lemmas that use it hold for large $s$ only.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.6, pp.74–76

import Mathlib

set_option autoImplicit false

namespace ContractionLemma

/-! Recursion parameters — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), App. A.6, pp.74–76 (PDF pp.77–79). Throughout, `s` is the (fixed) scale of
the original input. -/

/-- `λ = ⌈log₂ s⌉` (p.74). -/
def lam (s : ℕ) : ℕ := Nat.clog 2 s

/-- The leaf size `H = ⌈s/⌊√λ⌋⌉` (p.75); below `H` edges the recursion uses brute force.
(For `s ≤ 1`, `⌊√λ⌋ = 0` and the division gives `0`; the lemmas are stated for large `s`.) -/
def leafH (s : ℕ) : ℕ := ⌈(s : ℚ) / (Nat.sqrt (lam s) : ℚ)⌉₊

/-- `ε = 2^{−17}` (p.75). -/
noncomputable def epsC : ℝ := 1 / 2 ^ 17

/-- The number of levels used at depth `d`: `u_d = ⌊ελ/2^d⌋ = ⌊λ/2^{d+17}⌋` (p.75). -/
def uLev (s d : ℕ) : ℕ := lam s / 2 ^ (d + 17)

/-- **The slot length at depth `d`**: `a_d = 2 ∑_{j=0}^{d} u_j` (p.75); the packet size is
`L = 2^{a_d}` and the number of edge classes `Q = 64^{2a_d}`. -/
def aSlot (s d : ℕ) : ℕ := 2 * ∑ j ∈ Finset.range (d + 1), uLev s j

/-- `a_{d−1}`, with `a_{−1} = 0` (p.74). -/
def aPrev (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => aSlot s d

/-- The degree cap `∆ = ⌈s^{9/10}⌉` (p.74). -/
noncomputable def degCap (s : ℕ) : ℕ := ⌈(s : ℝ) ^ ((9 : ℝ) / 10)⌉₊

/-- `h = ⌈3M/u⌉` (Lemma A.15, p.73). -/
def taperH (M u : ℕ) : ℕ := ⌈(3 * M : ℚ) / u⌉₊

/-- The child precision at an easy point of level `i` of a call at depth `d` with `M` edges and
incoming precision `p` (p.76): `p_t = p + 8 h D_i + 8 M (a + 1)`, with `a = a_d`,
`h = ⌈3M/u_d⌉` and `D_i = 2^{a−i}`. -/
def childPrec (s d M i p : ℕ) : ℕ :=
  p + 8 * taperH M (uLev s d) * 2 ^ (aSlot s d - i) + 8 * M * (aSlot s d + 1)

end ContractionLemma


