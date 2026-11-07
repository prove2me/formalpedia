-- Prove2me | Definitions.Def_QLocalCert_runLengths
-- name    : QLocalCert_runLengths
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:12.688286+00:00
-- url     : https://prove2.me/theorems/3afc1c17-06a3-4846-a5e2-7250db5f75a0
-- title:
--   Balanced strings and the zero-run-length vector $r(z)$
-- statement:
--   A string $z\in\{0,1\}^N$ is **balanced** if its Hamming weight is $N/2$. If the ones of a balanced $z$ occur at positions $p_1<\dots<p_{N/2}$ in $\{0,\dots,N-1\}$, its zero-run-length vector $r(z)=(r_0,\dots,r_{N/2})$ is
--   $$
--   r_i=\begin{cases}p_1,& i=0,\\ p_{i+1}-p_i-1,& 1\le i<N/2,\\ N-1-p_{N/2},& i=N/2.\end{cases}
--   $$
--   For $z=01011010$ this gives $r(z)=(1,1,0,1,1)$ (Figure 2(b)).
--
--   The vertex $a_i$ of each side of $T^{\mathrm{tr}}_{N,\mu}$ carries $r_i$ pendant leaves.
--
--   **Formalization Note** $p_{k+1}$ is `onePos z k`, the $k$-th element (0-based) of the set of one-positions, via `Nat.nth`. The subtractions are natural-number subtractions, exact for balanced strings; the value on unbalanced strings is not used.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §4, display defining r(z), p.34; Figure 2(b), p.35

import Mathlib

set_option autoImplicit false

namespace QLocalCert

/-- A string `z ∈ {0,1}^N` is **balanced** when its Hamming weight is `N/2`.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §4, p.34 ("strings z ∈ {0, 1}^N of Hamming
weight N/2").

**Formalization Note.** Bits are `Bool` with `true = 1`; positions are `Fin N = {0, …, N − 1}`. -/
def Balanced {N : ℕ} (z : Fin N → Bool) : Prop :=
  (Finset.univ.filter fun p => z p = true).card = N / 2

/-- `onePos z k` is the position of the `(k + 1)`-th one of `z`, i.e. `p_{k+1}` in the notation of
p.34 (positions `p₁ < ⋯ < p_{N/2}` of the ones of a balanced `z`). -/
noncomputable def onePos {N : ℕ} (z : Fin N → Bool) (k : ℕ) : ℕ :=
  Nat.nth (fun q => ∃ h : q < N, z ⟨q, h⟩ = true) k

/-- The zero-run-length vector `r(z) = (r₀, …, r_{N/2})` (§4, p.34): "If the ones occur at
positions p₁ < ⋯ < p_{N/2} ∈ {0, . . . , N − 1}, define r(z) = (r₀, . . . , r_{N/2}) by
rᵢ := p₁ (i = 0), p_{i+1} − pᵢ − 1 (1 ≤ i < N/2), N − 1 − p_{N/2} (i = N/2)."

Source: B. Jauregui, M. Miyamoto, STOC 2027 submission (manuscript sha256 b707143b…0c51), §4,
display defining r(z), p.34.

**Formalization Note.** `pᵢ = onePos z (i − 1)`. The three cases are tested in the order of the
display; the subtractions are natural-number subtractions, which are exact for a balanced string
(`p_{i+1} > pᵢ`, `p_{N/2} ≤ N − 1`). The value on unbalanced strings is never used. For
`z = 01011010` (positions `0, …, 7` from the left) it is `(1, 1, 0, 1, 1)` (Figure 2(b)). -/
noncomputable def runLengths {N : ℕ} (z : Fin N → Bool) : Fin (N / 2 + 1) → ℕ := fun i =>
  if i.val = 0 then onePos z 0
  else if i.val < N / 2 then onePos z i.val - onePos z (i.val - 1) - 1
  else N - 1 - onePos z (N / 2 - 1)

end QLocalCert


