-- Prove2me | Definitions.Def_QPACLarge_padFn
-- name    : QPACLarge_padFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:35.422189+00:00
-- url     : https://prove2.me/theorems/efe9ea59-d7ec-4898-8fbe-2a263b361447
-- title:
--   Padded function $f_g(x,z)=g(x)$
-- statement:
--   For $g : \{0,1\}^m \to \{0,1\}$ and $n > m$, the **padded function** $f_g : \{0,1\}^n \to \{0,1\}$ is $f_g(x, z) = g(x)$ for $(x, z) \in \{0,1\}^m \times \{0,1\}^{n-m}$: it depends only on the $m$-bit prefix (the core input) of its argument. The padded class is $D_{n,m} = \{f_g : g \in \mathrm{ALL}_m\}$.
--
--   **Formalization Note** Every use has $m < n$; the junk case $m > n$ would read missing bits as $0$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 5.1, p.34

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QPACLarge

open QAlgorithms

/-- **The padded function `f_g(x, z) = g(x)`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 5.1, p.34: "`D_{n,m} = {f_g(x, z) = g(x) : g ∈ ALL_m}`, where
`(x, z) ∈ {0,1}^m × {0,1}^{n−m}`"; "The core input of a query `y ∈ {0,1}ⁿ` is its `m`-bit prefix."

`padFn n g` reads `g` on the first `m` bits of its `n`-bit input.

**Formalization Note.** Every use has `m < n`; for `m > n` the missing bits would be read as `0`. -/
def padFn {m : ℕ} (n : ℕ) (g : Qubits m → Bool) : Qubits n → Bool :=
  fun y => g fun i => if hi : (i : ℕ) < n then y ⟨i, hi⟩ else false

end QPACLarge


