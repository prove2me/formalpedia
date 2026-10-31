-- Prove2me | Definitions.Def_KempeCloning_Sector
-- name    : KempeCloning_Sector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:00.227163+00:00
-- url     : https://prove2.me/theorems/c995b027-9b9a-4e66-be67-d2de1b0e7516
-- title:
--   Labels $(i,j)$ with $i+j\le N$ of the sector (15)
-- statement:
--   For $N\in\mathbb N$, $\mathrm{Sector}(N)$ is the finite set of pairs $(i,j)$ of natural numbers with $i + j \le N$. These label the Fock states of the general form (15),
--
--   $$|(m+j)_{a_1}, i_{a_2}, i_{b_1}, j_{b_2}, (N-i-j)_c\rangle ,$$
--
--   that the Hamiltonian (14) generates from the initial state (13).
--
--   **Formalization Note** Pairs in $\{0,\dots,N\}^2$ with $i+j\le N$, so $N-i-j$ is a natural number.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (15), p.4

import Mathlib

namespace KempeCloning

/-- **Labels `(i, j)` with `i + j ≤ N` of the dynamical sector (15).**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (15), p.4: "Action of (14) on (13)
generates Fock basis states of the general form |(m + j)_{a1}, i_{a2}, i_{b1}, j_{b2}, (N − i − j)_c⟩".

`Sector N` is the finite set of pairs `(i, j)` of natural numbers with `i + j ≤ N`, each written as
a pair of elements of `Fin (N + 1)`.

**Formalization Note.** The occupation `N − i − j` of mode `c` is a natural number exactly when
`i + j ≤ N`, which is the constraint of the subtype. -/
abbrev Sector (N : ℕ) : Type := {q : Fin (N + 1) × Fin (N + 1) // q.1.val + q.2.val ≤ N}

end KempeCloning


