-- Prove2me | Definitions.Def_MCPoise_AVert
-- name    : MCPoise_AVert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:52.824041+00:00
-- url     : https://prove2.me/theorems/1a3f37ec-c9d7-4a6a-a913-7e57021e30e6
-- title:
--   The vertices and edge weights of the auxiliary graph
-- statement:
--   The auxiliary graph has **pair vertices** $z_i$, $i \in [k]$, and **root copies** $r_{j,\ell}$ for a root $j$ and a bucket $\ell \in \{0, \dots, \lceil \log_2 M \rceil + 2\}$. An edge at the root copy $r_{j,\ell}$ has weight $w = 1/2^{\ell+1}$.
--
--   **Formalization Note** The page writes "$\log M + 2$". The ceiling is what is needed, since a surviving $\lambda_{i,j} \in (1/(8M), 1]$ lies in a bucket $\ell$ with $2^\ell < 8M$.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2.1, p.11

import Mathlib

namespace MCPoise

/-- A root copy `r_{j,ℓ}`: a root `j ∈ [M]` (`M = k`) and a bucket `ℓ = 0, …, ⌈log₂ M⌉ + 2` (p.11). -/
abbrev Copy (k : ℕ) : Type := Fin k × Fin (Nat.clog 2 k + 3)

/-- **The vertices of the auxiliary graph.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2.1, p.11: "On one side, we add a vertex z_i for each (s_i, t_i) pair in D′; these are referred to as pair
vertices. The other side consists of vertices r_{j,ℓ} for each root r_j and bucket B_ℓ; these vertices are referred to
as root copies."

`Sum.inl i` is `z_i` and `Sum.inr (j, ℓ)` is `r_{j,ℓ}`.

**Formalization Note.** The page's "ℓ = 0, . . . , log M + 2" is read with the ceiling `⌈log₂ M⌉`: every surviving
`λ_{i,j}` lies in `(1/(8M), 1]`, and `1/(8M) < 1/2^ℓ` gives `2^ℓ < 8M`, so `ℓ ≤ ⌈log₂ M⌉ + 2`. -/
abbrev AVert (k : ℕ) : Type := Fin k ⊕ Copy k

/-- The weight `w(e) = 1/2^{ℓ+1}` of an auxiliary edge at the root copy `r_{j,ℓ}` (p.11). -/
noncomputable def wt {k : ℕ} (c : Copy k) : ℝ := 1 / 2 ^ (c.2.val + 1)

end MCPoise


