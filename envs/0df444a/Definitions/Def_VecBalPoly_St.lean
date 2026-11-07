-- Prove2me | Definitions.Def_VecBalPoly_St
-- name    : VecBalPoly_St
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:09:38.773589+00:00
-- url     : https://prove2.me/theorems/b2f6ea20-bc30-4e2e-b47e-a83b01491ef9
-- title:
--   State of Algorithm 2.2
-- statement:
--   A state of Algorithm 2.2 on an $m\times n$ input consists of
--   1. the fractional coloring $x\in\mathbb R^n$;
--   2. the active set $V\subseteq[n]$;
--   3. for each row $i$, the set $T_i$ of retained column indices;
--   4. for each row $i$, the offset $c_i$ recording the contributions of removed entries;
--   5. for each row $i$, the scale $r_i$;
--   6. for each row $i$, the set $D_i$ of column indices whose entries were removed from row $i$ by the dominant-entry rule.
--
--   **Formalization Note** Indices start at $0$. The last component is a ghost field: the algorithm never reads it; it is the set $D_i$ of the proof of Lemma 3.1.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), §2.1, pp.3–4 (PDF pp.4–5); §2.2, p.4; proof of Lemma 3.1, p.7

import Mathlib

namespace VecBalPoly

/-- **A state of Algorithm 2.2** for an `m × n` input: the fractional coloring `x ∈ ℝⁿ`, the
active set `V`, the retained sets `Tᵢ`, the offsets `cᵢ`, the scales `rᵢ`, and the set `Domᵢ` of
column indices whose entries were removed from row `i` by the dominant-entry rule.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.1, pp.3–4 (PDF pp.4–5); §2.2, p.4; proof of Lemma 3.1, p.7 (the sets `Dᵢ`).

**Formalization Note** Columns and rows are indexed from `0` (`Fin n`, `Fin m`). `Dom` is a ghost
field: the algorithm never reads it; it records the paper's `Dᵢ` for Lemma 3.1. -/
structure St (m n : ℕ) where
  x : Fin n → ℝ
  V : Finset (Fin n)
  T : Fin m → Finset (Fin n)
  c : Fin m → ℝ
  r : Fin m → ℝ
  Dom : Fin m → Finset (Fin n)

end VecBalPoly


