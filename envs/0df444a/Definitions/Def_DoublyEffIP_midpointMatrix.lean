-- Prove2me | Definitions.Def_DoublyEffIP_midpointMatrix
-- name    : DoublyEffIP_midpointMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:54.95986+00:00
-- url     : https://prove2.me/theorems/87b38d85-421b-4491-aa82-f00caba5623c
-- title:
--   The midpoint matrix $M_x$
-- statement:
--   Let $x=((x_{i,\mathrm{start}},x_{i,\mathrm{end}}))_{i\in[k]}$ be a batch of transition claims of length $t$ and let $\lambda\in\mathbb N$ be a splitting parameter. For $i\in[k]$ and $j\in\{0,\dots,\lambda\}$ let $x_{i,j}=\mathrm{step}^{(t/\lambda)\cdot j}(x_{i,\mathrm{start}})$ be the configuration reached after $(t/\lambda)\cdot j$ steps. The **midpoint matrix** is the $k\times(\lambda+1)$ matrix
--
--   $$
--   M_x[i,j]=x_{i,j}.
--   $$
--
--   **Formalization Note** Rows and columns are numbered from $0$; entries are configurations rather than their $S$ bits; $t/\lambda$ is natural-number division, exact when $\lambda\mid t$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Definition 10, p.19

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP

/-- **The midpoint matrix `M_x`** — Definition 10 of Chen–Hong–Kalai–Xi, *Towards a Doubly
Efficient IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), p.19: "let
x_{i,j} denote the configuration that M reaches after (t/λ)·j time steps when starting from
configuration x_{i,0} = x_{i,start}. Define the midpoint matrix M = M_x … M[i, j] = x_{i,j}."

`midpointMatrix step t lam x i j = step^{(t/λ)·j}(x_{i,start})` for rows `i : Fin k` and columns
`j ∈ {0, …, λ}`.

**Formalization Note.** Rows and columns are `0`-based: row `i : Fin k` is the paper's `i + 1`,
and column `j : Fin (λ + 1)` is the paper's `j ∈ {0, …, λ}`. An entry is a configuration (an
element of `C`) rather than its `S` bits. `t / λ` is natural-number division, exact in the paper's
setting `t = λ^τ` (p.20). -/
def midpointMatrix {C : Type*} (step : C → C) (t lam : ℕ) {k : ℕ} (x : Fin k → C × C) :
    Fin k → Fin (lam + 1) → C :=
  fun i j => step^[(t / lam) * j.val] (x i).1

end DoublyEffIP


