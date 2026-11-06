-- Prove2me | Definitions.Def_NewtonLCP_RumpWeight
-- name    : NewtonLCP_RumpWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:59.394563+00:00
-- url     : https://prove2.me/theorems/7171db9d-9042-4817-9eb7-1d96018b768f
-- title:
--   Rump weights $q_H$
-- statement:
--   Let $H\in\mathbb R^{n\times n}$ and $K=8$. For $j\in[n]$ the **Rump weight** is
--
--   $$q_H(j)=\max\Big\{\prod_{k=1}^{\ell}\frac{|H_{i_ki_{k+1}}|}{K}:\ i_1,\dots,i_{\ell+1}=j\text{ is a simple path}\Big\},$$
--
--   with the convention that the product is $1$ for an empty path; $Q_H=\mathrm{diag}(q_H)$. In the paper $H=(I_n+A)^{-1}$ with $A\in\mathcal P_\star$.
--
--   These weights define the Rump norm $\|Q_Hv\|_2$ in which Newton steps converge at a rate independent of the handicap number.
--
--   **Formalization Note** A simple path ending at $j$ is a list of distinct indices with last entry $j$; the one-vertex path has weight $1$. The formula is defined for every $H$; the hypothesis $A\in\mathcal P_\star$ is carried by the theorems.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Definition 5.2 and K := 8, p.14

import Mathlib

namespace NewtonLCP

/-!
# Rump weights `q_H`

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), Definition 5.2, p.14 (with `K := 8`, p.14).

For `j ∈ [n]`, `q_H(j) = max {∏_{k=1}^{ℓ} |H_{i_k i_{k+1}}|/K : i₁, …, i_{ℓ+1} = j is a simple
path}`, with the convention that the product is `1` for an empty path; `Q_H = diag(q_H)`.

**Formalization Note.** `K = 8` is written as the literal `8`. A simple path ending at `j` is a
duplicate-free list `[i₁, …, i_{ℓ+1}]` whose last entry is `j`; its arcs are consecutive pairs
(the list zipped with its tail). The one-vertex list `[j]` is the empty path, of weight `1`. The
set of such lists is finite and nonempty, so the `sSup` is the maximum. The paper defines `q_H`
for `H = (Iₙ + A)⁻¹` with `A ∈ P⋆`; the formula is defined for every `H`, and that hypothesis
is carried by the theorems that use it.
-/

variable {ι : Type*}

/-- `∏_{k} |H_{i_k i_{k+1}}|/8` along the path `l` (empty product `1`). -/
noncomputable def pathWeight (H : Matrix ι ι ℝ) (l : List ι) : ℝ :=
  ((l.zip l.tail).map (fun p => |H p.1 p.2| / 8)).prod

/-- The Rump weight `q_H(j)` (Definition 5.2): the maximum of `pathWeight H l` over simple paths
`l` ending at `j`. -/
noncomputable def rumpWeight (H : Matrix ι ι ℝ) (j : ι) : ℝ :=
  sSup {r : ℝ | ∃ l : List ι, l.Nodup ∧ l.getLast? = some j ∧ r = pathWeight H l}

end NewtonLCP


