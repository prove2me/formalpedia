-- Prove2me | Definitions.Def_BipMatchNC_Weighted_Folded
-- name    : BipMatchNC_Weighted_Folded
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:11:18.695967+00:00
-- url     : https://prove2.me/theorems/5ea4bd25-2aff-4626-9505-fd5d94810759
-- title:
--   Folded Vandermonde and folded Wronskian matrices, r-folded roots of a polynomial space and Z_r (§2.3–2.4, Definition 2.5)
-- statement:
--   Let $F$ be a field and $\gamma\in F$. We say that $\gamma$ **has order at least $m$** if $\gamma\neq0$ and $\gamma^k\neq1$ for $0<k<m$; an element of infinite multiplicative order (such as $2\in\mathbb Q$) has order at least $m$ for every $m$, and "order more than $d$" means order at least $d+1$.
--
--   The **$\gamma$-folded Vandermonde matrix** $V(\alpha)$ is the $D\times r$ matrix with rows $0,\dots,D-1$ and columns $0,\dots,r-1$ whose entry in row $i$ and column $j$ is
--   $$V(\alpha)_{i,j}=(\alpha\gamma^{j})^{i}.$$
--   For polynomials $p_1,\dots,p_s\in F[x]$, the **$\gamma$-folded Wronskian** $W_\gamma(p_1,\dots,p_s)$ is the $s\times s$ matrix over $F[x]$ whose row $j$ ($0\le j\le s-1$) is $\big(p_1(\gamma^jx),\dots,p_s(\gamma^jx)\big)$.
--
--   An element $\alpha\in F$ is an **$r$-folded root** of $p\in F[x]$ (with respect to $\gamma$) if $p(\alpha\gamma^\ell)=0$ for each $0\le\ell\le r-1$. For a linear subspace $P\subseteq F[x]$, $\alpha$ is an **$r$-folded root of $P$** if it is an $r$-folded root of some **nonzero** $p\in P$. Finally $Z_r(P,\alpha)$ is the number of linearly independent polynomials of $P$ having $\alpha$ as an $r$-folded root, i.e. the dimension of the subspace
--   $$\{p\in P : p(\alpha)=p(\alpha\gamma)=\dots=p(\alpha\gamma^{r-1})=0\}.$$
--
--   These objects are the algebraic tools behind the rank criterion for the matching matrix.
--
--   **Formalization Note.** `OrderAtLeast γ m`, `foldedVandermonde γ α D r`, `foldedWronskian γ p` (entry `(j, i)` is `(p i).comp (C (γ^j) * X)`), `IsFoldedRoot`, `foldedRootSpace` (the common kernel of the evaluations at `α γ^ℓ`, `ℓ < r`), `IsFoldedRootOfSpace` and `foldedRootMult` (= $Z_r$, a `Module.finrank`). The printed Definition 2.5 says "some polynomial $p(x)\in P$"; the zero polynomial would make every $\alpha$ a root of every $P$, and the proof of Lemma 2.6 says "some nonzero $p_0(x)\in P$", which is the reading used.
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), pp. 6–7 (PDF 7–8), §2.3, §2.4 and Definition 2.5

import Mathlib

namespace BipMatchNC.Weighted

open Polynomial

/-- `γ` **has (multiplicative) order at least `m`**: `γ ≠ 0` and `γ ^ k ≠ 1` for `0 < k < m`.
An element of infinite order (such as `2 ∈ ℚ`) has order at least `m` for every `m`.
"`γ` has order more than `d`" is `OrderAtLeast γ (d + 1)`; "`γ` has order at least `n r`" (§3.1, p. 9)
is `OrderAtLeast γ (n * r)`. -/
def OrderAtLeast {F : Type*} [Field F] (γ : F) (m : ℕ) : Prop :=
  γ ≠ 0 ∧ ∀ k : ℕ, 0 < k → k < m → γ ^ k ≠ 1

/-- The `γ`-**folded Vandermonde matrix** `V(α)` (§2.3, p. 6): the `D × r` matrix whose entry in row
`i` (`0 ≤ i ≤ D - 1`) and column `j` (`0 ≤ j ≤ r - 1`) is `(α γ^j)^i`. Rows and columns are indexed
from `0`. -/
def foldedVandermonde {F : Type*} [Field F] (γ α : F) (D r : ℕ) : Matrix (Fin D) (Fin r) F :=
  fun i j => (α * γ ^ (j : ℕ)) ^ (i : ℕ)

/-- The `γ`-**folded Wronskian matrix** `W_γ(p₁, …, p_s)` (§2.4, p. 6): the `s × s` matrix over `F[x]`
whose entry in row `j` (`0 ≤ j ≤ s - 1`) and column `i` is `p_i(γ^j x)`. -/
noncomputable def foldedWronskian {F : Type*} [Field F] (γ : F) {s : ℕ} (p : Fin s → F[X]) :
    Matrix (Fin s) (Fin s) F[X] :=
  fun j i => (p i).comp (C (γ ^ (j : ℕ)) * X)

/-- `α` is an `r`-**folded root** of the polynomial `p` with respect to `γ` (Definition 2.5, p. 7):
`p(α γ^ℓ) = 0` for each `0 ≤ ℓ ≤ r - 1`. -/
def IsFoldedRoot {F : Type*} [Field F] (γ : F) (r : ℕ) (p : F[X]) (α : F) : Prop :=
  ∀ ℓ : ℕ, ℓ < r → p.eval (α * γ ^ ℓ) = 0

/-- The subspace of all polynomials having `α` as an `r`-folded root with respect to `γ`: the common
kernel of the evaluations at `α, α γ, …, α γ^{r-1}`. -/
noncomputable def foldedRootSpace {F : Type*} [Field F] (γ : F) (r : ℕ) (α : F) : Submodule F F[X] :=
  ⨅ ℓ : Fin r, LinearMap.ker (Polynomial.leval (α * γ ^ (ℓ : ℕ)))

/-- `α` is an `r`-**folded root of the linear space** `P ⊆ F[x]` with respect to `γ` (Definition 2.5,
p. 7): `α` is an `r`-folded root of some **nonzero** polynomial of `P`.

**Formalization Note.** The printed definition says "of some polynomial `p(x) ∈ P`"; the zero
polynomial would make every `α` a root of every `P`. The proof of Lemma 2.6 says "some nonzero
`p₀(x) ∈ P`", which is the reading used here. -/
def IsFoldedRootOfSpace {F : Type*} [Field F] (γ : F) (r : ℕ) (P : Submodule F F[X]) (α : F) :
    Prop :=
  ∃ p ∈ P, p ≠ 0 ∧ IsFoldedRoot γ r p α

/-- `Z_r(P, α)` (Definition 2.5, p. 7): the number of linearly independent polynomials in `P` for
which `α` is an `r`-folded root, i.e. the dimension of the subspace of `P` of polynomials having `α`
as an `r`-folded root (the largest size of a linearly independent family of such polynomials). -/
noncomputable def foldedRootMult {F : Type*} [Field F] (γ : F) (r : ℕ) (P : Submodule F F[X])
    (α : F) : ℕ :=
  Module.finrank F ↥(P ⊓ foldedRootSpace γ r α)

end BipMatchNC.Weighted


