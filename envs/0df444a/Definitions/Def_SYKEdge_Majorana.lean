-- Prove2me | Definitions.Def_SYKEdge_Majorana
-- name    : SYKEdge_Majorana
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:04:55.214483+00:00
-- url     : https://prove2.me/theorems/c882984b-8fd9-4aea-9cf3-683fa7ecd486
-- title:
--   Majorana operators $\gamma_1,\dots,\gamma_n$, Majorana monomials $\Gamma_S=i^{r(r-1)/2}\gamma_{s_1}\cdots\gamma_{s_r}$ and signs $\varepsilon_{S,T}$
-- statement:
--   Let $n\ge2$ be even. **Majorana operators** are matrices $\gamma_1,\dots,\gamma_n$ that are
--
--   1. Hermitian, $\gamma_i=\gamma_i^*$;
--   2. involutions, $\gamma_i^2=\mathrm{Id}$;
--   3. pairwise anti-commuting, $\gamma_i\gamma_j=-\gamma_j\gamma_i$ for $i\neq j$.
--
--   For a nonempty $S=\{s_1<\dots<s_r\}\subseteq[n]$ the **Majorana monomial** is
--   $$\Gamma_S=i^{r(r-1)/2}\,\gamma_{s_1}\gamma_{s_2}\cdots\gamma_{s_r},\qquad \Gamma_\emptyset=\mathrm{Id},$$
--   a Hermitian unitary with $\Gamma_S^2=\mathrm{Id}$. Two monomials commute up to the sign
--   $$\Gamma_S\Gamma_T=\varepsilon_{S,T}\,\Gamma_T\Gamma_S,\qquad \varepsilon_{S,T}=(-1)^{|S|\cdot|T|-|S\cap T|}.$$
--   Finally $\binom{[n]}{k}$ denotes the set of $k$-element subsets of $[n]$.
--
--   The paper fixes an irreducible unitary representation of these relations on $\mathbb C^N$, $N=2^{n/2}$; the statements of the mission quantify over every family of dimension $2^{n/2}$, which for even $n$ is the same class.
--
--   **Formalization Note** Modes are indexed by `Fin n` (that is, $0,\dots,n-1$). The predicate records only the three relations, on an arbitrary finite index set; statements add the dimension hypothesis $|\iota|=2^{n/2}$. The exponent $r(r-1)/2$ is an exact natural-number division, and $|S\cap T|\le|S|\cdot|T|$, so the exponent of $\varepsilon_{S,T}$ involves no truncated subtraction.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, §3 'Majorana Operators', p.15, eq. (7) and footnote 14; eq. (1), p.1

import Mathlib

open Matrix

namespace SYKEdge

/-!
# Majorana families, Majorana monomials `Γ_S` and the commutation signs `ε_{S,T}`

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, §3 "Majorana Operators", p.15, and (7); (1), p.1.

**Formalization Note.**
* Modes are `Fin n` (the page's `[n]` shifted to start at `0`).
* `IsMajoranaFamily γ` is the page's three properties (Hermitian, involution, anti-commutation)
  for a family `γ : Fin n → Matrix ι ι ℂ` on an arbitrary finite index type `ι`. The page then fixes
  an irreducible unitary representation on `ℂ^N`, `N = 2^{n/2}` (footnote 14); statements of the
  mission add the hypothesis `Fintype.card ι = 2 ^ (n / 2)`. For even `n` the complex Clifford algebra
  on `n` generators is the full matrix algebra of size `2^{n/2}`, so every family of that dimension
  is such an irreducible representation, and every irreducible representation is one.
* `monomial γ S = Γ_S = i^{r(r−1)/2} γ_{s₁} ⋯ γ_{s_r}` with `s₁ < ⋯ < s_r` the elements of `S`
  (`Finset.sort`), `r = |S|`; for `S = ∅` the empty product and `i⁰` give `Γ_∅ = Id`. The
  exponent `r(r−1)/2` is computed in `ℕ`, where the division is exact (`r(r−1)` is even).
* `eps S T = ε_{S,T} = (−1)^{|S|·|T| − |S∩T|}`, (7). The `ℕ` subtraction is exact because
  `|S∩T| ≤ |S|·|T|` for all finite sets (if `T = ∅` both sides are `0`; otherwise
  `|S∩T| ≤ |S| ≤ |S|·|T|`).
* `KSet n k` is `([n] choose k)`, the `k`-subsets of the modes.
-/

/-- `([n] choose k)`: the `k`-element subsets of the modes `Fin n`. -/
abbrev KSet (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- **Majorana operators** (p.15): a family `γ₁, …, γ_n` of matrices with
(1) `γ_i = γ_i*` (Hermitian), (2) `γ_i² = Id` (involution), (3) `γ_iγ_j = −γ_jγ_i` for `i ≠ j`
(anti-commutation). -/
structure IsMajoranaFamily {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Fin n → Matrix ι ι ℂ) : Prop where
  herm : ∀ i, (γ i).IsHermitian
  sq : ∀ i, γ i * γ i = 1
  anticomm : ∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i)

/-- The **Majorana monomial** `Γ_S := i^{r(r−1)/2} γ_{s₁} ⋯ γ_{s_r}` for
`S = {s₁ < ⋯ < s_r}`, and `Γ_∅ := Id` (p.15). -/
noncomputable def monomial {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Fin n → Matrix ι ι ℂ) (S : Finset (Fin n)) : Matrix ι ι ℂ :=
  (Complex.I ^ (S.card * (S.card - 1) / 2)) • ((S.sort (· ≤ ·)).map γ).prod

/-- The commutation sign `ε_{S,T} := (−1)^{|S|·|T| − |S∩T|}`, so that `Γ_SΓ_T = ε_{S,T} Γ_TΓ_S`,
(7), p.15. -/
def eps {n : ℕ} (S T : Finset (Fin n)) : ℤ :=
  (-1) ^ (S.card * T.card - (S ∩ T).card)

end SYKEdge


