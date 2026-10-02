-- Prove2me | Definitions.Def_AppliedComb_Polya_cycleIndex
-- name    : AppliedComb_Polya_cycleIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:42:18.794288+00:00
-- url     : https://prove2.me/theorems/0050580e-116f-40b5-bf63-4b0521f30380
-- title:
--   Section 15.4.1 — the monomial of a permutation and the cycle index P_G
-- statement:
--   Let $S$ be a finite set with $|S| = r$ and let $\pi$ be a permutation of $S$. Written in cycle notation (Section 15.2.1), $\pi$ splits $S$ into disjoint cycles; a fixed point of $\pi$ is a cycle of length $1$. For $1 \le k \le r$ let $j_k(\pi)$ be the number of cycles of length $k$ of $\pi$, so that $j_1 + 2j_2 + \cdots + r j_r = r$. The **monomial associated with** $\pi$ is
--
--   $$x_1^{j_1(\pi)}\, x_2^{j_2(\pi)} \cdots x_r^{j_r(\pi)}.$$
--
--   A **permutation group** $G$ of $S$ is a set of permutations of $S$ containing the identity and closed under composition and inverses. Its **cycle index** is the average of these monomials over $G$:
--
--   $$P_G(x_1, \ldots, x_r) = \frac{1}{|G|} \sum_{\pi \in G} x_1^{j_1(\pi)} \cdots x_r^{j_r(\pi)},$$
--
--   a polynomial with rational coefficients in $r$ commuting variables. For the dihedral group $D_8$ of the square, $P_{D_8} = \tfrac18\bigl(x_1^4 + 2x_1^2x_2 + 3x_2^2 + 2x_4\bigr)$.
--
--   The cycle index is the object into which Pólya's Enumeration Theorem substitutes power sums of the colors.
--
--   **Formalization Note.** `cycleCount σ k` is $j_k(\sigma)$: for $k = 1$ it is the number of fixed points of $\sigma$, for $k \ge 2$ it is the multiplicity of $k$ in Mathlib's `Equiv.Perm.cycleType` (which lists only the cycles of length at least $2$). The variables are indexed by `Fin r`, $r$ = `Fintype.card S`, the index `i` standing for $x_{i+1}$. $G$ is a `Subgroup (Equiv.Perm S)`, and $|G|$ is `Nat.card G` $\ge 1$, so the factor $1/|G|$ is never a division by zero. The cycle index is defined from cycle structure only, not from colorings or orbits.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 299–301, Section 15.4.1

import Mathlib

namespace AppliedComb.Polya

open MvPolynomial

/-- Keller–Trotter, Section 15.4.1 (p. 299). For a permutation `σ` of a finite set `S` and
`k ≥ 1`, `cycleCount σ k` is `j_k`, the number of cycles of length `k` in the cycle notation of
`σ` (Section 15.2.1). Fixed points are cycles of length `1` (the book writes `π = (1245)(3)`),
so `j_1` is the number of fixed points; Mathlib's `Equiv.Perm.cycleType` omits them and lists
only the cycles of length `≥ 2`. -/
def cycleCount {S : Type*} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S) (k : ℕ) : ℕ :=
  if k = 1 then Fintype.card {x : S // σ x = x} else σ.cycleType.count k

/-- Keller–Trotter, Section 15.4.1 (p. 299). The monomial associated with a permutation `σ` of
an `r`-element set `S` (`r = |S|`) with `j_k` cycles of length `k` for `1 ≤ k ≤ r`:
`x_1^{j_1} x_2^{j_2} ⋯ x_r^{j_r}`. The variable `X i` with index `i : Fin r` stands for
`x_{i+1}`. -/
noncomputable def cycleMonomial {S : Type*} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S) :
    MvPolynomial (Fin (Fintype.card S)) ℚ :=
  ∏ i : Fin (Fintype.card S), X i ^ cycleCount σ (i.val + 1)

open Classical in
/-- Keller–Trotter, Section 15.4.1 (pp. 300–301). The cycle index `P_G(x_1, …, x_r)` of a
permutation group `G` of a finite set `S` with `|S| = r` (Section 15.2: a set of permutations of
`S` containing the identity and closed under composition and inverses, i.e. a subgroup of
`Equiv.Perm S`): the average, over the permutations `σ ∈ G`, of the monomials
`x_1^{j_1(σ)} ⋯ x_r^{j_r(σ)}` associated with them,
`P_G = (1/|G|) ∑_{σ ∈ G} x_1^{j_1(σ)} ⋯ x_r^{j_r(σ)}`, a polynomial with rational coefficients
in the `r` variables `x_1, …, x_r`. -/
noncomputable def cycleIndex {S : Type*} [Fintype S] [DecidableEq S]
    (G : Subgroup (Equiv.Perm S)) : MvPolynomial (Fin (Fintype.card S)) ℚ :=
  (Nat.card G : ℚ)⁻¹ • ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm S => σ ∈ G), cycleMonomial σ

end AppliedComb.Polya


