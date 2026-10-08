-- Prove2me | Definitions.Def_EdgeTransBiCayley_BiDihedrant_Gamma
-- name    : EdgeTransBiCayley_BiDihedrant_Gamma
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:29.852976+00:00
-- url     : https://prove2.me/theorems/c2fb9902-fdfc-4cc8-917f-0731da8fce89
-- title:
--   Example 6.2, pp. 12–13 — the bi-dihedrants Γ(n, λ, 2k) and their hypotheses
-- statement:
--   Let $D_n = \langle a, b \mid a^n = b^2 = (ab)^2 = 1\rangle$ be the dihedral group of degree $n$ and order $2n$. For natural numbers $\lambda$ and $i$ put
--
--   $$
--   c_i = 1 + \lambda^2 + \lambda^4 + \cdots + \lambda^{2i}, \qquad d_i = \lambda c_i = \lambda + \lambda^3 + \cdots + \lambda^{2i+1},
--   $$
--
--   read modulo $n$ as exponents of $a$. The **connection set** and the graph of Example 6.2 are
--
--   $$
--   S(n,\lambda,2k) = \{a^{c_i} : i \in \mathbb Z_k\} \cup \{ba^{d_i} : i \in \mathbb Z_k\}, \qquad \Gamma(n,\lambda,2k) = \mathrm{BiCay}(D_n, \emptyset, \emptyset, S(n,\lambda,2k)).
--   $$
--
--   The example is stated under the hypotheses: $n \ge 5$, $k \ge 2$, $\lambda$ is an element of order $2k$ in $\mathbb Z_n^*$, and
--
--   $$
--   1 + \lambda^2 + \lambda^4 + \cdots + \lambda^{2(k-1)} \equiv 0 \pmod n.
--   $$
--
--   These graphs give the semisymmetric bi-dihedrants of valency $2k$ for odd $k$ in Theorem 1.5.
--
--   **Formalization Note** $D_n$ is Mathlib's `DihedralGroup n`, with $a = $ `r 1`, $b = $ `sr 0`, so $a^c = $ `r c` and $ba^d = $ `sr d`. $\lambda$ is a natural number `lam` (the word `λ` is reserved in Lean) and enters through its residue in `ZMod n`. The index set $\mathbb Z_k$ is enumerated as $0 \le i < k$. The hypotheses are collected in the predicate `Ex62Hyp n lam k`; the graph itself is defined for all parameters. In `Ex62Hyp`, `orderOf` is computed in the monoid `ZMod n`, where a non-unit has order $0$, so the condition "order $2k$" with $k \ge 2$ forces $\lambda \in \mathbb Z_n^*$.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, pp. 12–13, Example 6.2

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiDihedrant_Setting
open Pointwise

namespace EdgeTransBiCayley.BiDihedrant

/-- Example 6.2, p. 12: `cᵢ = 1 + λ² + λ⁴ + ⋯ + λ²ⁱ` (as a natural number, read mod `n`). -/
def cParam (lam i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (i + 1), lam ^ (2 * j)

/-- Example 6.2, p. 12: `dᵢ = λ cᵢ = λ + λ³ + ⋯ + λ²ⁱ⁺¹`. -/
def dParam (lam i : ℕ) : ℕ := lam * cParam lam i

/-- Example 6.2, p. 13: `S(n, λ, 2k) = {a^{cᵢ} : i ∈ ℤ_k} ∪ {ba^{dᵢ} : i ∈ ℤ_k}` in
`Dₙ = DihedralGroup n`, where `a = r 1`, `b = sr 0`, `a^c = r c` and `ba^d = sr d`. -/
def gammaS (n lam k : ℕ) : Finset (DihedralGroup n) :=
  (Finset.range k).image (fun i => DihedralGroup.r (cParam lam i : ZMod n)) ∪
  (Finset.range k).image (fun i => DihedralGroup.sr (dParam lam i : ZMod n))

/-- Example 6.2, p. 13: the data of `Γ(n, λ, 2k) = BiCay(Dₙ, ∅, ∅, S(n, λ, 2k))`. -/
def gammaData (n lam k : ℕ) : BiCayData (DihedralGroup n) where
  R := ∅
  L := ∅
  S := gammaS n lam k
  inv_R := by simp
  inv_L := by simp
  one_notMem_R := by simp
  one_notMem_L := by simp
  card_R_eq_card_L := rfl

/-- The hypotheses of Example 6.2, p. 12: `n ≥ 5`, `k ≥ 2`, `λ` has order `2k` in `ℤₙ^*`
(`orderOf` in the monoid `ZMod n` is `0` for a non-unit, so `orderOf = 2k > 0` forces `λ` to be a
unit), and `1 + λ² + ⋯ + λ^{2(k-1)} ≡ 0 mod n`. -/
def Ex62Hyp (n lam k : ℕ) : Prop :=
  5 ≤ n ∧ 2 ≤ k ∧ orderOf (lam : ZMod n) = 2 * k ∧
  ∑ j ∈ Finset.range k, (lam : ZMod n) ^ (2 * j) = 0

end EdgeTransBiCayley.BiDihedrant


