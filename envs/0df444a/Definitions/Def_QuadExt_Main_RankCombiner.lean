-- Prove2me | Definitions.Def_QuadExt_Main_RankCombiner
-- name    : QuadExt_Main_RankCombiner
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:02:53.056696+00:00
-- url     : https://prove2.me/theorems/89d9b20c-dc87-4cb2-b8c9-050c1f69855e
-- title:
--   Sidon sets, $(d, r, \varepsilon)$-rank combiners (Definition 8.2), and the constructions of Theorems 8.5 and 8.9
-- statement:
--   A finite set $S \subseteq \mathbb N$ is a **Sidon set** if $|S + S| \ge \binom{|S|}{2} + |S|$, where $S + S = \{a + b : a, b \in S\}$.
--
--   **Rank combiner (Definition 8.2).** Matrices $W_1, \dots, W_N \in F^{m \times n}$ over a field $F$ ($N \ge 1$) form a **$(d, r, \varepsilon)$-rank combiner** if for every $k \ge 1$ and all $G_1, \dots, G_n \in F^{k \times k}$ with $\dim \operatorname{span}\{G_i y\}_{i \in [n]} \ge d$ for every non-zero $y \in F^k$, with probability at least $1 - \varepsilon$ over a uniform $t \in [N]$,
--   $$\operatorname{rank}_F\Big(\sum_{i=1}^n (c^\top W_t)_i\, G_i\Big) \ge r \quad\text{for all non-zero } c \in F^m. \qquad (10)$$
--   $m$ is the output length and $N$ the size. The square matrices have size $k \ge 1$: for $k = 0$ the premise holds vacuously while every rank is $0$, so no family with $r > 0$, $\varepsilon < 1$, $m \ge 1$ would qualify and Theorems 8.5, 8.9, 8.11 would be false.
--
--   **Large-field construction (proof of Theorem 8.5).** For field elements $\lambda_1, \dots, \lambda_n$ and weights $w_1, \dots, w_n$, the family $\{W(\beta)\}_{\beta \in F}$ with $(W(\beta))_{ji} = \lambda_i^{j-1} \beta^{w_i}$.
--
--   **Field-size reduction (proof of Theorem 8.9).** For a basis $e_1, \dots, e_h$ of $\mathbb F_{2^h}$ over $\mathbb F_2$ write $U = \sum_j M_j(U) e_j$ with $M_j(U) \in \mathbb F_2^{m \times n}$, stack $M(U) = (M_1(U); \dots; M_h(U)) \in \mathbb F_2^{hm \times n}$, let $L_s \in \mathbb F_2^{m' \times hm}$ be the matrix of $\mathrm{LExt}(\cdot, s)$, and set $W(i, s) = L_s M(U_i)$ for $i \in [N]$, $s \in \{0,1\}^\ell$.
--
--   **Formalization Note.** Matrix indices are 0-based (`Fin m`, `Fin n`), so $\lambda_i^{j-1}$ is $\lambda_i^j$ for `j : Fin m`. The family is indexed by any finite non-empty type (`Fin N`, the field `F` itself, or `Fin N × 𝔽₂^ℓ`); the probability is the count $\#\{\text{good } t\} \ge (1 - \varepsilon) N$. The size of $G_i$ is quantified over every $k$. In `fieldReduce`, row $(j, \rho)$ of $M(U)$ is at position $\rho + m j$ (block $j$ of the stack), and column $b$ of $L_s M(U_i)$ is computed as $\mathrm{LExt}(\text{column } b \text{ of } M(U_i), s)$, which is the same matrix because $\mathrm{LExt}(\cdot, s)$ is linear.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 3 (PDF 4), Sidon set; p. 25 (PDF 26), Definition 8.2; p. 26 (PDF 27), proof of Theorem 8.5; p. 29 (PDF 30), proof of Theorem 8.9

import Mathlib

namespace QuadExt.Main

/-!
# Sidon sets, rank combiners, and the two rank-combiner constructions of §8

Chandrasekaran, Goodman, Zuckerman, *Quadratic Extractors*, STOC 2027 submission (manuscript
sha256 ddc80a9a…): Sidon set, §2, p. 3 (PDF 4); Definition 8.2, p. 25 (PDF 26); the large-field
construction `(W(β))_{ji} = λ_i^{j−1} β^{w_i}` in the proof of Theorem 8.5, p. 26 (PDF 27); the
field-size reduction `W(i, s) = L_s M(U_i)` in the proof of Theorem 8.9, p. 29 (PDF 30).

Row and column indices are 0-based (`Fin m`, `Fin n`), so the paper's `λ_i^{j−1}` (`j ∈ [m]`) is
`λ_i^j` for `j : Fin m`.
-/

/-- A **Sidon set** (§2, p. 3): a finite `S ⊆ ℕ` with `|S + S| ≥ (|S| choose 2) + |S|`, where
`S + S = {a + b | a ∈ S, b ∈ S}`. -/
def IsSidon (S : Finset ℕ) : Prop :=
  S.card.choose 2 + S.card ≤ ((S ×ˢ S).image fun p => p.1 + p.2).card

open Classical in
/-- A **`(d, r, ε)`-rank combiner** over a field `F` (Definition 8.2): matrices `W_t ∈ F^{m×n}`,
`t` ranging over a finite index set of size `N`, such that for **every** size `k ≥ 1` and all
`G_1, …, G_n ∈ F^{k×k}` with `dim span{G_i y}_{i∈[n]} ≥ d` for every non-zero `y ∈ F^k`, with
probability at least `1 − ε` over a uniform `t`,
`rank_F(Σ_i (c^⊤ W_t)_i G_i) ≥ r` for all non-zero `c ∈ F^m` (Equation (10)).
`m` is the output length and `N ≥ 1` the size (a uniform `t ∈ [N]` must exist). The size `k`
of the square matrices is at least `1`: at `k = 0` the premise holds vacuously while every rank is
`0`, so no family with `r > 0`, `ε < 1` and `m ≥ 1` could satisfy the condition. -/
def IsRankCombiner {F : Type} [Field F] {ι : Type} [Fintype ι] {m n : ℕ} (d : ℕ) (r ε : ℝ)
    (W : ι → Matrix (Fin m) (Fin n) F) : Prop :=
  0 < Fintype.card ι ∧ ∀ (k : ℕ), 0 < k → ∀ G : Fin n → Matrix (Fin k) (Fin k) F,
    (∀ y : Fin k → F, y ≠ 0 →
      d ≤ Module.finrank F (Submodule.span F (Set.range fun i => Matrix.mulVec (G i) y))) →
    (1 - ε) * (Fintype.card ι : ℝ) ≤
      ((Finset.univ.filter fun t => ∀ c : Fin m → F, c ≠ 0 →
          r ≤ ((∑ i, Matrix.vecMul c (W t) i • G i).rank : ℝ)).card : ℝ)

/-- The **large-field construction** of Theorem 8.5 (p. 26): for `β ∈ F`,
`(W(β))_{ji} = λ_i^{j−1} β^{w_i}` (0-based row index `j`), from field elements `λ_i` and weights
`w_i`. The family `{W(β)}_{β∈F}` has size `|F|`. -/
def largeFieldCombiner {F : Type} [Field F] {m n : ℕ} (lam : Fin n → F) (w : Fin n → ℕ) :
    F → Matrix (Fin m) (Fin n) F :=
  fun β => Matrix.of fun j i => lam i ^ (j : ℕ) * β ^ w i

/-- The **field-size reduction** of Theorem 8.9 (p. 29). For a basis `e_1, …, e_h` of `K = 𝔽_{2^h}`
over `𝔽₂`, write `U = Σ_j M_j(U) e_j` with `M_j(U) ∈ 𝔽₂^{m×n}` and stack `M(U) = (M_1(U); …; M_h(U))
∈ 𝔽₂^{hm×n}` (row `(j, ρ)` at position `ρ + m·j`); `L_s` is the matrix of the linear map
`LExt(·, s)`. Then `W(i, s) = L_s M(U_i)`; column `b` of it is `LExt(column b of M(U_i), s)`.
The family is indexed by `[N] × {0,1}^ℓ`, of size `N·2^ℓ`. -/
noncomputable def fieldReduce {K : Type} [Field K] [Algebra (ZMod 2) K] {h m n N ℓ m' : ℕ}
    (e : Module.Basis (Fin h) (ZMod 2) K)
    (LExt : (Fin (h * m) → ZMod 2) → (Fin ℓ → ZMod 2) → (Fin m' → ZMod 2))
    (U : Fin N → Matrix (Fin m) (Fin n) K) :
    Fin N × (Fin ℓ → ZMod 2) → Matrix (Fin m') (Fin n) (ZMod 2) :=
  fun p => Matrix.of fun a b =>
    LExt (fun idx => e.repr (U p.1 (finProdFinEquiv.symm idx).2 b) (finProdFinEquiv.symm idx).1) p.2 a

end QuadExt.Main


