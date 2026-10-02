-- Prove2me | Definitions.Def_Disjunctive_HigherDim_Lifts
-- name    : Disjunctive_HigherDim_Lifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:37:55.393873+00:00
-- url     : https://prove2.me/theorems/fdcf672a-f337-4736-8347-153e24aa2157
-- title:
--   The Lovász-Schrijver lift M(K)/N(K) and the Sherali-Adams lift Xt/Kt
-- statement:
--   This definition fixes the two competing higher-dimensional lift constructions of
--   Sections 7.2 and 7.3, each ending in a projection back to the $x$-space.
--
--   **Lovász-Schrijver.** `MK A b N'` is $M(K)$ (eq. (7.4), Step 2): pairs $(x,Y)$ with $Y$ symmetric,
--   $Y_{jj} = x_j$ for every $j \in N'$, and, for every $j \in N'$ simultaneously, the two linearized
--   inequality families obtained from multiplying $\tilde A x \ge \tilde b$ by $(1-x_j)$ and $x_j$
--   and substituting $Y_{ij}$ for $x_i x_j$. `NOp A b N'` is $N(K) := \{x : \exists Y,\ (x,Y) \in
--   M(K)\}$, the projection of Step 3. Iterating, $N^1(K) := N(K)$, $N^t(K) := N(N^{t-1}(K))$
--   (formalized directly as the `hStep` hypothesis of `lovasz_schrijver_reaches_hull` rather than as a
--   named iteration operator, since each step's ambient representation $(A_t,b_t)$ genuinely changes).
--
--   **Sherali-Adams.** For a subset $J$ of the 0-1 index set and a "moment" function $w : \mathrm{Finset}
--   (\mathrm{Fin}\ n) \to \mathbb R$ (standing for $w_J = \prod_{j\in J} x_j$) together with $v :
--   \mathrm{Finset}(\mathrm{Fin}\ n) \to \mathrm{Fin}\ n \to \mathbb R$ (standing for $v_{J,k} =
--   x_k \prod_{j \in J} x_j$, $k$ outside the 0-1 block), `MomentEval N' w v J k` evaluates the
--   moment of $\{k\} \cup J$: $w(J \cup \{k\})$ if $k \in N'$ (idempotent, $x_k$ already a factor
--   of the monomial), $v_J(k)$ otherwise. `RowNLt A b N' w v i J1 J2` is row $i$'s linearized version of
--   the multiplier $\prod_{j \in J_1} x_j \prod_{j \in J_2}(1-x_j)$ applied to row $i$ of $\tilde A
--   x \ge \tilde b$ (Step 1's (NL_t)), obtained by expanding every $(1-x_j)$ factor via
--   inclusion-exclusion over subsets $S \subseteq J_2$ and linearizing each resulting monomial via
--   `MomentEval`. `IsXt A b N' t x w v` says $(x,w,v)$ represents a point of $X_t$: $w$ normalized
--   ($w_\emptyset = 1$, $w_{\{j\}} = x_j$ for $j \in N'$), and every level-$t$ row (every disjoint
--   $J_1,J_2 \subseteq N'$ with $|J_1 \cup J_2| = t$) nonnegative. `KtSet A b N' t` is $K_t := \{x :
--   \exists w, v,\ \mathrm{IsXt}\ A\ b\ N'\ t\ x\ w\ v\}$, the projection of Step 3.
--
--   **Formalization Note (see `MODERATION_NOTES.md`).** The book states Step 1 of the Sherali-Adams
--   construction narratively (multiply by every product of $t$ literals, positive or negated) rather
--   than displaying (NL_t) as an explicit linear system, unlike every other construction in this
--   chapter. `RowNLt` derives the unique linearization such a system has via inclusion-exclusion
--   expansion of $\prod_{j\in J_2}(1-x_j)$ — a mechanical consequence of the book's own Step 1/Step 2
--   instructions, not an independent construction choice.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 93-94, Section 7.2-7.3

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic

namespace Disjunctive.HigherDim

/-- `M(K)`, the Lovász-Schrijver lifted polyhedron (Balas §7.2, p. 92-93, eq. (7.4)): a
symmetric matrix `Y` with `Y_{jj} = x_j` for `j ∈ N'`, satisfying the linearized system for
every `j ∈ N'` simultaneously. -/
def MK {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n)) :
    Set ((Fin n → ℝ) × (Fin n → Fin n → ℝ)) :=
  {p | (∀ i j, p.2 i j = p.2 j i) ∧ (∀ j ∈ Nprime, p.2 j j = p.1 j) ∧
        ∀ j ∈ Nprime, (∀ i, 0 ≤ (A.mulVec p.1) i - (A.mulVec (fun k => p.2 k j)) i + b i * (p.1 j - 1)) ∧
          ∀ i, 0 ≤ (A.mulVec (fun k => p.2 k j)) i - b i * p.1 j}

/-- `N(K)`, the projection of `M(K)` onto the `x`-space (Balas §7.2, p. 93, Step 3). -/
def NOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {x | ∃ Y, (x, Y) ∈ MK A b Nprime}

/-- The moment substitution for one variable `k` against a subset `J` of `N'`: `w(J ∪ {k})` if
`k ∈ N'` (idempotent product, `x_k` already in the monomial), `v_J(k)` otherwise (Balas §7.3,
p. 94, Step 2). -/
def MomentEval {n : ℕ} (Nprime : Finset (Fin n)) (w : Finset (Fin n) → ℝ)
    (v : Finset (Fin n) → Fin n → ℝ) (J : Finset (Fin n)) (k : Fin n) : ℝ :=
  if k ∈ Nprime then w (insert k J) else v J k

/-- Row `i`'s linearized Sherali-Adams inequality for the multiplier `∏_{j∈J1} x_j ·
∏_{j∈J2}(1-x_j)`, obtained by expanding the `(1-x_j)` factors via inclusion-exclusion over
subsets `S ⊆ J2` (Balas §7.3, p. 94, Step 1-2). -/
def RowNLt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n))
    (w : Finset (Fin n) → ℝ) (v : Finset (Fin n) → Fin n → ℝ) (i : Fin m)
    (J1 J2 : Finset (Fin n)) : ℝ :=
  ∑ S ∈ J2.powerset, (-1 : ℝ) ^ S.card *
    ((∑ k, A i k * MomentEval Nprime w v (J1 ∪ S) k) - b i * w (J1 ∪ S))

/-- `(x,w,v)` represents a point of the lifted Sherali-Adams polyhedron `X_t` at level `t`
(Balas §7.3, p. 94): `w` normalized (`w ∅ = 1`, `w {j} = x_j`), the continuous variables tied to
the lift at the empty monomial (`v_∅(k) = x_k` for `k ∉ N'`, since `v_J(k)` linearizes
`x_k ∏_{j ∈ J} x_j` and `J = ∅` leaves `x_k`), and every level-`t` linearized inequality
nonnegative. Without the tie the continuous coordinates are free of the lift and `K_t` is far
larger than the page's set: for `K = {0 ≤ x₁ ≤ 1, x₂ ≤ 3}`, `N' = {1}`, `t = 1`, the point
`(0.5, 100)` would lie in `K_1` while `conv(K ∩ {x₁ ∈ {0,1}}) ⊆ {x₂ ≤ 3}`. -/
def IsXt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n))
    (t : ℕ) (x : Fin n → ℝ) (w : Finset (Fin n) → ℝ) (v : Finset (Fin n) → Fin n → ℝ) : Prop :=
  w ∅ = 1 ∧ (∀ j ∈ Nprime, w {j} = x j) ∧ (∀ k ∉ Nprime, v ∅ k = x k) ∧
    ∀ i (J1 J2 : Finset (Fin n)), Disjoint J1 J2 → J1 ⊆ Nprime → J2 ⊆ Nprime →
      (J1 ∪ J2).card = t → 0 ≤ RowNLt A b Nprime w v i J1 J2

/-- `K_t`, the projection of `X_t` onto the `x`-space (Balas §7.3, p. 94, Step 3). -/
def KtSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n))
    (t : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ w v, IsXt A b Nprime t x w v}

end Disjunctive.HigherDim


