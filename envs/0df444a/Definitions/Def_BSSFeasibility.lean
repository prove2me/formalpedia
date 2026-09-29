-- Prove2me | Definitions.Def_BSSFeasibility
-- name    : BSSFeasibility
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T14:56:44.663924+00:00
-- url     : https://prove2.me/theorems/66223d3f-dc2f-4627-b9ba-2ede0d70677b
-- title:
--   The 4-Feasibility problem and the powerfree representation (§5)
-- statement:
--   The 4-Feasibility problem $(F, F_{\mathrm{yes}})$ and the powerfree representation of §5 (p. 26).
--
--   A polynomial $f : \mathbb{R}^n \to \mathbb{R}$ of degree at most $4$ is powerfreely represented in
--   $\mathbb{R}^\infty$ as the header $(4, n)$ followed by blocks
--   $(\alpha_1, \alpha_2, \alpha_3, \alpha_4, a_\alpha)$ of five entries, with
--   $\alpha_t \in \{0, \dots, n\}$ natural numbers satisfying
--   $\alpha_1 \le \alpha_2 \le \alpha_3 \le \alpha_4$, the blocks listed in increasing lexicographic
--   order of $\alpha$. The block stands for the monomial
--   $a_\alpha x_{\alpha_1} x_{\alpha_2} x_{\alpha_3} x_{\alpha_4}$, with $x_0 = 1$ to allow terms of
--   degree less than $4$, and $f$ is the sum of these monomials.
--
--   $F$ is the set of such codes and $F_{\mathrm{yes}}$ the set of codes whose polynomial has a real
--   zero. The zero is quantified over assignments $\mathbb{N} \to \mathbb{R}$, which is equivalent to
--   quantifying over $\mathbb{R}^n$ since only $x_1, \dots, x_n$ occur.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §5, p. 26

import Definitions.Def_BSSComplexity

/-!
# The 4-Feasibility problem over the reals (Blum–Shub–Smale, §5)

Formalization of the decision problem `(F, F_yes)` of

  L. Blum, M. Shub, S. Smale, *On a theory of computation and complexity over the
  real numbers: NP-completeness, recursive functions and universal machines*,
  Bull. Amer. Math. Soc. **21** (1989), no. 1, 1–46, §5, p. 26,

together with the powerfree representation of degree `≤ 4` polynomials in `ℝ^∞`
described there.

A polynomial `f : ℝⁿ → ℝ` of degree `≤ 4` is powerfreely represented in `ℝ^∞` as
`(4, n)` followed by a sequence of blocks `(α, a_α)`, where `α = (α₁, α₂, α₃, α₄)`
with `αᵢ ∈ {0, …, n}` and `αᵢ ≤ αᵢ₊₁`, and `a_α ∈ ℝ`. The block `(α, a_α)` stands
for the monomial `a_α x_{α₁} x_{α₂} x_{α₃} x_{α₄}`, with the convention `x₀ = 1`,
and the blocks are ordered by the lexicographic order on `α`.
-/

namespace BSS

/-- The number of monomial blocks of a powerfree code `w`: the entries of `w`
after the two header entries, grouped five at a time. -/
noncomputable def numBlocks (w : Rinf ℝ) : ℕ := (lengthInf w - 2) / 5

/-- The `t`-th exponent index of the `t`-th block of a powerfree code. -/
noncomputable def blockExp (w : Rinf ℝ) (b t : ℕ) : ℕ := ⌊w (2 + 5 * b + t)⌋₊

/-- The coefficient `a_α` of block `b` of a powerfree code. -/
noncomputable def blockCoeff (w : Rinf ℝ) (b : ℕ) : ℝ := w (2 + 5 * b + 4)

/-- The exponent multi-index of block `b`, as a list of four indices. -/
noncomputable def blockIndex (w : Rinf ℝ) (b : ℕ) : List ℕ :=
  List.ofFn (fun t : Fin 4 => blockExp w b t)

/-- `w ∈ ℝ^∞` is a powerfree representation of a polynomial `ℝⁿ → ℝ` of degree
`≤ 4`, for some `n` (BSS §5, p. 26). -/
def IsPowerfreeCode (w : Rinf ℝ) : Prop :=
  ∃ n : ℕ,
    w 0 = 4 ∧ w 1 = (n : ℝ) ∧
    lengthInf w = 2 + 5 * numBlocks w ∧
    (∀ b < numBlocks w, ∀ t < 4,
        w (2 + 5 * b + t) = ((blockExp w b t : ℕ) : ℝ) ∧ blockExp w b t ≤ n) ∧
    (∀ b < numBlocks w, ∀ t < 3, blockExp w b t ≤ blockExp w b (t + 1)) ∧
    (∀ b : ℕ, b + 1 < numBlocks w →
        List.Lex (· < ·) (blockIndex w b) (blockIndex w (b + 1)))

/-- The value at the point `x` of the polynomial powerfreely represented by `w`,
with the convention `x₀ = 1` that allows terms of degree less than `4`. -/
noncomputable def feasValue (w : Rinf ℝ) (x : ℕ → ℝ) : ℝ :=
  ∑ b ∈ Finset.range (numBlocks w),
    blockCoeff w b *
      ∏ t ∈ Finset.range 4, (if blockExp w b t = 0 then (1 : ℝ) else x (blockExp w b t))

/-- The instance space `F` of the 4-Feasibility problem: the powerfree
representations of polynomials of degree `≤ 4` (BSS §5, p. 26). -/
def Feas4 : Set (Rinf ℝ) := {w : Rinf ℝ | IsPowerfreeCode w}

/-- The yes-instances `F_yes` of the 4-Feasibility problem: those `f ∈ F` having a
real zero (BSS §5, p. 26). -/
def Feas4Yes : Set (Rinf ℝ) :=
  {w : Rinf ℝ | IsPowerfreeCode w ∧ ∃ x : ℕ → ℝ, feasValue w x = 0}

end BSS


