-- Prove2me | Definitions.Def_KTCenter_Rounding
-- name    : KTCenter_Rounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:54.049377+00:00
-- url     : https://prove2.me/theorems/a8e5100a-5595-4182-a395-9733d4f2a2f7
-- title:
--   The rounding distribution, $\mu_i$, conditional means $M^j_i$, the potential $\Phi_j$ (79) and runs of Algorithm 11
-- statement:
--   A feasible solution of (LP1) defines a random assignment: keys on $F$ are $\varphi$; large-block keys are independent with marginals $x$; each small block $B$ selects $h$ with probability $z_{Bh}$ and then draws its keys independently with marginals $y^{Bh}/z_{Bh}$; blocks are independent. $\mu_i$ is the expected surrogate cost. Choices are ordered with all small-block indices first, then residual keys; $M^j_i$ is the conditional expected cost after the first $j$ choices; $b_j=L_B$ for an index choice and $\lambda_v$ for a key choice; $a=\gamma W$, $t_r=8\ell/a$ (78), and
--
--   $$\Phi_j=\sum_{i=1}^n\exp\Bigl(t_r(M^j_i-\mu_i-a)+\frac{t_r^2}{8}\sum_{k=j+1}^m b_k^2\Bigr).\qquad(79)$$
--
--   A **run** of Algorithm 11 fixes, at each step, an outcome of positive conditional probability with smallest approximate potential, the approximation being within $1/(8m)$ of $\Phi$.
--
--   **Formalization Note** Expectations are finite sums over outcomes; a conditional mean is a quotient of two finite sums and is used only at prefixes of positive probability. Division by $z_{Bh}$ occurs only under the factor $z_{Bh}$.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §5.5 p.49 (PDF p.51), §6.1, eqs. (76)–(79), Algorithm 11, pp.58–59 (PDF pp.60–61)

import Mathlib
import Definitions.Def_KTCenter_LP1

namespace KTCenter

namespace CostInstance

section

open Classical

variable {K : ℕ} {C₀ C₁ : ℚ} (I : CostInstance K C₀ C₁) (ξ : ℚ)

/-- **An outcome of the rounding distribution**, p.49 (PDF p.51): one index `h ∈ G_B` for each small
subset, and keys on `U′`.

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…), §§5.5, 6.1. -/
abbrev Outcome (fam : I.SmallFamily ξ) : Type :=
  ((B : {B // B ∈ I.bSmall ξ}) → Fin (fam B).length) × I.AssignOn (I.Ures ξ)

variable {I ξ} {fam : I.SmallFamily ξ}

/-- **The probability of an outcome**, p.49: keys on `F` are `φ`; large-subset keys are independent
with marginals `x`; each small subset selects `h` with probability `z_{Bh}`, then draws its keys
independently with conditional marginals `y^{Bh}/z_{Bh}`; choices of different subsets are
independent.

**Formalization Note.** Division occurs only under the factor `z_{Bh}`: when `z_{Bh} = 0` the whole
product is `0`, whatever `0/0` is, so the convention `0/0 = 0` plays no role. -/
noncomputable def prob (φ : I.AssignOn (I.F ξ)) (P : I.LPPoint ξ fam) (ω : I.Outcome ξ fam) : ℝ :=
  (∏ B : {B // B ∈ I.bSmall ξ}, P.z B (ω.1 B)) *
    (∏ v ∈ I.Uell ξ, P.x v (I.union ξ φ ω.2 v)) *
    ∏ B : {B // B ∈ I.bSmall ξ}, ∏ v ∈ B.1,
      (P.y B (ω.1 B) v (I.union ξ φ ω.2 v) / P.z B (ω.1 B))

/-- `µᵢ = E[C̃ᵢ(p)]`, p.49 (PDF p.51): the finite sum over outcomes. -/
noncomputable def mu (φ : I.AssignOn (I.F ξ)) (P : I.LPPoint ξ fam) (i : Fin I.n) : ℝ :=
  ∑ ω : I.Outcome ξ fam, prob φ P ω * (I.cost i (I.union ξ φ ω.2) : ℝ)

variable (I ξ) in
/-- A rounding choice, p.58: the index of a small subset, or the key of a residual candidate. -/
abbrev Choice : Type := {B // B ∈ I.bSmall ξ} ⊕ {v // v ∈ I.Ures ξ}

variable (I ξ) in
/-- `m = |ℬ_s| + |U′|`, the number of choices, p.59 (PDF p.61). -/
def numChoices : ℕ := (I.bSmall ξ).card + (I.Ures ξ).card

/-- The small-subset indices come first and then the residual keys, p.58. -/
def IndicesFirst (ord : Fin (numChoices I ξ) ≃ Choice I ξ) : Prop :=
  ∀ j j' : Fin (numChoices I ξ), j < j' → (ord j').isLeft = true → (ord j).isLeft = true

/-- Two outcomes make the same choice `c`. -/
def SameChoice (c : Choice I ξ) (ω ω' : I.Outcome ξ fam) : Prop :=
  match c with
  | Sum.inl B => ω.1 B = ω'.1 B
  | Sum.inr v => ω.2 v = ω'.2 v

/-- Two outcomes share the prefix of the first `j` choices. -/
def SamePrefix (ord : Fin (numChoices I ξ) ≃ Choice I ξ) (j : ℕ) (ω ω' : I.Outcome ξ fam) : Prop :=
  ∀ j' : Fin (numChoices I ξ), (j' : ℕ) < j → SameChoice (ord j') ω ω'

/-- The probability of the prefix of the first `j` choices of `ω`. -/
noncomputable def prefixMass (φ : I.AssignOn (I.F ξ)) (P : I.LPPoint ξ fam)
    (ord : Fin (numChoices I ξ) ≃ Choice I ξ) (j : ℕ) (ω : I.Outcome ξ fam) : ℝ :=
  ∑ ω' : I.Outcome ξ fam, if SamePrefix ord j ω ω' then prob φ P ω' else 0

/-- `M^j_i`, p.58 (PDF p.60): the conditional expected cost of input `i` after the prefix of `j`
choices of `ω`; the quotient of two finite sums.

**Formalization Note.** Used at prefixes of positive probability only. -/
noncomputable def condMean (φ : I.AssignOn (I.F ξ)) (P : I.LPPoint ξ fam)
    (ord : Fin (numChoices I ξ) ≃ Choice I ξ) (j : ℕ) (ω : I.Outcome ξ fam) (i : Fin I.n) : ℝ :=
  (∑ ω' : I.Outcome ξ fam, if SamePrefix ord j ω ω' then
      prob φ P ω' * (I.cost i (I.union ξ φ ω'.2) : ℝ) else 0) / prefixMass φ P ord j ω

/-- The range bound of a choice, p.59: `b = L_B` for an index choice in `B`, `b = λ_v` for a key
choice at `v`. -/
def rangeBound (c : Choice I ξ) : ℚ :=
  match c with
  | Sum.inl B => I.LB B.1
  | Sum.inr v => I.lam v.1

variable (I ξ) in
/-- `a = γW`, eq. (78), p.59. -/
def aParam : ℚ := gamma ξ * I.W

variable (I ξ) in
/-- `t_r = 8ℓ/a`, eq. (78), p.59. -/
def trParam : ℚ := 8 * (I.ell : ℚ) / aParam I ξ

/-- **The potential**, eq. (79), p.59 (PDF p.61):
`Φ_j = Σᵢ exp(t_r(M^j_i − µᵢ − a) + (t_r²/8) Σ_{k=j+1}^m b_k²)`.

**Formalization Note.** With 0-based choice indices, the source's `k = j+1, …, m` are the indices
`k ≥ j`. -/
noncomputable def Phi (φ : I.AssignOn (I.F ξ)) (P : I.LPPoint ξ fam)
    (ord : Fin (numChoices I ξ) ≃ Choice I ξ) (j : ℕ) (ω : I.Outcome ξ fam) : ℝ :=
  ∑ i : Fin I.n, Real.exp
    ((trParam I ξ : ℝ) * (condMean φ P ord j ω i - mu φ P i - (aParam I ξ : ℝ)) +
      (trParam I ξ : ℝ) ^ 2 / 8 *
        ∑ k ∈ Finset.univ.filter (fun k : Fin (numChoices I ξ) => j ≤ (k : ℕ)),
          (rangeBound (ord k) : ℝ) ^ 2)

/-- **An evaluator of the potential**, Algorithm 11, line 6, p.59: a function of the prefix that is
within `1/(8m)` of `Φ` at every prefix of positive probability. -/
def IsEvaluator (φ : I.AssignOn (I.F ξ)) (P : I.LPPoint ξ fam)
    (ord : Fin (numChoices I ξ) ≃ Choice I ξ) (Ψ : ℕ → I.Outcome ξ fam → ℝ) : Prop :=
  (∀ j ω ω', SamePrefix ord j ω ω' → Ψ j ω = Ψ j ω') ∧
  ∀ j ω, 0 < prefixMass φ P ord j ω →
    |Ψ j ω - Phi φ P ord j ω| ≤ 1 / (8 * (numChoices I ξ : ℝ))

/-- **A run of Algorithm 11**, p.59: at each step the outcome has positive conditional probability
and has a smallest approximate potential among the outcomes of positive conditional probability.

**Formalization Note.** The tie-break is left free, so this covers every fixed order of line 7. -/
def IsRun (φ : I.AssignOn (I.F ξ)) (P : I.LPPoint ξ fam)
    (ord : Fin (numChoices I ξ) ≃ Choice I ξ) (Ψ : ℕ → I.Outcome ξ fam → ℝ)
    (ω : I.Outcome ξ fam) : Prop :=
  ∀ j : Fin (numChoices I ξ), 0 < prefixMass φ P ord ((j : ℕ) + 1) ω ∧
    ∀ ω' : I.Outcome ξ fam, SamePrefix ord j ω ω' → 0 < prefixMass φ P ord ((j : ℕ) + 1) ω' →
      Ψ ((j : ℕ) + 1) ω ≤ Ψ ((j : ℕ) + 1) ω'

end

end CostInstance

end KTCenter


