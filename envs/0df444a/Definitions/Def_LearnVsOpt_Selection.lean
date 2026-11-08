-- Prove2me | Definitions.Def_LearnVsOpt_Selection
-- name    : LearnVsOpt_Selection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:13.59468+00:00
-- url     : https://prove2.me/theorems/589517a1-41b5-41ab-bb2e-a96e9c5f0880
-- title:
--   Valid responses, tie-breaking rules, and the concrete selector
-- statement:
--   The learner's response to predicted vectors $(u,c)$ is a pair $\vec J=(j_1,j_2)$, the probability $Q\in[0,1]$ of the first action, and a dual multiplier $\lambda$. It is **valid** when:
--
--   1. $y=Q e_{j_1}+(1-Q)e_{j_2}\in\mathrm{BR}_L(u,c)$, and $j_1=j_2$ comes with $Q=0$;
--   2. $0\le\lambda\le1/\rho_L$, and $\lambda$ minimizes the dual objective of (9),
--   $$
--   \lambda\rho_L+\max_{j\in[n_L]}\big(u[j]-\lambda c[j]\big),\qquad \lambda\ge0 .
--   $$
--
--   A **selector** is a charged function of $(u,c)$, the learner's tie-breaking rule. It is valid when its response is valid at every $(u,c)\in[0,1]^{2n_L}$ with $c[j_0]=0$ for the null action $j_0$.
--
--   The concrete selector `vertexSel` enumerates the vertices of the learner's program, the pure actions with $c[j]\le\rho_L$ and the pairs with $c[j]<\rho_L<c[j']$ at weight $q=(c[j']-\rho_L)/(c[j']-c[j])$ on $j$, keeping the first of maximal utility. It takes the first minimizer of (9) among $0$ and the positive breakpoints $(u[j]-u[j'])/(c[j]-c[j'])$.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, §2, p.6; §4, p.8; (9), p.12; (37), p.41; p.22

import Mathlib
import Definitions.Def_LearnVsOpt_BR
import Definitions.Def_LearnVsOpt_Prog

open scoped Matrix

namespace LearnVsOpt

variable {nL : ℕ}

/-- The learner's response to a forecast: the pair `J⃗(f) = (j₁, j₂)`, the probability `Q(f)` of the
first action, and the dual multiplier `λ(f)` (Fikioris, Sivan & Tardos, arXiv:2611.05580, §4, p.8,
and (9), p.12). -/
structure Selection (nL : ℕ) where
  /-- The first action of `J⃗(f)`. -/
  j₁ : Fin nL
  /-- The second action of `J⃗(f)`. -/
  j₂ : Fin nL
  /-- `Q(f)`, the probability of playing `j₁`. -/
  Q : ℝ
  /-- `λ(f)`. -/
  lam : ℝ

/-- The mixed strategy `y(f) = Q(f) e_{j₁} + (1 − Q(f)) e_{j₂}`. -/
def Selection.y (s : Selection nL) : Fin nL → ℝ :=
  fun j => s.Q * (if j = s.j₁ then 1 else 0) + (1 - s.Q) * (if j = s.j₂ then 1 else 0)

/-- The dual objective of (9), p.12: `λρ_L + max_{j ∈ [n_L]} (u[j] − λc[j])`. The argument `j₀` only
witnesses that `[n_L]` is nonempty. -/
noncomputable def dualObj (j₀ : Fin nL) (ρL : ℝ) (u c : Fin nL → ℝ) (lam : ℝ) : ℝ :=
  lam * ρL + Finset.univ.sup' ⟨j₀, Finset.mem_univ j₀⟩ (fun j => u j - lam * c j)

/-- A valid response to `(u, c)` (pp.6, 8, 12): `y = Q e_{j₁} + (1 − Q) e_{j₂} ∈ BR_L(u, c)` with
`Q ∈ [0, 1]`; `J⃗ = (j, j)` comes with `Q = 0`; and `λ` minimizes (9) over `λ ≥ 0` with `λ ≤ 1/ρ_L`. -/
def IsValidSelection (j₀ : Fin nL) (ρL : ℝ) (u c : Fin nL → ℝ) (s : Selection nL) : Prop :=
  s.Q ∈ Set.Icc (0 : ℝ) 1 ∧ s.y ∈ BR ρL u c ∧ (s.j₁ = s.j₂ → s.Q = 0) ∧
    0 ≤ s.lam ∧ s.lam ≤ 1 / ρL ∧
    ∀ lam' : ℝ, 0 ≤ lam' → dualObj j₀ ρL u c s.lam ≤ dualObj j₀ ρL u c lam'

/-- A **selector**: the learner's tie-breaking rule, a charged function of the predicted utility and
cost vectors `(u(f), c(f))` ("breaking ties consistently", Algorithm 1, p.7). -/
abbrev Selector (nL : ℕ) := (Fin nL → ℝ) → (Fin nL → ℝ) → Det (Selection nL)

/-- A selector is valid when its response is valid on every `(u, c) ∈ [0,1]^{2n_L}` in which the null
action `j₀` has cost `0`; every forecast's `(u(f), c(f))` is of this form.

**Formalization Note.** The clauses of the theorems quantify over all valid selectors, since the paper
allows "any consistent tie-breaking rule" (p.8). -/
def IsValidSel (j₀ : Fin nL) (ρL : ℝ) (sel : Selector nL) : Prop :=
  ∀ u c : Fin nL → ℝ, (∀ j, u j ∈ Set.Icc (0 : ℝ) 1) → (∀ j, c j ∈ Set.Icc (0 : ℝ) 1) → c j₀ = 0 →
    IsValidSelection j₀ ρL u c (sel u c).val

open Classical in
/-- The first optimal primal vertex of the learner's two-constraint LP (compare (37), Appendix H, p.41):
the pure actions `j` with `c[j] ≤ ρ_L`, then the pairs with `c[j] < ρ_L < c[j']` and weight
`q = (c[j'] − ρ_L)/(c[j'] − c[j])` on `j`, keeping the first of maximal utility. -/
noncomputable def vertexPrimal (j₀ : Fin nL) (ρL : ℝ) (u c : Fin nL → ℝ) :
    Det ((Fin nL × Fin nL × ℝ) × ℝ) := do
  let init ← opn 2 ((j₀, j₀, (0 : ℝ)), u j₀)
  let b₁ ← foldD (List.finRange nL) (fun b j =>
      opn 4 (if c j ≤ ρL ∧ b.2 < u j then ((j, j, (0 : ℝ)), u j) else b)) init
  foldD (List.finRange nL) (fun b j =>
      foldD (List.finRange nL) (fun b j' =>
        let q := (c j' - ρL) / (c j' - c j)
        let v := q * u j + (1 - q) * u j'
        opn 12 (if c j < ρL ∧ ρL < c j' ∧ b.2 < v then ((j, j', q), v) else b)) b) b₁

open Classical in
/-- The first minimizer of (9) among `λ = 0` and the positive breakpoints
`(u[j] − u[j'])/(c[j] − c[j'])`, `c[j] ≠ c[j']`, evaluating the objective by a scan over `[n_L]`. -/
noncomputable def vertexDual (j₀ : Fin nL) (ρL : ℝ) (u c : Fin nL → ℝ) : Det ℝ := do
  let evalAt := fun lam : ℝ => do
    let m ← foldD (List.finRange nL) (fun b j => opn 3 (max b (u j - lam * c j))) (u j₀ - lam * c j₀)
    opn 2 (lam * ρL + m)
  let v₀ ← evalAt 0
  let b ← foldD (List.finRange nL) (fun b j =>
      foldD (List.finRange nL) (fun b j' => do
        let lam ← opn 6 ((u j - u j') / (c j - c j'))
        if c j ≠ c j' ∧ 0 < lam then do
          let v ← evalAt lam
          opn 1 (if v < b.2 then (lam, v) else b)
        else pure b) b) ((0 : ℝ), v₀)
  pure b.1

/-- **The concrete selector** of the running-time clause: charged vertex enumeration of the learner's
LP and of its dual (p.22, "solves a linear program in `n_L` variables"), with `O(n_L³)` operations. -/
noncomputable def vertexSel (j₀ : Fin nL) (ρL : ℝ) : Selector nL := fun u c => do
  let p ← vertexPrimal j₀ ρL u c
  let lam ← vertexDual j₀ ρL u c
  pure ⟨p.1.1, p.1.2.1, p.1.2.2, lam⟩

end LearnVsOpt


