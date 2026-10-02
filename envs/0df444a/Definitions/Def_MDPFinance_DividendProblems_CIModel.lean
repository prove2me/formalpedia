-- Prove2me | Definitions.Def_MDPFinance_DividendProblems_CIModel
-- name    : MDPFinance_DividendProblems_CIModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:12:23.816909+00:00
-- url     : https://prove2.me/theorems/4608b511-2948-4c77-b04e-5ec419b58f22
-- title:
--   The random-horizon consumption-investment model (§9.1)
-- statement:
--   Section 9.1's model: an investor with wealth $x$ chooses consumption $c$ and a portfolio $a \in \mathbb R^d$ each period, facing a random one-period return $R_1$ and a random planning horizon that ends after each period independently with probability $1-p$. The reward $r(x,c,a) := U_c(c) + \beta(1-p)\,\mathbb E[U_p(T(x,c,a,R_1))]$ already folds in the $(1-p)$-probability terminal-utility term, and the effective one-period discount becomes $\tilde\beta := \beta p$ rather than $\beta$ — the model, once converted to a `StationaryMDM` via `toMDM`, is a genuine instance of Chapter 7's contracting theory with this effective discount. `v_0 := \sup_{\alpha \in \tilde A}\mathbb E[1+\alpha \cdot R_1]$ and `\alpha_b := \max\{1,v_0\}$ give the model's own upper bounding function $b(x):=1+x$ its explicit contraction constant.
--
--   **Formalization Note.** $d$, the number of risky assets, is a type parameter; the admissible-portfolio set $\tilde A$ and the domain $D(x)$ are stored as explicit fields with defining-equation hypotheses (`hAtilde`, `hD`) rather than folded silently into other fields' definitions, so the model's own standing restrictions are visible and citable.
--
--   **Moderation note.** The draft's admissible set was `{(c,a) | 0 ≤ c ≤ x, a ∈ Ã}` with `Ã = {1 + a·R₁ ≥ 0}` — not the book's `x − c + a·R₁ ≥ 0` a.s. (they differ unless `x − c = 1`); the utilities were arbitrary maps `ℝ → ℝ`; Assumption (FM) (no arbitrage, `𝔼‖R₁‖ < ∞`), the support `[-1,∞)^d`, `p ∈ (0,1)` and the state space `[0,∞)` were absent, so `v₀` was a junk real supremum and the reward a junk Bochner integral. Now the model carries (FM), the support, `p ∈ (0,1)`, `β ∈ (0,1]`, utility functions in the book's sense (Definition 3.4.1, nonnegative on `[0,∞)`), state space `E = [0,∞)`, the book's `D(x)`, and the reward as a `[0,∞]`-valued Lebesgue expectation; the transition is a Markov kernel built from `T(x,c,a,z) = x − c + a·z`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 269, PDF 279, the unnumbered data preceding Theorem 9.1.1

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- The **random-horizon consumption-investment model** (Bäuerle–Rieder, §9.1, pp. 268-269, PDF
278-279). A financial market with `d` risky assets and a riskless bond with interest rate `0`;
the relative risks `R_1, R_2, \dots` are i.i.d. with law `μR` on `[-1,\infty)^d` satisfying
Assumption (FM): (i) no arbitrage (`\varphi \cdot R_1 \ge 0` a.s. forces `\varphi \cdot R_1 = 0`
a.s.), (ii) `\mathbb E\|R_1\| < \infty`. The horizon `\tau` is geometric with parameter `p \in
(0,1)`, independent of the market; `\beta \in (0,1]`; `U_c, U_p : [0,\infty) \to \mathbb R_+`
are continuous utility functions (Definition 3.4.1: strictly increasing, strictly concave,
continuous on `\mathrm{dom} = [0,\infty)`). Wealth `x \in E := [0,\infty)`, action `(c,a) \in
\mathbb R_+ \times \mathbb R^d`, `D(x) := \{(c,a) \mid 0 \le c \le x,\ x - c + a \cdot R_1 \ge 0
\text{ a.s.}\}`, `T(x,c,a,z) := x - c + a \cdot z`, `r(x,c,a) := U_c(c) + \beta(1-p)\,\mathbb
E[U_p(T(x,c,a,R_1))]`, effective discount `\tilde\beta := \beta p`. -/
structure RandomHorizonCIModel (d : ℕ) where
  Uc : ℝ → ℝ
  Up : ℝ → ℝ
  hUc : (∀ x, 0 ≤ x → 0 ≤ Uc x) ∧ StrictMonoOn Uc (Set.Ici 0) ∧
    StrictConcaveOn ℝ (Set.Ici 0) Uc ∧ ContinuousOn Uc (Set.Ici 0)
  hUp : (∀ x, 0 ≤ x → 0 ≤ Up x) ∧ StrictMonoOn Up (Set.Ici 0) ∧
    StrictConcaveOn ℝ (Set.Ici 0) Up ∧ ContinuousOn Up (Set.Ici 0)
  μR : Measure (Fin d → ℝ)
  hμR : IsProbabilityMeasure μR
  hR_supp : ∀ᵐ z ∂μR, ∀ j, -1 ≤ z j
  /-- (FM)(i): no arbitrage. -/
  hNA : ∀ φ : Fin d → ℝ, (∀ᵐ z ∂μR, 0 ≤ ∑ j, φ j * z j) → ∀ᵐ z ∂μR, ∑ j, φ j * z j = 0
  /-- (FM)(ii): `\mathbb E\|R_1\| < \infty`. -/
  hmom : ∫⁻ z, ‖z‖ₑ ∂μR < ⊤
  β : ℝ
  hβ : β ∈ Set.Ioc (0 : ℝ) 1
  p : ℝ
  hp : p ∈ Set.Ioo (0 : ℝ) 1

variable {d : ℕ}

/-- `\tilde A := \{\alpha \in \mathbb R^d \mid 1 + \alpha \cdot R_1 \ge 0 \text{ a.s.}\}`
(Bäuerle–Rieder, p. 269). -/
def RandomHorizonCIModel.Atilde (M : RandomHorizonCIModel d) : Set (Fin d → ℝ) :=
  {α | ∀ᵐ z ∂M.μR, 0 ≤ 1 + ∑ j, α j * z j}

/-- `D := \{(x,c,a) \mid 0 \le c \le x,\ x - c + a \cdot R_1 \ge 0 \text{ a.s.}\}`. -/
def RandomHorizonCIModel.Dset (M : RandomHorizonCIModel d) :
    Set (ℝ≥0 × (ℝ≥0 × (Fin d → ℝ))) :=
  {xca | xca.2.1 ≤ xca.1 ∧ ∀ᵐ z ∂M.μR, 0 ≤ (xca.1 : ℝ) - xca.2.1 + ∑ j, xca.2.2 j * z j}

/-- `T(x,c,a,z) := x - c + a \cdot z` (Bäuerle–Rieder, p. 269), read in `E = [0,\infty)`; for
admissible `(c,a)` the argument is a.s. nonnegative, so the truncation is inactive. -/
noncomputable def RandomHorizonCIModel.Tnext (x c : ℝ≥0) (a z : Fin d → ℝ) : ℝ≥0 :=
  ((x : ℝ) - c + ∑ j, a j * z j).toNNReal

/-- `r(x,c,a) := U_c(c) + \beta(1-p)\,\mathbb E[U_p(T(x,c,a,R_1))]` in `[0,\infty]`. -/
noncomputable def RandomHorizonCIModel.reward (M : RandomHorizonCIModel d) (x c : ℝ≥0)
    (a : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M.Uc c) +
    ENNReal.ofReal (M.β * (1 - M.p)) *
      ∫⁻ z, ENNReal.ofReal (M.Up (RandomHorizonCIModel.Tnext x c a z)) ∂M.μR

/-- The stationary Markov Decision Model of §9.1 with effective discount `\tilde\beta := \beta p`
(Bäuerle–Rieder, p. 269). -/
noncomputable def RandomHorizonCIModel.toMDM (M : RandomHorizonCIModel d) :
    StationaryMDM ℝ≥0 (ℝ≥0 × (Fin d → ℝ)) where
  D := M.Dset
  hD_nonempty := fun x => ⟨(0, 0), by
    refine ⟨by simp, ?_⟩
    exact Filter.Eventually.of_forall fun z => by simp⟩
  step := haveI := M.hμR
    Kernel.map (Kernel.id ×ₖ Kernel.const _ M.μR)
      (fun q : (ℝ≥0 × (ℝ≥0 × (Fin d → ℝ))) × (Fin d → ℝ) =>
        RandomHorizonCIModel.Tnext q.1.1 q.1.2.1 q.1.2.2 q.2)
  isMarkov := by
    have := M.hμR
    refine Kernel.IsMarkovKernel.map _ ?_
    unfold RandomHorizonCIModel.Tnext
    fun_prop
  r := fun xca => M.reward xca.1 xca.2.1 xca.2.2
  β := M.β * M.p
  hβ := mul_pos M.hβ.1 M.hp.1

/-- `v_0 := \sup_{\alpha \in \tilde A} \mathbb E(1+\alpha \cdot R_1)` (finite under (FM), since
`\tilde A` is then bounded and `0 \in \tilde A`) and `\alpha_b := \max\{1, v_0\}`, the
contraction constant of the bounding function `b(x) := 1 + x` (Bäuerle–Rieder, p. 269). -/
noncomputable def RandomHorizonCIModel.v0 (M : RandomHorizonCIModel d) : ℝ :=
  ⨆ α : M.Atilde, ∫ z, (1 + ∑ j, (α : Fin d → ℝ) j * z j) ∂M.μR

noncomputable def RandomHorizonCIModel.αb (M : RandomHorizonCIModel d) : ℝ :=
  max 1 M.v0

end MDPFinance.DividendProblems


