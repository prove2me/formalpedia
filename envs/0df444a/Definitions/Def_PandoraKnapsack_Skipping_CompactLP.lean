-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_CompactLP
-- name    : PandoraKnapsack_Skipping_CompactLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:24:27.804204+00:00
-- url     : https://prove2.me/theorems/1d849773-40bf-4508-8f91-7b40f4e84f7c
-- title:
--   The compact LP Ψ_P(b) on dyadic breakpoints and the uniform lift
-- statement:
--   The breakpoints are $T_b=\{\tau\le b:\tau=0\text{ or }\tau\text{ is a power of }2\}$, which is $\{0\}\cup\{2^l:0\le l\le\lfloor\log_2 b\rfloor\}$ for $b\ge1$ and $\{0\}$ for $b=0$. The compact LP $\Psi_P(b)$ is
--   $$\max_x\ \sum_{i,j}\sum_{\tau\in T_b} w_{i,j,2\tau}\,x_{i,j,\tau}$$
--   subject to (25) $\sum_{i,j}\sum_{\tau'\in T_b,\,\tau'\le\tau}x_{i,j,\tau'}\,\mu_{i,j,2\tau}\le2\tau$ for every $\tau\in T_b$, (26) $\sum_j\sum_{\tau\in T_b}x_{i,j,\tau}\le1$ for every item, and (27) $0\le x_{i,j,\tau}\le1$; $w$ and $\mu$ are evaluated by the same formulas also when $2\tau>b$ or $2\tau>T$.
--
--   For $\tau\in T_b\setminus\{0\}$ let $I_\tau=[\tau,2\tau)\cap\{0,\dots,b\}$. The **uniform lift** of $x$ is $y_{i,j,0}=x_{i,j,0}$ and $y_{i,j,t}=x_{i,j,\tau}/|I_\tau|$ for $t\in I_\tau$; for $1\le t\le b$ the breakpoint is $\tau=2^{\lfloor\log_2 t\rfloor}$ and $|I_\tau|\ge1$. Coordinates $t>b$ are set to $0$.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, Appendix B.1, equations (25)–(27) and the definition before Lemma B.2, printed pp. 39–41 (PDF 41–43)

import Definitions.Def_PandoraKnapsack_Skipping_TimeIndexedLP

open scoped Classical

namespace PandoraKnapsack.Skipping

/-- **The compact LP `Ψ_P(b)` and the uniform lift of its solutions.**

Barak et al. (2026), *Pandora's Knapsack via Simple Policies*, supplied PDF (SHA256
45e5830b…7a2d), Appendix B.1, printed pp. 39–41 (PDF 41–43). The breakpoints are
`T_b = {0} ∪ {2^l : l ∈ {0, …, ⌊log b⌋}}`, and
`Ψ_P(b) = max Σ_{i,j} Σ_{τ ∈ T_b} w_{i,j,2τ} x_{i,j,τ}` subject to
(25) `Σ_{i,j} Σ_{τ' ≤ τ} x_{i,j,τ'} μ_{i,j,2τ} ≤ 2τ` for every `τ ∈ T_b`,
(26) `Σ_j Σ_{τ ∈ T_b} x_{i,j,τ} ≤ 1` for every item `i`,
(27) `0 ≤ x_{i,j,τ} ≤ 1`.
"Here `w_{i,j,2τ}` and `μ_{i,j,2τ}` are given by the same formulas as in Section 5.1 also when
`2τ > b`."

**Formalization Note.** `T_b` is written as `{τ ≤ b : τ = 0 or τ is a power of two}`, which for
`b ≥ 1` is the source's set (`2^l ≤ b` iff `l ≤ ⌊log₂ b⌋`) and for `b = 0` is `{0}`, where the
source's `⌊log 0⌋` is undefined. Arrays are indexed by `ℕ`; coordinates outside `T_b` are ignored. -/
noncomputable def breakpoints (b : ℕ) : Finset ℕ :=
  (Finset.range (b + 1)).filter fun τ => τ = 0 ∨ ∃ l : ℕ, τ = 2 ^ l

variable {n m T : ℕ}

/-- Feasibility for `Ψ_P(b)`: constraints (25), (26), (27). -/
def PsiPFeasible (I : Instance n m T) (b : ℕ) (x : LPArray n m) : Prop :=
  (∀ τ ∈ breakpoints b,
      ∑ i, ∑ j, ∑ τ' ∈ (breakpoints b).filter (fun τ' => τ' ≤ τ),
        x i j τ' * mu I i j (2 * τ) ≤ 2 * (τ : ℝ)) ∧
  (∀ i, ∑ j, ∑ τ ∈ breakpoints b, x i j τ ≤ 1) ∧
  (∀ i j, ∀ τ ∈ breakpoints b, 0 ≤ x i j τ ∧ x i j τ ≤ 1)

/-- The objective `Σ_{i,j} Σ_{τ ∈ T_b} w_{i,j,2τ} x_{i,j,τ}` of `Ψ_P(b)`. -/
noncomputable def psiPObjective (I : Instance n m T) (b : ℕ) (x : LPArray n m) : ℝ :=
  ∑ i, ∑ j, ∑ τ ∈ breakpoints b, effWeight I i j (2 * τ) * x i j τ

/-- `x` is an optimal solution of `Ψ_P(b)`. -/
def PsiPOptimal (I : Instance n m T) (b : ℕ) (x : LPArray n m) : Prop :=
  PsiPFeasible I b x ∧ ∀ y, PsiPFeasible I b y → psiPObjective I b y ≤ psiPObjective I b x

/-- The interval `I_τ = [τ, 2τ) ∩ {0, …, b}` of a breakpoint `τ` (printed p. 41, PDF 43). -/
def blockInterval (b τ : ℕ) : Finset ℕ :=
  (Finset.Ico τ (2 * τ)).filter fun t => t ≤ b

/-- The breakpoint `τ = 2^{⌊log₂ t⌋}` whose interval `I_τ` contains a time `t ≥ 1`. -/
def blockOf (t : ℕ) : ℕ := 2 ^ Nat.log 2 t

/-- The uniform lift `y` of an array `x` on `T_b` (printed p. 41, PDF 43):
`y_{i,j,0} = x_{i,j,0}` and `y_{i,j,t} = x_{i,j,τ} / |I_τ|` for `τ ∈ T_b ∖ {0}` and `t ∈ I_τ`.
For `1 ≤ t ≤ b` the unique such `τ` is `blockOf t`, and `|I_τ| ≥ 1`. Coordinates `t > b`, outside
the index set of `Ψ(b)`, are set to `0`. -/
noncomputable def liftY (b : ℕ) (x : LPArray n m) : LPArray n m := fun i j t =>
  if t = 0 then x i j 0
  else if t ≤ b then x i j (blockOf t) / ((blockInterval b (blockOf t)).card : ℝ)
  else 0

end PandoraKnapsack.Skipping


