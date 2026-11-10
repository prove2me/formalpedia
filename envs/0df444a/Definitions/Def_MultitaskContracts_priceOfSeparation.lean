-- Prove2me | Definitions.Def_MultitaskContracts_priceOfSeparation
-- name    : MultitaskContracts_priceOfSeparation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:42.57858+00:00
-- url     : https://prove2.me/theorems/a91d0119-b7fc-4087-bf3a-bc0f8ba07647
-- title:
--   Price of separation $\mathrm{PoSep}_X(\mathcal I)$ (Definition 1)
-- statement:
--   Let $X$ be an objective (Budgeted Min-Pay, Min-Pay or Min-Budget), so that every instance $I$ and contract class $\mathcal T$ have an optimum $\mathrm{OPT}^{\mathcal T}_X(I)\in[0,\infty]$. The **price of separation** of $X$ over a class $\mathcal I$ of instances on the task set $K$ is
--   $$\mathrm{PoSep}_X(\mathcal I)=\sup_{I\in\mathcal I}\frac{\mathrm{OPT}^{\mathrm{Sep}}_X(I)}{\mathrm{OPT}^{\mathrm{Bun}}_X(I)},\qquad\text{where } \infty/\infty:=1,$$
--   the worst-case ratio between the optimum over separable contracts and the optimum over bundle contracts.
--
--   It quantifies how much the principal can gain by bundling the tasks into one contract.
--
--   **Formalization Note** The objective is passed as a function `obj I T` of the instance and the contract class (Min-Pay is `fun I T => I.optMinPay T`). Ratios and the supremum are in `ℝ≥0∞`, where a supremum always exists; the helper `sepRatio a b` is `1` when $a=b=\infty$ and $a/b$ otherwise (in `ℝ≥0∞`, $a/0=\infty$ for $a\neq0$ and $0/0=0$; neither case arises when both optima are finite and positive).
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Definition 1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_separable

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- The ratio of Definition 1 with the convention `∞/∞ := 1`.

**Formalization Note.** In `ℝ≥0∞`, `a/0 = ⊤` for `a ≠ 0` and `0/0 = 0`; neither case arises
when both optima are finite and positive. -/
noncomputable def sepRatio (a b : ℝ≥0∞) : ℝ≥0∞ :=
  if a = ⊤ ∧ b = ⊤ then 1 else a / b

/-- **Price of separation** (Definition 1, p.8, PDF 10): for an objective `X` and a class `𝓘` of
instances, `PoSep_X(𝓘) := sup_{I ∈ 𝓘} OPT^Sep_X(I) / OPT^Bun_X(I)`, where `∞/∞ := 1`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Definition 1, p.8.

**Formalization Note.** The objective is passed as `obj I T` (the optimum of instance `I` over the
contract class `T`), e.g. `fun I T => I.optMinPay T` for Min-Pay. Optima live in `ℝ≥0∞` and so
does the supremum (`⨆`), which always exists; `sepRatio` implements `∞/∞ := 1`. -/
noncomputable def priceOfSeparation {K : Type*} [Fintype K] [DecidableEq K]
    (obj : Instance K → Set (Finset K → ℝ) → ℝ≥0∞) (𝓘 : Set (Instance K)) : ℝ≥0∞ :=
  ⨆ I ∈ 𝓘, sepRatio (obj I (separable K)) (obj I (bundle K))

end MultitaskContracts


