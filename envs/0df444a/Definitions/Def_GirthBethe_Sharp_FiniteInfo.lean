-- Prove2me | Definitions.Def_GirthBethe_Sharp_FiniteInfo
-- name    : GirthBethe_Sharp_FiniteInfo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:10:11.185266+00:00
-- url     : https://prove2.me/theorems/edbf5102-4c2a-408d-9dfb-12d8bf5c04e1
-- title:
--   Definitions 2.5, 2.6 — laws, conditional laws, KL divergence and $\Psi$-information gain
-- statement:
--   Let $P$ be a probability law on a finite sample space $\Omega$ and let $U:\Omega\to\alpha$, $Y:\Omega\to\beta$ be finite random variables.
--
--   1. The law of $U$ is $\mathcal L(U)(a)=P(U=a)$.
--   2. The conditional law is $\mathcal L(U\mid Y=y)(a)=P(U=a,\,Y=y)/P(Y=y)$ when $P(Y=y)>0$; when $P(Y=y)=0$ the unconditional law $\mathcal L(U)$ is used as the version of the conditional law.
--   3. (Definition 2.6) For a functional $\Psi$ on laws on $\alpha$, the $\Psi$-information gain from observing $Y$ is
--   $$I_\Psi(U;Y)=\Psi(\mathcal L(U))-\mathbb E_Y\,\Psi(\mathcal L(U\mid Y))=\Psi(\mathcal L(U))-\sum_y P(Y=y)\,\Psi(\mathcal L(U\mid Y=y)).$$
--   4. (Definition 2.5) For laws $\mu,\nu$ on a finite set, the Kullback–Leibler divergence is
--   $$\mathrm{KL}(\mu\|\nu)=\sum_\omega \mu(\omega)\log\frac{\mu(\omega)}{\nu(\omega)}\in[0,+\infty],$$
--   with $0\log(0/y)=0$ for $y\ge0$ and $x\log(x/0)=+\infty$ for $x>0$.
--
--   These objects express the information-theoretic steps of the paper: mutual information, its concave generalizations, and the edge weights of §4.
--
--   **Formalization Note** Laws are real vectors on finite types. The convention for conditioning on a null event never changes an information gain, since such a term carries weight $P(Y=y)=0$. KL takes values in the extended reals.
--
--   The KL function reuses the published `RobustKellyTV.kl`, after a bijection of the finite alphabet with `Fin (card α)` and the canonical embedding of nonnegative extended reals in extended reals. The function has no `Setting` argument and imposes no full-support condition. Its finite branch uses `ENNReal.ofReal` on the entire divergence sum; Gibbs' inequality makes that conversion exact for probability laws.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 7, Definitions 2.5 and 2.6, equations (2.2)–(2.3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_RobustKellyTV_kl

open Finset

namespace GirthBethe.Sharp

/-! Finite probability, Kullback–Leibler divergence and Ψ-information gain (§2.2, Definitions 2.5
and 2.6 of Jain–Dong, STOC 2027 submission #705). A probability law on a finite sample space `Ω`
is a vector `P ∈ stdSimplex ℝ Ω`; a finite random variable is a function `U : Ω → α` into a
finite type. -/

open scoped Classical in
/-- The law `L(U)` of `U : Ω → α` under `P`: `L(U)(a) = P(U = a)`. -/
noncomputable def law {Ω α : Type*} [Fintype Ω] (P : Ω → ℝ) (U : Ω → α) : α → ℝ :=
  fun a => ∑ ω with U ω = a, P ω

open scoped Classical in
/-- The conditional law `L(U | Y = y)`: `P(U = a, Y = y) / P(Y = y)` when `P(Y = y) > 0`. When
`P(Y = y) = 0` the unconditional law `L(U)` is used as the version of the conditional law;
it enters every formula below only with weight `P(Y = y) = 0`. -/
noncomputable def condLaw {Ω α β : Type*} [Fintype Ω] (P : Ω → ℝ) (U : Ω → α) (Y : Ω → β)
    (y : β) : α → ℝ :=
  if law P Y y = 0 then law P U
  else fun a => (∑ ω with U ω = a ∧ Y ω = y, P ω) / law P Y y

/-- The Ψ-information gain `I_Ψ(U; Y) = Ψ(L(U)) - E_Y Ψ(L(U | Y))` (Definition 2.6), for a
functional `Ψ` on laws on `α`. -/
noncomputable def infoGain {Ω α β : Type*} [Fintype Ω] [Fintype β] (Ψ : (α → ℝ) → ℝ)
    (P : Ω → ℝ) (U : Ω → α) (Y : Ω → β) : ℝ :=
  Ψ (law P U) - ∑ y, law P Y y * Ψ (condLaw P U Y y)

/-- Kullback–Leibler divergence `KL(μ ‖ ν) = ∑_ω μ(ω) log (μ(ω)/ν(ω))` (Definition 2.5), valued
in the extended reals, with the conventions `0 log (0/y) = 0` for `y ≥ 0` and
`x log (x/0) = +∞` for `x > 0`. This reuses the published `RobustKellyTV.kl`,
reindexing the finite alphabet by an equivalence and embedding its `ℝ≥0∞` value in `EReal`.
The divergence itself has no `Setting` argument or full-support hypothesis. The `ofReal`
conversion in that definition loses no value on probability laws, by Gibbs' inequality. -/
noncomputable def klDiv {α : Type*} [Fintype α] (μ ν : α → ℝ) : EReal :=
  (RobustKellyTV.kl (fun i => μ ((Fintype.equivFin α).symm i))
    (fun i => ν ((Fintype.equivFin α).symm i)) : EReal)

end GirthBethe.Sharp


