-- Prove2me | Definitions.Def_OnlineBinCover_Ratios
-- name    : OnlineBinCover_Ratios
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:41.557073+00:00
-- url     : https://prove2.me/theorems/7533dc14-4110-418c-84f1-f71f4ad92244
-- title:
--   Random-order averages, $\mathrm{ARR}$ and $\mathrm{ECR}$
-- statement:
--   Let $A$ map each arrival sequence of sizes to a number of covered bins.
--
--   1. **Random order.** For a uniformly random permutation $\sigma$ of the items, item $\sigma(t)$ arrives at time $t$; $\mathbb E_\sigma[A(I_\sigma)]$ is the average of $A(s\circ\sigma)$ over the $n!$ permutations.
--   2. **ARR.** For $m\in\mathbb N$,
--   $$\mathrm{arrInf}_A(m)=\inf_{I:\ \mathrm{OPT}(I)\ge m}\frac{\mathbb E_\sigma[A(I_\sigma)]}{\mathrm{OPT}(I)},$$
--   the infimum over all valid instances; $\mathrm{ARR}(A)=1$ means $\mathrm{arrInf}_A(m)\to1$ as $m\to\infty$.
--   3. **IID.** For a probability measure $F$ on $\mathbb R$ carried by $(0,1]$, $I_n(F)=(X_1,\dots,X_n)$ with $X_i$ independent of law $F$, arriving in draw order. For $M\in\mathbb R$,
--   $$\mathrm{ecrInf}_A(M)=\inf_{n,F:\ \mathbb E[\mathrm{OPT}(I_n(F))]\ge M}\frac{\mathbb E[A(I_n(F))]}{\mathbb E[\mathrm{OPT}(I_n(F))]},$$
--   and $\mathrm{ECR}(A)=1$ means $\mathrm{ecrInf}_A(M)\to1$ as $M\to\infty$.
--
--   These are the two performance measures in which the main theorem is stated.
--
--   **Formalization Note** The infima are `sInf` of sets of reals (nonempty and bounded below by $0$), never iterated infima over propositions. Expectations under $F$ are lower Lebesgue integrals of nonnegative functions bounded by $n$, converted to reals; a lower bound on $\mathbb E[A]$ is therefore never obtained free. Quotients use $x/0=0$, which affects only $m=0$ and $M\le0$.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §1, p.2 (PDF p.3), displays (Expected Competitive Ratio) and (Asymptotic Random-order Ratio)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_OnlineBinCover_Basic

namespace OnlineBinCover

/-!
# Random-order averages, the asymptotic random-order ratio and the expected competitive ratio

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §1 p.2, the displays (Expected Competitive
Ratio) and (Asymptotic Random-order Ratio).

**Formalization Note.**
* An algorithm is a map `A : (n : ℕ) → (Fin n → ℝ) → ℕ` from the arrival sequence of sizes to the
  number of covered bins.
* *Random order.* A uniformly random permutation `σ` of the item labels makes item `σ t` arrive at
  time `t`, so the arrival sequence is `s ∘ σ`. `Eσ` is the published plain average
  `DynamicOnlineLP.DLA.avgPerm` over the `n!` permutations.
* *ARR.* `arrInf A m` is the infimum of `Eσ[A(Iσ)]/OPT(I)` over all instances with sizes in
  `(0,1]` and `OPT(I) ≥ m`, written as `sInf` of a set of reals (the set is nonempty and bounded
  below by `0`). "`ARR(A) = 1`" is `Tendsto (arrInf A) atTop (𝓝 1)`.
* *IID.* `iidExp μ n g` is `E[g(X₁,…,Xₙ)]` for `X₁,…,Xₙ` independent with law `μ`, written as the
  lower Lebesgue integral of `ofReal ∘ g` under the product measure, converted to a real number; the
  functions used are natural-number valued and at most `n`, so the integral is finite. For a
  non-measurable integrand the lower integral is the lower integral, so a lower bound on `E[A]` is
  never obtained free. The arrival order is the draw order.
* *ECR.* `ecrInf A M` is the infimum of `E[A(Iₙ(F))]/E[OPT(Iₙ(F))]` over all `n` and all
  probability measures `F` on `ℝ` carried by `(0,1]` (`F((0,1]ᶜ) = 0`) with `E[OPT] ≥ M`.
  "`ECR(A) = 1`" is `Tendsto (ecrInf A) atTop (𝓝 1)` with `M → ∞` through the reals.
* The quotient uses Lean's `x / 0 = 0`; this only affects `m = 0` and `M ≤ 0`, not the limits.
-/

open MeasureTheory

/-- `Eσ[A(Iσ)]`: the average of `A` over the `n!` arrival orders of the instance `s`. -/
noncomputable def roAvg (A : (n : ℕ) → (Fin n → ℝ) → ℕ) {n : ℕ} (s : Fin n → ℝ) : ℝ :=
  DynamicOnlineLP.DLA.avgPerm (fun σ : Equiv.Perm (Fin n) => (A n (s ∘ σ) : ℝ))

/-- `inf_{I : OPT(I) ≥ m} Eσ[A(Iσ)] / OPT(I)` (p.2). -/
noncomputable def arrInf (A : (n : ℕ) → (Fin n → ℝ) → ℕ) (m : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (s : Fin n → ℝ), ValidSizes s ∧ m ≤ OPT s ∧
    r = roAvg A s / (OPT s : ℝ)}

/-- `E[g(X₁,…,Xₙ)]` for `Xᵢ` i.i.d. with law `μ`. -/
noncomputable def iidExp (μ : Measure ℝ) (n : ℕ) (g : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (g x) ∂(Measure.pi fun _ : Fin n => μ)).toReal

/-- `inf_{n, F : E[OPT(Iₙ(F))] ≥ M} E[A(Iₙ(F))] / E[OPT(Iₙ(F))]` (p.2). -/
noncomputable def ecrInf (A : (n : ℕ) → (Fin n → ℝ) → ℕ) (M : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (μ : Measure ℝ), IsProbabilityMeasure μ ∧ μ (Set.Ioc 0 1)ᶜ = 0 ∧
    M ≤ iidExp μ n (fun x => (OPT x : ℝ)) ∧
    r = iidExp μ n (fun x => (A n x : ℝ)) / iidExp μ n (fun x => (OPT x : ℝ))}

end OnlineBinCover


