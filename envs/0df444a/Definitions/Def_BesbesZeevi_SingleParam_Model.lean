-- Prove2me | Definitions.Def_BesbesZeevi_SingleParam_Model
-- name    : BesbesZeevi_SingleParam_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:41:52.996554+00:00
-- url     : https://prove2.me/theorems/db81d778-296e-43ef-84a5-2d018de5b83b
-- title:
--   Prices, the demand class $\mathcal L(M,\underline K,\overline K,m)$ and the deterministic relaxation $J^D$
-- statement:
--   A **market** consists of price bounds $0<\underline p<\overline p$, an "off" price $p_\infty>\overline p$, an initial inventory $x>0$ and a selling horizon $T>0$. Prices are chosen from $[\underline p,\overline p]\cup\{p_\infty\}$.
--
--   For constants $M,\underline K,\overline K,m$, a demand function $\lambda:\mathbb R\to\mathbb R$ (price $\mapsto$ demand rate) belongs to the class $\mathcal L(M,\underline K,\overline K,m)$ when
--
--   1. $\lambda(p_\infty)=0$ and $\lambda\ge 0$ on $[\underline p,\overline p]$;
--   2. (regularity) $\lambda$ is non-increasing and injective on $[\underline p,\overline p]$, with inverse $\gamma$, and the revenue rate $r(l)=l\,\gamma(l)$ is concave on $[\lambda(\overline p),\lambda(\underline p)]$;
--   3. $|\lambda(p)|\le M$ for $p\in[\underline p,\overline p]$;
--   4. $|\lambda(p)-\lambda(p')|\le\overline K|p-p'|$ on $[\underline p,\overline p]$ and $|\gamma(l)-\gamma(l')|\le\underline K^{-1}|l-l'|$ on $[\lambda(\overline p),\lambda(\underline p)]$;
--   5. $\max\{p\lambda(p):p\in[\underline p,\overline p]\}\ge m$.
--
--   The **full-information deterministic relaxation** with demand $\lambda$ and inventory $y$ is
--
--   $$
--   J^D(y,T\mid\lambda)=\sup\Big\{\int_0^T p(s)\lambda(p(s))\,ds\;:\;\int_0^T\lambda(p(s))\,ds\le y,\ p(s)\in[\underline p,\overline p]\cup\{p_\infty\}\text{ for }s\in[0,T]\Big\},
--   $$
--
--   the supremum being over measurable price paths. In the market of size $n$ (inventory $nx$, demand $n\lambda$), $J^D_n(x,T\mid\lambda)=J^D(nx,T\mid n\lambda)$.
--
--   These objects are the benchmark against which the regret of a pricing policy is measured.
--
--   **Formalization Note** The inverse $\gamma$ is `Function.invFunOn` of $\lambda$ on $[\underline p,\overline p]$. The class conditions constrain $\lambda$ only on $[\underline p,\overline p]\cup\{p_\infty\}$, the only prices any path uses. Feasible paths are required to be measurable with integrable rate and revenue integrands (which holds automatically for paths with values in $[\underline p,\overline p]\cup\{p_\infty\}$ when $\lambda$ is in the class). The supremum is a real `sSup` of a set that is nonempty (the constant path $p_\infty$) and bounded above by $\overline p MT$ on the class. Positivity of $M,\underline K,m$ and $\underline K\le\overline K$ are hypotheses of the statements that use the class.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), pp. 6-8 (PDF pp. 8-10), §3 and eq. (5); p. 11 (PDF p. 13), Assumption 1; p. 12 (PDF p. 14), scaling (11)

import Mathlib

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- The market primitives of Besbes–Zeevi (2009), §3, pp. 6–7: the price bounds
`0 < pLo < pHi` (the paper's `p̲ < p̄`), the "off" price `pOff` (the paper's `p∞`), the
initial inventory `x > 0` and the selling horizon `T > 0`. The off price lies above `pHi`:
a non-increasing demand that is positive on `[pLo, pHi]` and vanishes at `pOff` forces this. -/
structure Market where
  pLo : ℝ
  pHi : ℝ
  pOff : ℝ
  x : ℝ
  T : ℝ
  pLo_pos : 0 < pLo
  pLo_lt_pHi : pLo < pHi
  pHi_lt_pOff : pHi < pOff
  x_pos : 0 < x
  T_pos : 0 < T

/-- The inverse `γ` of a demand function `f` on the price interval `[pLo, pHi]`. -/
noncomputable def invDemand (D : Market) (f : ℝ → ℝ) : ℝ → ℝ :=
  Function.invFunOn f (Set.Icc D.pLo D.pHi)

/-- The class `𝓛(M, K̲, K̄, m)` of Besbes–Zeevi (2009): regular demand functions (p. 6) that
satisfy Assumption 1 (p. 11). A demand function `f : ℝ → ℝ` (price ↦ rate) belongs to it iff

* `f(p∞) = 0` (the off price turns demand off) and `f ≥ 0` on `[p̲, p̄]`;
* *regularity*: `f` is non-increasing on `[p̲, p̄]`, has an inverse `γ` there (`f` is injective
  on `[p̲, p̄]`, and `γ = invDemand D f`), and the revenue rate `r(l) = l γ(l)` is concave on
  the rate interval `[f(p̄), f(p̲)]`;
* (i) `|f(p)| ≤ M` on `[p̲, p̄]`;
* (ii) `|f(p) - f(p')| ≤ K̄ |p - p'|` on `[p̲, p̄]` and `|γ(l) - γ(l')| ≤ K̲⁻¹ |l - l'|` on
  `[f(p̄), f(p̲)]`;
* (iii) `max {p f(p) : p ∈ [p̲, p̄]} ≥ m`, i.e. some admissible price earns revenue rate `≥ m`.

The positivity of the constants and `K̲ ≤ K̄` are hypotheses of the statements that use it. -/
def InClass (D : Market) (M KLo KHi m : ℝ) (f : ℝ → ℝ) : Prop :=
  f D.pOff = 0 ∧
  (∀ p ∈ Set.Icc D.pLo D.pHi, 0 ≤ f p) ∧
  AntitoneOn f (Set.Icc D.pLo D.pHi) ∧
  Set.InjOn f (Set.Icc D.pLo D.pHi) ∧
  ConcaveOn ℝ (Set.Icc (f D.pHi) (f D.pLo)) (fun l => l * invDemand D f l) ∧
  (∀ p ∈ Set.Icc D.pLo D.pHi, |f p| ≤ M) ∧
  (∀ p ∈ Set.Icc D.pLo D.pHi, ∀ p' ∈ Set.Icc D.pLo D.pHi, |f p - f p'| ≤ KHi * |p - p'|) ∧
  (∀ l ∈ Set.Icc (f D.pHi) (f D.pLo), ∀ l' ∈ Set.Icc (f D.pHi) (f D.pLo),
    |invDemand D f l - invDemand D f l'| ≤ KLo⁻¹ * |l - l'|) ∧
  (∃ p ∈ Set.Icc D.pLo D.pHi, m ≤ p * f p)

/-- A feasible price path of the deterministic relaxation (5) (p. 8) for demand `f` and
inventory `y`: a measurable path `p : ℝ → ℝ` taking values in `[p̲, p̄] ∪ {p∞}` on `[0, T]`,
whose rate and revenue-rate integrands are integrable on `[0, T]` and whose total demand
`∫₀ᵀ f(p(s)) ds` does not exceed `y`. -/
def Feasible (D : Market) (f : ℝ → ℝ) (y : ℝ) (p : ℝ → ℝ) : Prop :=
  Measurable p ∧
  (∀ s ∈ Set.Icc (0 : ℝ) D.T, p s ∈ Set.Icc D.pLo D.pHi ∨ p s = D.pOff) ∧
  IntegrableOn (fun s => f (p s)) (Set.Icc (0 : ℝ) D.T) ∧
  IntegrableOn (fun s => p s * f (p s)) (Set.Icc (0 : ℝ) D.T) ∧
  (∫ s in Set.Icc (0 : ℝ) D.T, f (p s)) ≤ y

/-- `J^D(y, T | f)`: the value of the full-information deterministic relaxation (5) (p. 8),
`sup ∫₀ᵀ p(s) f(p(s)) ds` over feasible paths (here `r(f(p)) = p f(p)`). -/
noncomputable def detValue (D : Market) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ p : ℝ → ℝ, Feasible D f y p ∧
    v = ∫ s in Set.Icc (0 : ℝ) D.T, p s * f (p s)}

/-- `J^D_n(x, T | f)`: the deterministic relaxation in the market of size `n` (scaling (11),
p. 12): inventory `n x` and demand `n f(·)`. -/
noncomputable def detValueScaled (D : Market) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  detValue D (fun p => (n : ℝ) * f p) ((n : ℝ) * D.x)

end BesbesZeevi.SingleParam


