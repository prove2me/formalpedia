-- Prove2me | Definitions.Def_BousquetElisseeff_KLReg_IsKLRegMinimizer
-- name    : BousquetElisseeff_KLReg_IsKLRegMinimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:43:19.766523+00:00
-- url     : https://prove2.me/theorems/58ca8b1e-b08f-4c72-8b59-a9db0e49ad88
-- title:
--   Minimizer over $\mathcal F$ of a relative-entropy regularized empirical risk
-- statement:
--   Fix a prior density $f_0$, a parameter $\lambda$, a weight $w$, a sample $S = (z_1,\dots,z_m)$ and a set of indices $T \subseteq \{1,\dots,m\}$. A function $g$ is a **minimizer** if $g$ is a density and for every density $g'$
--   $$w \sum_{j\in T} \ell(g, z_j) + \lambda K(g, f_0) \;\le\; w \sum_{j\in T} \ell(g', z_j) + \lambda K(g', f_0).$$
--   The three instances used in the mission are
--
--   1. $w = 1/m$, $T = \{1,\dots,m\}$: a minimizer of $R_r$ in (19), i.e. a value $A_S$ of the algorithm (29);
--   2. $w = 1/m$, $T = \{1,\dots,m\}\setminus\{i\}$: a minimizer $f^{\setminus i}$ of $R_r^{\setminus i}$ in (20);
--   3. $w = 1/(m-1)$, $T = \{1,\dots,m\}\setminus\{i\}$: a value $A_{S^{\setminus i}}$ of the algorithm (29) run on the sample with the $i$-th point removed.
--
--   **Formalization Note** The objective takes values in $(-\infty, +\infty]$ because $K$ may be $+\infty$; it is compared in `EReal`, where nothing is subtracted. "arg min" is read as "any minimizer"; the predicate asserts neither existence nor uniqueness.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, eqs. (19)–(20), p. 512; eq. (29), p. 518

import Mathlib
import Definitions.Def_BousquetElisseeff_KLReg_IsDensity
import Definitions.Def_BousquetElisseeff_KLReg_relEnt
import Definitions.Def_BousquetElisseeff_KLReg_avgLoss

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **A minimizer over 𝓕 of a relative-entropy regularized empirical objective** (eqs. (19),
(20), (29)).
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526:
eq. (19), p. 512: "R_r(g) := (1/m) Σ_{j=1}^m ℓ(g, z_j) + λN(g)"; eq. (20), p. 512:
"R_r^{\i}(g) := (1/m) Σ_{j≠i} ℓ(g, z_j) + λN(g)"; eq. (29), p. 518:
"A_S = arg min_{g∈𝓕} (1/m) Σ_{i=1}^m ℓ(g, z_i) + λK(g, f0)", with N(g) = K(g, f0) (p. 517).

`IsKLRegMinimizer μ r f0 lam w T S g` says that `g` is a density (`IsDensity μ g`) and that for
every density `g'`
`w · Σ_{j ∈ T} ℓ(g, z_j) + λ K(g, f₀) ≤ w · Σ_{j ∈ T} ℓ(g', z_j) + λ K(g', f₀)`,
where `z_j = S j`, `ℓ = avgLoss μ r` and `K = relEnt μ`. The instances used in the mission are
1. `w = 1/m`, `T = univ`: a minimizer of (19), i.e. a value of A_S in (29);
2. `w = 1/m`, `T = univ.erase i`: a minimizer f^{\i} of (20) (Lemmas 20–21);
3. `w = 1/(m − 1)`, `T = univ.erase i`: a value of A_{S\i}, i.e. (29) on the `(m−1)`-point
   sample S\i (the order of S\i is irrelevant by the symmetry of A, p. 501).

**Formalization Note.** The objective takes values in `(−∞, +∞]` (K can be `+∞`) and is compared
in `EReal`: the empirical term is a real number and `λ K` is `λ` times the `ℝ≥0∞` value of K
coerced to `EReal`, so nothing is subtracted and no `⊤ − ⊤` occurs. "arg min" is read as "any
minimizer": the predicate does not assert existence or uniqueness. -/
def IsKLRegMinimizer {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ)
    (f0 : Θ → ℝ) (lam w : ℝ) {m : ℕ} (T : Finset (Fin m)) (S : Fin m → Z) (g : Θ → ℝ) : Prop :=
  IsDensity μ g ∧ ∀ g' : Θ → ℝ, IsDensity μ g' →
    ((w * ∑ j ∈ T, avgLoss μ r g (S j) : ℝ) : EReal) + (lam : EReal) * ((relEnt μ g f0 : ENNReal) : EReal)
      ≤ ((w * ∑ j ∈ T, avgLoss μ r g' (S j) : ℝ) : EReal)
          + (lam : EReal) * ((relEnt μ g' f0 : ENNReal) : EReal)

end BousquetElisseeff.KLReg


