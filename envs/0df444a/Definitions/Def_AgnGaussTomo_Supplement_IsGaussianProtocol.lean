-- Prove2me | Definitions.Def_AgnGaussTomo_Supplement_IsGaussianProtocol
-- name    : AgnGaussTomo_Supplement_IsGaussianProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:01:01.92901+00:00
-- url     : https://prove2.me/theorems/d6e70dbd-a2de-4854-844b-9cf5ca51379a
-- title:
--   Gaussian protocols: algorithms on $N$ copies that use only Gaussian measurements
-- statement:
--   Let $N$ copies of an $m$-mode bosonic system be given; together they form a system of $Nm$ modes, with Fock space $\ell^2(\mathbb N^m)^{\otimes N}$. Recall that a **Gaussian measurement** of a system of $M$ modes is a POVM $M(d^{2M}y)=(2\pi)^{-M}D(y)\,\tau\,D(y)^\dagger\,d^{2M}y$ with a mean-zero Gaussian **seed** state $\tau$, where $D(y)$ is the displacement operator, $D(y)^\dagger\hat R_jD(y)=\hat R_j+y_jI$.
--
--   A POVM $P$ on the $N$-copy system with outcomes $(y,u)\in\mathbb R^{2Nm}\times\mathbb R$ is a **Gaussian protocol** if there is a family $\tau(y,u)$ of mean-zero Gaussian states of the $Nm$ modes, depending measurably on $(y,u)$, such that for every density operator $R$ of the $N$-copy system and every measurable set $B$ of outcomes
--
--   $$
--   \Pr_R[(y,u)\in B]=\int_{(y,u)\in B,\ 0\le u\le1}\frac{1}{(2\pi)^{Nm}}\operatorname{tr}\big(D(y)\,\tau(y,u)\,D(y)^\dagger R\big)\,d^{2Nm}y\,du .
--   $$
--
--   So $u$ is a uniform random number in $[0,1]$ (classical randomness), and the effect density at the outcome $(y,u)$ is a displaced mean-zero Gaussian state whose seed may depend on the outcome.
--
--   This is the class of "algorithms using only Gaussian measurements" on $N$ copies for which the hardness result (Theorem 5.6) is stated. It contains every way of combining Gaussian measurements with adaptivity and classical processing: (a) adaptive single-copy schemes in which every round is a Gaussian measurement (the transcript $(y_1,\dots,y_N)$ has effect density $\bigotimes_t D(y_t)\tau_t(y_{<t})D(y_t)^\dagger$, a displaced product seed determined by the earlier outcomes); (b) a joint Gaussian measurement of all $N$ copies, with a seed that may be entangled across copies, and adaptive Gaussian measurements of blocks of copies; (c) adaptive Gaussian measurements of subsets of the modes, with Gaussian unitaries chosen from earlier outcomes. Every such effect has a nonnegative Wigner function, the property the source's proof uses.
--
--   **Formalization Note** The $N$-copy Fock basis is indexed by $N$-tuples of one-copy Fock states; a Fock state $v$ of the $Nm$ modes, labelled $(k,j)$ for mode $j$ of copy $k$, corresponds to the tuple $k\mapsto(j\mapsto v(k,j))$. The outcome $y$ is in the grouped order $(q,p)$. The density $\operatorname{tr}(D(y)\tau D(y)^\dagger R)$ is an iterated series over the Fock basis (real part), and the integral is a lower Lebesgue integral, so no integrability side condition can make it vanish. Measurability of $\tau$ is entrywise in the Fock basis.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 5.6, printed pp. 52–53 (PDF pp. 55–56) ("any algorithm using only Gaussian measurements"); proof, Eq. (80), printed p. 55 (PDF p. 58) ("including those that use adaptivity or arbitrary classical processing"); Gaussian measurements, §2.2, printed p. 10 (PDF p. 13)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation Quadratures weylKernel)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt OscillatorCovariance)
open MeasureTheory

namespace AgnGaussTomo.Supplement

/-- **An algorithm on `N` copies that uses only Gaussian measurements, as one measurement of the
`N`-copy system.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure in Bosonic States*,
arXiv:2610.06810 (version of 3 Nov 2026), Theorem 5.6, printed pp. 52–53 (PDF pp. 55–56): "any
algorithm using only Gaussian measurements"; its proof, printed p. 55 (PDF p. 58), Eq. (80): "no
protocol using only Gaussian measurements, including those that use adaptivity or arbitrary
classical processing"; Gaussian measurements are defined in §2.2, printed p. 10 (PDF p. 13):
"POVMs of the form M(d^{2n}y) = 1/(2π)^n D(y) τ D(y)† d^{2n}y, where τ is a mean-zero Gaussian state
known as the seed state".

The `N` copies of an `m`-mode system form a system of `N·m` modes, labelled `(k, j)` (mode `j` of
copy `k`). A POVM `P` on it with outcomes `(y, u) ∈ ℝ^{2Nm} × ℝ` is a *Gaussian protocol* if there
is a family `τ(y, u)` of mean-zero Gaussian states of the `N·m` modes, depending measurably on
`(y, u)`, such that for every density operator `R` of the `N`-copy system and every measurable set
`B` of outcomes

  `P[(y, u) ∈ B] = ∫_{(y,u) ∈ B, 0 ≤ u ≤ 1} (2π)^{-Nm} tr(D(y) τ(y, u) D(y)† R) d^{2Nm}y du`,

i.e. `u` is a uniform random number in `[0, 1]` and the effect density at `(y, u)` is the displaced
Gaussian seed `(2π)^{-Nm} D(y) τ(y, u) D(y)†`, whose seed may depend on the outcome.

**Formalization Note.**
1. The paper does not define the class of "algorithms using only Gaussian measurements". This class
   contains every reading: (a) adaptive single-copy schemes whose every round is a Gaussian
   measurement (the published `AgnGaussTomo.IsGaussianScheme`: the transcript `(y₁, …, y_N)` has
   effect density `⊗_t D(y_t) τ_t(y_{<t}) D(y_t)†`, a displaced product seed depending on the earlier
   outcomes; the per-round random numbers are coded into `u`); (b) one joint Gaussian measurement of
   all `N` copies (constant seed, possibly entangled across copies) and adaptive Gaussian
   measurements of blocks of copies; (c) adaptive Gaussian measurements of subsets of the modes with
   Gaussian unitaries chosen from earlier outcomes (outcomes relabelled by the affine symplectic
   maps, which preserve Lebesgue measure). In each case the effect density is a displaced mean-zero
   Gaussian state with a seed determined by the outcome. All these effects have nonnegative Wigner
   functions, which is the only property the paper's proof uses (Lemma 3 of [SW21] in Eq. (80)).
2. The `N`-copy Fock basis is `Fin N → Occupation (Fin m)` (as in the published
   `WildeQIT.Schumacher.tensorPow` and `BosonicLearn.Supplement.KCopyScheme`); a Fock state `v` of
   the `N·m` modes corresponds to `fun k j => v (k, j)`. `y` is in the grouped order (`inl (k, j)` =
   `q_{k,j}`, `inr (k, j)` = `p_{k,j}`); `D(y)` is the published `weylKernel` at `−y`, exactly as in
   `AgnGaussTomo.dispOp`. The seed's Gaussianity is the published `GaussianAt … 0 W` (mean zero).
3. As in `AgnGaussTomo.IsGaussianPOVM`, the density `tr(D(y) τ D(y)† R)` is the iterated Fock-basis
   series (real part), and the integral is a lower Lebesgue integral of its `ENNReal.ofReal`, so no
   integrability condition can make it vanish. Measurability of the seed family is entrywise; it is
   a regularity condition every protocol satisfies (the seed is determined by the outcome law). -/
def IsGaussianProtocol {N m : ℕ}
    (P : BosonicLearn.FockPOVM (Fin N → Occupation (Fin m))
      ((Quadratures (Fin N × Fin m) → ℝ) × ℝ)) : Prop :=
  ∃ τ : (Quadratures (Fin N × Fin m) → ℝ) × ℝ → State (Occupation (Fin N × Fin m)),
    (∀ p, ∃ W : OscillatorCovariance (Fin N × Fin m), GaussianAt (τ p).coefficients 0 W) ∧
    (∀ a b, Measurable fun p => (τ p).coefficients a b) ∧
    ∀ R : Matrix (Fin N → Occupation (Fin m)) (Fin N → Occupation (Fin m)) ℂ, IsDensity R →
      ∀ B : Set ((Quadratures (Fin N × Fin m) → ℝ) × ℝ), MeasurableSet B →
        P.law R B = ∫⁻ p in B ∩ (Set.univ ×ˢ Set.Icc 0 1),
          ENNReal.ofReal (((2 * Real.pi) ^ (N * m))⁻¹ *
            (∑' u, ∑' v, (∑' a, ∑' b, weylKernel (fun i => -p.1 i) u a * (τ p).coefficients a b *
              star (weylKernel (fun i => -p.1 i) v b)) *
                R (fun k j => v (k, j)) (fun k j => u (k, j))).re)

end AgnGaussTomo.Supplement


