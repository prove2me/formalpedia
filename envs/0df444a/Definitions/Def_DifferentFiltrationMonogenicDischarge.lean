-- Prove2me | Definitions.Def_DifferentFiltrationMonogenicDischarge
-- name    : DifferentFiltrationMonogenicDischarge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/46b42402-ee59-5ba1-82bc-f0466f1b9a8a
-- title:
--   Monogenic case of the different-versus-ramification-filtration formula
-- statement:
--   This module carries out Serre's computation of the different of a monogenic extension and uses it to discharge the predicate [`DifferentEqPowFiltrationSum`](../def/DifferentFiltrationFormula.html#L76). The first group of lemmas works for a commutative ring $A$, an $A$-algebra $B$ and a group $G$ acting on $B$ by ring automorphisms. [`MulSemiringAction.aeval_smul_minpoly`](../def/DifferentFiltrationMonogenicDischarge.html#L15) records that $\sigma \cdot x$ is again a root of $\mathrm{minpoly}_A(x)$ for every $\sigma \in G$ and $x \in B$ (under `SMulCommClass G A B`). For finite $G$ and $x \in B$ whose minimal polynomial, pushed to $B[X]$, factors as $\prod_{\sigma \in G}(X - \sigma \cdot x)$, [`aeval_derivative_minpoly_eq_prod_sub_smul`](../def/DifferentFiltrationMonogenicDischarge.html#L22) gives $f'(x) = \prod_{\sigma \neq 1}(x - \sigma \cdot x)$, and [`span_aeval_derivative_minpoly_eq_prod_span_smul_sub`](../def/DifferentFiltrationMonogenicDischarge.html#L32) restates this as an equality of ideals $(f'(x)) = \prod_{\sigma \neq 1}(\sigma \cdot x - x)$.
--
--   The second group fixes the standing arithmetic setting: $A$ an integrally closed domain with fraction field $K$, $L/K$ finite separable, $B$ the integral closure of $A$ in $L$, a Dedekind domain and torsion-free as an $A$-module, with the expected scalar towers. [`differentIdeal_eq_span_aeval_derivative_minpoly`](../def/DifferentFiltrationMonogenicDischarge.html#L52) asserts that if $x \in B$ generates $L$ over $K$ and $A[x] = B$, then $\mathfrak{d}_{B/A} = (f'(x))$; [`differentIdeal_eq_prod_span_smul_sub`](../def/DifferentFiltrationMonogenicDischarge.html#L61) combines this with the factorisation. Assuming further that $B$ is local, [`differentIdeal_eq_pow_sum_depthCount_of_monogenic`](../def/DifferentFiltrationMonogenicDischarge.html#L69) shows that if each $(\sigma \cdot x - x)$, $\sigma \neq 1$, equals $\mathfrak{m}_B^{\,d_N(\sigma)}$ with $d_N(\sigma) = \#\{i < N : \sigma \in G_i\}$ the truncated depth count, then $\mathfrak{d}_{B/A} = \mathfrak{m}_B^{\sum_{\sigma \neq 1} d_N(\sigma)}$. Finally [`differentEqPowFiltrationSum_of_monogenic`](../def/DifferentFiltrationMonogenicDischarge.html#L90) converts this, for a cutoff $N$ with $G_N = \bot$, into [`DifferentEqPowFiltrationSum A B G`](../def/DifferentFiltrationFormula.html#L76): for every such cutoff, $\mathfrak{d}_{B/A} = \mathfrak{m}_B^{\sum_{i<N}(\#G_i - 1)}$.
--
--   **Relation to Mathlib.** The different ideal, the conductor and the identities `conductor_mul_differentIdeal` and `conductor_eq_top_of_adjoin_eq_top` are Mathlib's; the lower ramification groups $G_i = \mathrm{inertia}_G(\mathfrak{m}^{i+1})$, the filtration sum $\sum_{i<N}(\#G_i-1)$, the depth count and the predicate [`DifferentEqPowFiltrationSum`](../def/DifferentFiltrationFormula.html#L76) are the project's own definitions built on Mathlib's `Ideal.inertia`. The derivative-factorisation lemmas are project additions.
--
--   **Where it is used.** These results form the local ramification-theory layer supplying Serre's formula $v(\mathfrak{d}) = \sum_{\sigma \neq 1} i_G(\sigma)$ in the monogenic case, the hypotheses `hsplit` (splitting of the minimal polynomial through $G$) and `hdepth` (reading off the span of $\sigma \cdot x - x$ as a power of the maximal ideal) being provided elsewhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DifferentFiltrationMonogenicDischarge.lean

import Definitions.Def_DifferentFiltrationFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra

section DerivativeFactorisation

variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B]

theorem MulSemiringAction.aeval_smul_minpoly [SMulCommClass G A B] (σ : G) (x : B) :
    aeval (σ • x) (minpoly A x) = 0 := by
  have h : aeval (MulSemiringAction.toAlgHom A B σ x) (minpoly A x)
      = MulSemiringAction.toAlgHom A B σ (aeval x (minpoly A x)) :=
    Polynomial.aeval_algHom_apply _ x (minpoly A x)
  rwa [minpoly.aeval, map_zero, MulSemiringAction.toAlgHom_apply] at h

theorem aeval_derivative_minpoly_eq_prod_sub_smul [Fintype G] [DecidableEq G] (x : B)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x))) :
    aeval x (derivative (minpoly A x)) = ∏ σ ∈ Finset.univ.erase (1 : G), (x - σ • x) := by
  rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, hsplit,
    ← Finset.mul_prod_erase Finset.univ (fun σ : G => (X : B[X]) - C (σ • x))
      (Finset.mem_univ (1 : G)),
    one_smul, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_prod]
  exact Finset.prod_congr rfl fun σ _ => by rw [eval_sub, eval_X, eval_C]

theorem span_aeval_derivative_minpoly_eq_prod_span_smul_sub [Fintype G] [DecidableEq G] (x : B)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x))) :
    Ideal.span {aeval x (derivative (minpoly A x))}
      = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • x - x} := by
  rw [aeval_derivative_minpoly_eq_prod_sub_smul x hsplit, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [← neg_sub (σ • x) x, Ideal.span_singleton_neg]

end DerivativeFactorisation

section MonogenicDifferent

variable (A K L B : Type*)
variable [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]

theorem differentIdeal_eq_span_aeval_derivative_minpoly (x : B)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤)
    (hxB : Algebra.adjoin A {x} = ⊤) :
    differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have h := conductor_mul_differentIdeal A K L x hxL
  rwa [conductor_eq_top_of_adjoin_eq_top hxB, ← Ideal.one_eq_top, one_mul] at h

variable (G : Type*) [Group G] [MulSemiringAction G B]

theorem differentIdeal_eq_prod_span_smul_sub [Fintype G] [DecidableEq G] (x : B)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤)
    (hxB : Algebra.adjoin A {x} = ⊤)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x))) :
    differentIdeal A B = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • x - x} := by
  rw [differentIdeal_eq_span_aeval_derivative_minpoly A K L B x hxL hxB,
    span_aeval_derivative_minpoly_eq_prod_span_smul_sub x hsplit]

theorem differentIdeal_eq_pow_sum_depthCount_of_monogenic
    [IsLocalRing B] [Fintype G] [DecidableEq G] (x : B)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤)
    (hxB : Algebra.adjoin A {x} = ⊤)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x)))
    (N : ℕ)
    (hdepth : ∀ σ : G, σ ≠ 1 → Ideal.span {σ • x - x}
        = IsLocalRing.maximalIdeal B ^ lowerRamificationDepthCount B G N σ) :
    differentIdeal A B
      = IsLocalRing.maximalIdeal B
          ^ ∑ σ ∈ Finset.univ.erase (1 : G), lowerRamificationDepthCount B G N σ :=
  calc differentIdeal A B
      = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • x - x} :=
        differentIdeal_eq_prod_span_smul_sub A K L B G x hxL hxB hsplit
    _ = ∏ σ ∈ Finset.univ.erase (1 : G),
          IsLocalRing.maximalIdeal B ^ lowerRamificationDepthCount B G N σ :=
        Finset.prod_congr rfl fun σ hσ => hdepth σ (Finset.ne_of_mem_erase hσ)
    _ = IsLocalRing.maximalIdeal B
          ^ ∑ σ ∈ Finset.univ.erase (1 : G), lowerRamificationDepthCount B G N σ :=
        Finset.prod_pow_eq_pow_sum _ _ _

theorem differentEqPowFiltrationSum_of_monogenic
    [IsLocalRing B] [Fintype G] [DecidableEq G] (x : B)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤)
    (hxB : Algebra.adjoin A {x} = ⊤)
    (hsplit : (minpoly A x).map (algebraMap A B) = ∏ σ : G, (X - C (σ • x)))
    {N : ℕ} (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥)
    (hdepth : ∀ σ : G, σ ≠ 1 → Ideal.span {σ • x - x}
        = IsLocalRing.maximalIdeal B ^ lowerRamificationDepthCount B G N σ) :
    DifferentEqPowFiltrationSum A B G := by
  refine differentEqPowFiltrationSum_of_cutoff hN ?_
  rw [differentIdeal_eq_pow_sum_depthCount_of_monogenic A K L B G x hxL hxB hsplit N hdepth,
    sum_lowerRamificationDepthCount_erase_one]

end MonogenicDifferent


