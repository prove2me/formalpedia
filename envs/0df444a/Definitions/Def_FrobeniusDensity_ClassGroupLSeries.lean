-- Prove2me | Definitions.Def_FrobeniusDensity_ClassGroupLSeries
-- name    : FrobeniusDensity_ClassGroupLSeries
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/3539501e-899f-5c13-bf5c-926a9332006e
-- title:
--   Partial Dedekind zeta functions and class-group L-series
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal{O}_K$. For an ideal class $C \in$ `ClassGroup (𝓞 K)` and $n : \mathbb{N}$, `classZetaCoeff K C n` is the `Nat.card` of the subtype of elements $I$ of the non-zero-divisor submonoid $(\mathrm{Ideal}\,\mathcal{O}_K)^{0}$ of the multiplicative monoid of ideals (i.e. of nonzero integral ideals) satisfying `absNorm` $I = n$ together with `ClassGroup.mk0 I = C`; so it counts the integral ideals of absolute norm $n$ lying in the class $C$. The partial zeta function `classZeta K C` is Mathlib's `LSeries` applied to these coefficients, cast to $\mathbb{C}$, i.e. $\sum_{n\ge 1} a_C(n) n^{-s}$ (the `LSeries` convention discards the index $0$ term).
--
--   `classResidue K` is the real number
--   $$\frac{2^{r_1}(2\pi)^{r_2} R_K}{w_K\sqrt{|d_K|}},$$
--   with $r_1 =$ `nrRealPlaces K`, $r_2 =$ `nrComplexPlaces K`, $R_K =$ `regulator K`, $w_K =$ `torsionOrder K` the order of the torsion subgroup of the units, and $d_K =$ `discr K`; this is the analytic class number formula constant with the class number removed.
--
--   Characters are taken to be monoid homomorphisms $\chi :$ `ClassGroup (𝓞 K) →* ℂ`, so $\chi(1) = 1$ and the values are roots of unity. For such a $\chi$, `classGroupLSeries K χ s` is the finite sum $\sum_{C} \chi(C)\,$`classZeta K C s` over the class group.
--
--   Finally, `LSeriesInheritsPole K χ` is the predicate asserting the existence of a real $c > 0$ such that, eventually in the filter $\mathcal{N}[>]1$ of real numbers approaching $1$ from above, $c \le \|(s-1)\,$`classGroupLSeries K χ s`$\|$ (with $s$ coerced to $\mathbb{C}$): the $L$-series retains a pole, rather than being regular, at $s = 1$.
--
--   **Relation to Mathlib.** Built on Mathlib's `LSeries`, `ClassGroup`/`ClassGroup.mk0`, `absNorm`, `regulator`, `torsionOrder`, `discr` and the counts of real and complex infinite places; the decomposition of the Dedekind zeta function into partial zeta functions of individual ideal classes, the associated class-group $L$-series and the pole predicate are the project's own.
--
--   **Where it is used.** These are the analytic objects used in the argument that the classes of the degree-one primes generate the ideal class group (the statement that an ideal class character trivial on degree-one primes is trivial), which feeds the class-group input of the Stickelberger–Herbrand branch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FrobeniusDensity_ClassGroupLSeries.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter Ideal NumberField NumberField.InfinitePlace NumberField.Units Topology
  nonZeroDivisors

open scoped Real

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

def classZetaCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C}

def classZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ classZetaCoeff K C n) s

def classResidue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
    (torsionOrder K * Real.sqrt |discr K|)

def classGroupLSeries (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K), χ C * classZeta K C s

def LSeriesInheritsPole (χ : ClassGroup (𝓞 K) →* ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ s : ℝ in 𝓝[>] 1, c ≤ ‖(fun s : ℝ ↦ (s - 1) * classGroupLSeries K χ s) s‖

end

end FrobeniusDensity


