-- Prove2me | Definitions.Def_FrobeniusDensity_DegOneAsymptotic
-- name    : FrobeniusDensity_DegOneAsymptotic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/9ebfda3d-953a-56c9-9afb-478353a7b926
-- title:
--   Degree-one prime counts and their Dirichlet-series asymptotic
-- statement:
--   Two declarations. First, for a number field $K$ and a natural number $\ell$, [`FrobeniusDensity.degOneCount K ℓ`](../def/FrobeniusDensity_DegOneAsymptotic.html#L22) is defined to be $0$ unless $\ell$ is prime, in which case it is the `Set.ncard` of the set of primes $\mathfrak q$ of $\mathcal O_K$ lying over the ideal $\ell\mathbb Z$ (Mathlib's `Ideal.primesOver`, with `ratPrimeIdeal ℓ = Ideal.span {(ℓ : ℤ)}` from the project's Taylor–Wiles-primes module) whose residue ring has exactly $\ell$ elements; that is, the number of degree-one primes of $K$ above $\ell$.
--
--   Second, for a finite Galois extension $L/\mathbb Q$ (a number field $L$ with `IsGalois ℚ L`), [`FrobeniusDensity.DegOneAsymptotic L`](../def/FrobeniusDensity_DegOneAsymptotic.html#L33) is a proposition, not a theorem: it asserts that for every subgroup $H \le \mathrm{Gal}(L/\mathbb Q)$ and every finite set $S_0$ of natural numbers, writing $E = L^H$ for the intermediate field of $H$-fixed points (Mathlib's `FixedPoints.intermediateField`, which is again a number field), the coefficients $a_\ell = \mathrm{degOneCount}(E,\ell)$ truncated by setting $a_\ell = 0$ for $\ell \in S_0$ satisfy: (i) for every real $s > 1$ the family $\ell \mapsto a_\ell\,\ell^{-s}$ (real `rpow`, summed over all natural $\ell$) is summable; and (ii) the function
--   $$s \mapsto \Big(\sum_{\ell} a_\ell\,\ell^{-s}\Big) + \log(s-1)$$
--   is $O(1)$ along the filter $\mathcal N[>]1$, i.e. as $s \to 1^+$. So the content is $\sum_{\ell \notin S_0} \#\{\text{degree-one primes of } E \text{ above } \ell\}\,\ell^{-s} = -\log(s-1) + O(1)$, uniformly only in the sense that the statement is quantified over all $H$ and all $S_0$ separately. Both the quantification over subgroups and the allowance for an arbitrary finite excluded set are what the later Möbius-inversion argument needs.
--
--   **Relation to Mathlib.** `degOneCount` is built from Mathlib's `Ideal.primesOver`, `Nat.card` and `Set.ncard`, and the fixed field is Mathlib's `FixedPoints.intermediateField`; the packaging of the degree-one prime sum asymptotic as a `Prop` parameterised by $L$ is the project's own, Mathlib having no Dedekind zeta pole or prime-density statement in this form.
--
--   **Where it is used.** This is the analytic half of Frobenius's density theorem in the form the project uses, namely [`FrobeniusDensity.Statement L`](../def/TaylorWiles_Primes.html#L72): for every $\sigma \in \mathrm{Gal}(L/\mathbb Q)$ and every finite set $S$ of primes there is $\ell \notin S$ with `RealizesCyclicAt L σ ℓ`. That density statement is in turn what produces primes $q \equiv 1 \pmod{p^n}$ at which the residual representation has Frobenius with distinct rational eigenvalues, i.e. Taylor–Wiles primes in the sense of [`TaylorWiles.IsTaylorWilesPrime`](../def/TaylorWiles_Primes.html#L90), used to augment the deformation problem in the Taylor–Wiles patching argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FrobeniusDensity_DegOneAsymptotic.lean

import Definitions.Def_TaylorWiles_Primes
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Fixed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal
open Filter Topology Asymptotics

namespace FrobeniusDensity

open NumberField Ideal

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

noncomputable def degOneCount (ℓ : ℕ) : ℕ :=
  if ℓ.Prime then
    {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard
  else 0

end DegOneCount

section AnalyticInput

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

def DegOneAsymptotic : Prop :=
  ∀ (H : Subgroup (L ≃ₐ[ℚ] L)) (S₀ : Finset ℕ),
    (∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s))) ∧
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ))

end AnalyticInput

end FrobeniusDensity


