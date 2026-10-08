-- Prove2me | Definitions.Def_ArtinHecke
-- name    : ArtinHecke
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T09:01:05.875306+00:00
-- url     : https://prove2.me/theorems/31bcdf63-d617-4868-98ae-5c60645b4a8f
-- title:
--   Finite-order Hecke characters (ray-class form), Hecke L-series, zero-free continuation, complete splitting
-- statement:
--   Definitions for the analytic half of OpenAI's *Primitive roots for every admissible integer base* (2026): Theorem 1.2 (p. 3) and §9 (pp. 60–63).
--
--   - `HeckeChar F 𝔪`: a finite-order Hecke character of the number field $F$ of modulus $\mathfrak m$, in ideal form. It is a function $\chi$ from the integral ideals of $F$ to $\mathbb C$ that is completely multiplicative, vanishes exactly on the zero ideal and on the ideals not coprime to $\mathfrak m$, and takes the value $1$ on every principal ideal $(\alpha)$ with $\alpha \in \mathcal O_F$, $\alpha \ne 0$, $\alpha \equiv 1 \pmod{\mathfrak m}$. The paper (p. 2) defines a finite-order Hecke character as “a continuous finite-image character of the idele class group $F^\times \backslash \mathbb A_F^\times$”. For a totally imaginary field such as a cyclotomic field containing $\mu_{12}$, these correspond to characters of ray class groups modulo some $\mathfrak m$, with no conditions at the infinite places. The definition is used only with such fields.
--   - `HeckeChar.coeff χ n`: the sum of $\chi(\mathfrak a)$ over the integral ideals $\mathfrak a$ of norm $n$. `HeckeChar.LSeries χ s`: the series $\sum_{\mathfrak a} \chi(\mathfrak a)\,\mathrm N\mathfrak a^{-s}$, as Mathlib's `LSeries` of these coefficients. It omits the Euler factors at the primes dividing $\mathfrak m$ that the primitive $L_F(s, \eta)$ may have. Those factors $1 - \eta(\mathfrak p)\,\mathrm N\mathfrak p^{-s}$ vanish only on $\operatorname{Re} s = 0$ (p. 60), so zero-free regions to the right of $\operatorname{Re} s = 0$ are the same for both.
--   - `HeckeChar.ZeroFreeRight χ σ`: some function holomorphic on $\{s : \operatorname{Re} s > \sigma,\ s \ne 1\}$ agrees with `χ.LSeries` on $\operatorname{Re} s > 1$ and has no zeros in that region. By the identity theorem such a function is the continuation of the $L$-series, so this says that the continuation exists there and has no zeros, with a pole at $s = 1$ permitted.
--   - `DedekindZeroFreeRight K σ`: the same for Mathlib's `NumberField.dedekindZeta K`.
--   - `SplitsCompletely K p`: the ring of integers of $K$ has exactly $[K : \mathbb Q]$ nonzero prime ideals of absolute norm $p$. This is the standard characterisation of complete splitting of a rational prime.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 2–3, 6, 60–61, §1 (finite-order Hecke characters), §9

import Mathlib

namespace ArtinPrimitiveRoots

open NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- A finite-order Hecke character of `F` of modulus `𝔪`, in its ideal-theoretic form for a
totally imaginary field: a function on the integral ideals of `F` that is completely
multiplicative, vanishes exactly on the ideals that are zero or not coprime to `𝔪`, and is `1`
on every principal ideal `(α)` with `α ≡ 1 (mod 𝔪)`. -/
structure HeckeChar (F : Type*) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) where
  /-- the value on an integral ideal -/
  toFun : Ideal (𝓞 F) → ℂ
  map_mul' : ∀ I J, toFun (I * J) = toFun I * toFun J
  eq_zero_iff' : ∀ I, toFun I = 0 ↔ (I = ⊥ ∨ I ⊔ 𝔪 ≠ ⊤)
  map_principal' : ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 → toFun (Ideal.span {α}) = 1

/-- The coefficient of `n^{-s}` in the Hecke `L`-series: the sum of `χ 𝔞` over the integral
ideals `𝔞` of norm `n`. -/
noncomputable def HeckeChar.coeff {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (n : ℕ) : ℂ :=
  ∑ᶠ I ∈ {I : Ideal (𝓞 F) | Ideal.absNorm I = n}, χ.toFun I

/-- The Hecke `L`-series `L(s, χ) = ∑_𝔞 χ(𝔞) N(𝔞)^{-s}`, as Mathlib's `LSeries` of `χ.coeff`;
it converges for `Re s > 1`. -/
noncomputable def HeckeChar.LSeries {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : ℂ :=
  _root_.LSeries χ.coeff s

/-- `L(s, χ)` continues holomorphically to the region `{Re s > σ, s ≠ 1}` without zeros there:
some function holomorphic on that region agrees with the `L`-series on `Re s > 1` and vanishes
nowhere in the region. -/
def HeckeChar.ZeroFreeRight {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (σ : ℝ) : Prop :=
  ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s | σ < s.re ∧ s ≠ 1} ∧
    (∀ s : ℂ, 1 < s.re → g s = χ.LSeries s) ∧
    ∀ s : ℂ, σ < s.re → s ≠ 1 → g s ≠ 0

/-- The Dedekind zeta function of `K` continues holomorphically to `{Re s > σ, s ≠ 1}` without
zeros there: some function holomorphic on that region agrees with `NumberField.dedekindZeta K`
on `Re s > 1` and vanishes nowhere in the region. -/
def DedekindZeroFreeRight (K : Type*) [Field K] [NumberField K] (σ : ℝ) : Prop :=
  ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s | σ < s.re ∧ s ≠ 1} ∧
    (∀ s : ℂ, 1 < s.re → g s = NumberField.dedekindZeta K s) ∧
    ∀ s : ℂ, σ < s.re → s ≠ 1 → g s ≠ 0

/-- The rational prime `p` splits completely in `K`: `𝓞 K` has `[K : ℚ]` distinct nonzero prime
ideals of absolute norm `p`. -/
def SplitsCompletely (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = p} =
    Module.finrank ℚ K

end ArtinPrimitiveRoots


