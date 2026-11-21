-- Prove2me | Definitions.Def_MasulloGRH_HeckeLFunction
-- name    : MasulloGRH_HeckeLFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:16:39.018265+00:00
-- url     : https://prove2.me/theorems/f7c7e72a-d9c6-4b5c-b3c4-e47380a4c990
-- title:
--   Idele class group, Hecke characters and the finite Hecke $L$-function $L_f(s,\chi)$
-- statement:
--   This file fixes the adelic objects from which the finite Hecke $L$-function is built.
--
--   Let $F$ be a number field with ring of integers $\mathcal O_F$ and adele ring $\mathbb A_F$.
--
--   1. The **idele group** $\mathrm{GL}_1(\mathbb A_F)$ is the group of units of $\mathbb A_F$, with the topology induced by $x\mapsto(x,x^{-1})$.
--   2. The **principal ideles** are the image of $F^\times$ under the diagonal embedding $F^\times\to\mathrm{GL}_1(\mathbb A_F)$.
--   3. The **idele class group** is the quotient $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$ with the quotient topology.
--   4. A **Hecke character** is a continuous homomorphism $\chi\colon C_F\to U(1)$, i.e. an element of the Pontryagin dual $\widehat{C_F}$.
--   5. For a finite place $v$ and $x\in F_v^\times$, the idele $j_v(x)$ has coordinate $x$ at $v$ and coordinate $1$ at every other place, finite or Archimedean. The **local component** of $\chi$ at $v$ is
--   $$\chi_v(x)=\chi\big(j_v(x)\bmod F^\times\big),\qquad x\in F_v^\times .$$
--   6. $\chi$ is **unramified** at $v$ if $\chi_v(u)=1$ for every $u\in F_v^\times$ with $|u|_v=1$, i.e. for every unit $u\in\mathcal O_{F_v}^\times$.
--   7. A **uniformizer** at $v$ is an element $\pi_v\in F_v^\times$ whose valuation is the generator of the value group that is smaller than $1$.
--   8. The **value at the prime** $\mathfrak p_v$ is
--   $$\chi(\mathfrak p_v)=\begin{cases}\chi_v(\pi_v)&\text{if }\chi\text{ is unramified at }v,\\[2pt] 0&\text{if }\chi\text{ is ramified at }v,\end{cases}$$
--   where $\pi_v$ is any uniformizer at $v$. In the unramified case the value does not depend on the choice of $\pi_v$.
--   9. The **Euler product** of the finite Hecke $L$-function is
--   $$\prod_{v\in\Sigma_{F,f}}\frac{1}{1-\chi(\mathfrak p_v)\,N(\mathfrak p_v)^{-s}},$$
--   the product over all finite places $v$ of $F$, where $N(\mathfrak p_v)$ is the absolute norm of the prime ideal of $v$. The factors at the ramified places are $1$, so this is the product over $v\in\Sigma_{F,f}\setminus S_\chi$ of Definition 3.2.1.4. For $\operatorname{Re}(s)>1$ the product converges absolutely and its value is $L_f(s,\chi)$.
--
--   10. The **finite Hecke $L$-function** $L_f(s,\chi)$ on all of $\mathbb C$ is the meromorphic continuation of the Euler product in item 9. It is taken in normal form: at a pole its value is $0$, and elsewhere it is the value of the continuation. The continuation is unique. If the Euler product had no meromorphic continuation to $\mathbb C$, the function would be defined to be identically $0$; the existence of the continuation is a separate statement of the mission.
--
--   These definitions are the common base of every statement about Hecke $L$-functions in the mission. For $F=\mathbb Q$ and $\chi=1$ the Euler product is that of the Riemann zeta function.
--
--   **Formalization Note** The adele ring is Mathlib's `NumberField.AdeleRing (𝓞 F) F`, the product of the infinite adele ring and the finite adele ring. The Euler product is an unconditional infinite product, which takes the value $1$ when the product does not converge. The continuation in item 10 is selected among the functions that are meromorphic in normal form on $\mathbb C$ and agree with the Euler product for $\operatorname{Re}(s)>1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Notation and terminology (p. 7); §3.1.2 (pp. 120–121); §3.2.1 (pp. 122–124), Definition 3.2.1.4, eq. (3.2.1.7)

import Mathlib

/-!
# Hecke characters and finite Hecke L-functions

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026),
"Notation and terminology" (p. 7), §3.1.2 (pp. 120–121) and §3.2.1 (pp. 122–124),
in particular Definition 3.2.1.4, equation (3.2.1.7) and the paragraph after it.
-/

namespace MasulloGRH

open NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The idele group `GL₁(𝔸_F)` of the number field `F`: the group of units of the adele ring,
with the units topology (the topology induced by `x ↦ (x, x⁻¹)`). -/
abbrev IdeleGroup : Type _ := (AdeleRing (𝓞 F) F)ˣ

/-- The diagonal embedding `Fˣ → GL₁(𝔸_F)`. -/
def principalIdele : Fˣ →* IdeleGroup F :=
  Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom

/-- The subgroup of principal ideles, i.e. the image of `Fˣ` in `GL₁(𝔸_F)`. -/
def principalIdeles : Subgroup (IdeleGroup F) := (principalIdele F).range

/-- The idele class group `C_F = GL₁(𝔸_F) / Fˣ`, with the quotient topology. -/
abbrev IdeleClassGroup : Type _ := IdeleGroup F ⧸ principalIdeles F

/-- A Hecke character of `F`: a continuous homomorphism `C_F → U(1)`, i.e. an element of the
Pontryagin dual of the idele class group. -/
abbrev HeckeCharacter : Type _ := PontryaginDual (IdeleClassGroup F)

variable {F}

open Classical in
/-- The finite idele whose coordinate at the finite place `v` is `x` and whose coordinate at
every other finite place is `1`. -/
def finiteIdeleSingle (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    (FiniteAdeleRing (𝓞 F) F)ˣ :=
  (RestrictedProduct.unitsEquiv (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)).symm
    (RestrictedProduct.mulSingle
      (fun w : HeightOneSpectrum (𝓞 F) =>
        (Submonoid.ofClass (w.adicCompletionIntegers F)).units) v x)

/-- The insertion `j_v : F_vˣ → GL₁(𝔸_F)` at a finite place `v`: the idele whose coordinate at
`v` is `x` and whose coordinate at every other place, finite or infinite, is `1`. -/
def ideleSingle (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) : IdeleGroup F :=
  MulEquiv.prodUnits.symm (1, finiteIdeleSingle v x)

/-- The local component `χ_v` of a Hecke character `χ` at a finite place `v`, as a function on
`F_vˣ`: the value of `χ` on the class of the idele `j_v(x)`. -/
def HeckeCharacter.localComponent (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x : (v.adicCompletion F)ˣ) : ℂ :=
  ((χ (QuotientGroup.mk (ideleSingle v x)) : Circle) : ℂ)

/-- `χ` is unramified at the finite place `v` if `χ_v` is trivial on the units `𝒪_{F_v}ˣ`,
i.e. on the elements of `F_vˣ` of valuation `1`. -/
def HeckeCharacter.IsUnramifiedAt (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : (v.adicCompletion F)ˣ, Valued.v (x : v.adicCompletion F) = 1 → χ.localComponent v x = 1

/-- `x ∈ F_vˣ` is a uniformizer at `v` if its valuation generates the value group, i.e. it is
the largest value smaller than `1`: `v(x) = exp (-1)` in `ℤᵐ⁰`. -/
def IsUniformizerAt (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion F) = WithZero.exp (-1 : ℤ)

open Classical in
/-- The value `χ(𝔭_v)` of a Hecke character at the prime ideal of a finite place `v`:
`χ_v(π_v)` for a uniformizer `π_v` if `χ` is unramified at `v` (the value does not depend on the
choice of `π_v`), and `0` if `χ` is ramified at `v`. -/
def HeckeCharacter.primeValue (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if h : χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x then
    χ.localComponent v h.2.choose
  else 0

/-- The Euler product of the finite Hecke L-function (Definition 3.2.1.4, (3.2.1.7)):
`∏_v (1 - χ(𝔭_v) N(𝔭_v)^{-s})⁻¹`, the product over all finite places `v`, with `χ(𝔭_v) = 0`
at the ramified places, so that the ramified factors are `1`. It is the value of the finite Hecke
L-function `L_f(s, χ)` for `Re s > 1`, where the product converges absolutely. -/
def heckeEulerProduct (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ∏' v : HeightOneSpectrum (𝓞 F),
    (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹

open Classical in
/-- The finite Hecke L-function `L_f(s, χ)` as a function on the whole complex plane: the
meromorphic continuation of the Euler product `heckeEulerProduct χ`, taken in normal form
(at a pole the value is `0`, at every other point it is the value of the continuation).
Such a continuation is unique if it exists; if none exists the function is identically `0`. -/
def heckeLFunction (χ : HeckeCharacter F) : ℂ → ℂ :=
  if h : ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = heckeEulerProduct χ s then
    h.choose
  else 0

end

end MasulloGRH


