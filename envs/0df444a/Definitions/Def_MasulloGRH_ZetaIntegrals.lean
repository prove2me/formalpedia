-- Prove2me | Definitions.Def_MasulloGRH_ZetaIntegrals
-- name    : MasulloGRH_ZetaIntegrals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:28:31.155436+00:00
-- url     : https://prove2.me/theorems/d24f06a4-cf60-4ca3-a771-9539943bf878
-- title:
--   Quasi-characters of $C_F$, Tamagawa measures on ideles, and the global zeta integral $Z(f,c)$
-- statement:
--   This file defines the measures and the Mellin transforms of Tate's thesis on the idele class group of a number field $F$.
--
--   1. $\mu_1(C_F^1)$ is the number
--   $$\frac{2^{r_1}(2\pi)^{r_2}h_FR_F}{|d_F|^{1/2}w_F},$$
--   with $r_1,r_2$ the numbers of real and complex places, $h_F$ the class number, $R_F$ the regulator, $d_F$ the discriminant and $w_F$ the number of roots of unity of $F$.
--   2. The **Tamagawa measure** $\bar\mu$ on the idele class group $C_F$ is the Haar measure that, together with $dt/t$ on $\mathbb R_{>0}\cong C_F/C_F^1$, gives $C_F^1$ the volume $\mu_1(C_F^1)$; equivalently $\bar\mu(\{x\in C_F:1\le|x|_F<e\})=\mu_1(C_F^1)$.
--   3. The **Tamagawa measure** $\mu$ on the idele group $\mathrm{GL}_1(\mathbb A_F)$ is the Haar measure that induces $\bar\mu$ on $C_F$ with the counting measure on $F^\times$: a measurable set on which the projection to $C_F$ is injective has the measure of its image.
--   4. A **quasi-character** of $C_F$ is a continuous homomorphism $c\colon\mathrm{GL}_1(\mathbb A_F)\to\mathbb C^\times$ that is trivial on $F^\times$. Its **abscissa** $\sigma(c)$ is the real number with $|c(g)|=|g|_F^{\sigma(c)}$ for all $g$.
--   5. $|\cdot|_F^s$ is the quasi-character $g\mapsto|g|_F^s$, the **twist** of $c$ is $c|\cdot|_F^s$, and the **dual** quasi-character is $\widehat c=|\cdot|_F\,c^{-1}$.
--   6. The **global zeta integral**, or Mellin transform, of a function $f$ on the adeles is
--   $$Z(f,c)=\int_{\mathrm{GL}_1(\mathbb A_F)}f(g)\,c(g)\,d\mu(g).$$
--   7. The Mellin transform of the $\theta$-function of $f\in\mathcal S(\mathbb A_F)$ is
--   $$L(f,c)=\int_{C_F}\Phi_F(f)(g)\,c(g)\,d\bar\mu(g).$$
--
--   The quasi-characters form the Riemann surface $\Omega(C_F)$; each connected component is $\{c_0|\cdot|_F^s:s\in\mathbb C\}$, and functions on $\Omega(C_F)$ are studied as functions of $s$.
--
--   **Formalization Note** Quasi-characters are functions on the idele group. $\mu_1(C_F^1)$ is Mathlib's `dedekindZeta_residue`, which is defined by the same formula. The two measures are selected by their characterizing properties. In item 7 the integrand is evaluated on a representative idele of each class.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, §3.1.1, Definitions 3.1.1.1–3.1.1.2, eq. (3.1.1.4) (pp. 118–119); Definition A.3.2.1, eq. (A.3.2.1) (pp. 559–560); Theorem 3.2.2.1, eqs. (3.2.2.1), (3.2.2.3) (p. 124); Definition 3.2.2.5 (p. 128)

import Definitions.Def_MasulloGRH_AdelicTheta

/-!
# Quasi-characters of the idele class group, Tamagawa measures, global zeta integrals

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026): §3.1.1 and
Definitions 3.1.1.1–3.1.1.2, eq. (3.1.1.4) (pp. 118–119); Definition A.3.2.1 and eq. (A.3.2.1)
(pp. 559–560); Theorem 3.2.2.1, eqs. (3.2.2.1) and (3.2.2.3) (p. 124); Definition 3.2.2.5 (p. 128).
-/

namespace MasulloGRH

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The Borel σ-algebra of the idele group. -/
scoped instance ideleMeasurableSpace : MeasurableSpace (IdeleGroup F) := borel _

scoped instance ideleBorelSpace : BorelSpace (IdeleGroup F) := ⟨rfl⟩

/-- The Borel σ-algebra of the idele class group. -/
scoped instance ideleClassMeasurableSpace : MeasurableSpace (IdeleClassGroup F) := borel _

scoped instance ideleClassBorelSpace : BorelSpace (IdeleClassGroup F) := ⟨rfl⟩

/-- The volume `μ₁(C_F^1) = 2^{r₁} (2π)^{r₂} h_F R_F / (|d_F|^{1/2} w_F)` of (A.3.2.1). -/
def tamagawaClassVolume : ℝ := dedekindZeta_residue F

open Classical in
/-- The Tamagawa measure `\bar μ` on the idele class group `C_F` (Definition A.3.2.1): the Haar
measure which, together with `dt/t` on `ℝ_{>0} ≅ C_F / C_F^1`, induces on `C_F^1` a measure of
total mass `μ₁(C_F^1)`; equivalently the set of classes of norm in `[1, e)` has measure
`μ₁(C_F^1)`. -/
def tamagawaIdeleClass : Measure (IdeleClassGroup F) :=
  if h : ∃ μ : Measure (IdeleClassGroup F), μ.IsHaarMeasure ∧
      μ ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
        {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
        ENNReal.ofReal (tamagawaClassVolume F) then
    h.choose
  else 0

open Classical in
/-- The Tamagawa measure `μ` on the idele group `GL₁(𝔸_F)` (Definition A.3.2.1): the Haar measure
which, with the counting measure on `Fˣ`, induces the Tamagawa measure on `C_F`; a measurable set
on which the projection to `C_F` is injective has the measure of its image. -/
def tamagawaIdele : Measure (IdeleGroup F) :=
  if h : ∃ μ : Measure (IdeleGroup F), μ.IsHaarMeasure ∧
      ∀ D : Set (IdeleGroup F), MeasurableSet D →
        Set.InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) D →
        μ D = tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' D) then
    h.choose
  else 0

variable {F}

/-- A quasi-character of the idele class group `C_F` (§3.1.1), as a function on the idele group:
a continuous homomorphism `GL₁(𝔸_F) → ℂˣ` that is trivial on `Fˣ`. -/
def IsQuasiCharacter (c : IdeleGroup F → ℂ) : Prop :=
  Continuous c ∧ (∀ g h : IdeleGroup F, c (g * h) = c g * c h) ∧ (∀ g : IdeleGroup F, c g ≠ 0) ∧
    ∀ ξ : Fˣ, c (principalIdele F ξ) = 1

open Classical in
/-- The abscissa `σ(c)` of a quasi-character (Definition 3.1.1.1): the real number `σ` with
`|c(g)| = |g|_F^σ` for all `g`. -/
def quasiAbscissa (c : IdeleGroup F → ℂ) : ℝ :=
  if h : ∃ σ : ℝ, ∀ g : IdeleGroup F, ‖c g‖ = ideleNorm g ^ σ then h.choose else 0

/-- The quasi-character `|·|_F^s`. -/
def normQuasiChar (s : ℂ) : IdeleGroup F → ℂ := fun g => ((ideleNorm g : ℝ) : ℂ) ^ s

/-- The twist `c |·|_F^s` of a quasi-character `c`. -/
def quasiTwist (c : IdeleGroup F → ℂ) (s : ℂ) : IdeleGroup F → ℂ := fun g => c g * normQuasiChar s g

/-- The dual quasi-character `\hat c = |·|_F c⁻¹` (3.1.1.4). -/
def quasiDual (c : IdeleGroup F → ℂ) : IdeleGroup F → ℂ :=
  fun g => ((ideleNorm g : ℝ) : ℂ) * (c g)⁻¹

/-- The global zeta integral `Z(φ, c) = ∫_{GL₁(𝔸_F)} φ(g) c(g) dμ(g)` (3.2.2.1) of a function `φ`
on the adeles. -/
def zetaIntegralFun (φ : AdeleRing (𝓞 F) F → ℂ) (c : IdeleGroup F → ℂ) : ℂ :=
  ∫ g : IdeleGroup F, φ (g : AdeleRing (𝓞 F) F) * c g ∂(tamagawaIdele F)

/-- The global zeta integral `Z(f, c)` of `f ∈ S(𝔸_F)` (3.2.2.1), the Mellin transform of `f`. -/
def zetaIntegral (f : AdelicSchwartz F) (c : IdeleGroup F → ℂ) : ℂ := zetaIntegralFun f.eval c

/-- The Mellin transform `L(f, c) = ∫_{C_F} Φ_F(f)(g) c(g) d\bar μ(g)` of the adelic θ-function
of `f` (3.2.2.3). -/
def thetaMellin (f : AdelicSchwartz F) (c : IdeleGroup F → ℂ) : ℂ :=
  ∫ x : IdeleClassGroup F, adelicTheta f x.out * c x.out ∂(tamagawaIdeleClass F)

end

end MasulloGRH


