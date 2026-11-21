-- Prove2me | Definitions.Def_MasulloGRH_CompletedL
-- name    : MasulloGRH_CompletedL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:36:43.238939+00:00
-- url     : https://prove2.me/theorems/799c7f6a-f757-49f0-94c6-c6bcd0820064
-- title:
--   The completed Hecke $L$-function $L(s,\chi)$, the measure $\mu_1$ on $C_F^1$, and the isotypes $H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbb A_F))$
-- statement:
--   Let $F$ be a number field and $\chi$ a Hecke character of $F$.
--
--   **Archimedean factors.** For an Archimedean place $v$ let $\chi_v$ be the local component of $\chi$ on $F_v^\times$, embedded in the $v$-th coordinate of the ideles.
--
--   1. If $v$ is real, $\chi_v(x)=\operatorname{sgn}(x)^{a_v}|x|^{it_v}$ with $a_v\in\{0,1\}$, $t_v\in\mathbb R$, and
--   $$L(\chi_v|\cdot|_v^s)=\pi^{-(s+it_v+a_v)/2}\,\Gamma\Big(\frac{s+it_v+a_v}{2}\Big).$$
--   2. If $v$ is complex, $\chi_v(z)=(z/|z|)^{n_v}|z|_v^{it_v}$ with $n_v\in\mathbb Z$, $t_v\in\mathbb R$ and $|z|_v=|z|^2$, and
--   $$L(\chi_v|\cdot|_v^s)=(2\pi)^{-(s+it_v+|n_v|/2)}\,\Gamma\Big(s+it_v+\frac{|n_v|}{2}\Big).$$
--   3. $\Gamma_F(s,\chi)=\prod_{v\mid\infty}L(\chi_v|\cdot|_v^s)$.
--   4. The **completed Hecke $L$-function** is the meromorphic function
--   $$L(s,\chi)=\Gamma_F(s,\chi)\,L_f(s,\chi),$$
--   which for $\operatorname{Re}(s)>1$ is the product (3.2.1.2).
--
--   **Homogeneous $\theta$-functions.**
--
--   5. $C_F^1\subset C_F$ is the subgroup of classes of idelic norm $1$, and $\mu_1$ is the **Tamagawa measure** on $C_F^1$: the invariant measure of total mass $\mu_1(C_F^1)=2^{r_1}(2\pi)^{r_2}h_FR_F/(|d_F|^{1/2}w_F)$.
--   6. For $\omega=\chi|_{C_F^1}$ and $f\in\mathcal S(\mathbb A_F)$, the **$\omega$-homogeneous global adelic $\theta$-function** is
--   $$\Phi_{F,\omega}(f)(g)=\int_{C_F^1}\Phi_F(f)(hg)\,\omega(h)\,d\mu_1(h).$$
--   7. The **isotype** is the quotient $H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbb A_F))=\mathcal S(\mathbb A_F)/\ker\Phi_{F,\omega}$ with the quotient topology.
--
--   The isotypes decompose the space of global $\theta$-functions according to the characters of the compact group $C_F^1$; the Mellin transform maps the $\omega$-isotype to functions on the component $\{\chi|\cdot|_F^s\}$ of $\Omega(C_F)$.
--
--   **Formalization Note** The parameters $a_v$, $t_v$, $|n_v|$ are read off from $\chi_v$: $t_v$ from its values on the positive real ray, $a_v$ from $\chi_v(-1)$, and $|n_v|$ from its values on the unit circle. $L(s,\chi)$ is taken in meromorphic normal form (value $0$ at poles). $\mu_1$ is a measure on $C_F$ supported on $C_F^1$, selected by its characterizing properties. A character $\omega$ of $C_F^1$ is given as the restriction of a Hecke character.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Lemma 3.2.1.1 and Definition 3.2.1.2, eqs. (3.2.1.2)–(3.2.1.5) (p. 123); Definition A.3.2.1 (pp. 559–560); Definition 2.2.5.1, eq. (2.2.5.2) (p. 95); Definition 5.2.2.1, eq. (5.2.2.3) (p. 232)

import Definitions.Def_MasulloGRH_ThetaSpaces
import Definitions.Def_MasulloGRH_ExpDecaySpaces

/-!
# The completed Hecke L-function, the measure on `C_F^1`, homogeneous θ-functions and isotypes

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026): Lemma 3.2.1.1 and
Definition 3.2.1.2, eqs. (3.2.1.2)–(3.2.1.5) (p. 123); Definition A.3.2.1 (pp. 559–560);
Definition 2.2.5.1, eq. (2.2.5.2) (p. 95); Definition 5.2.2.1, eq. (5.2.2.3) (p. 232).
-/

namespace MasulloGRH

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### Archimedean local components and Γ-factors -/

open Classical in
/-- The idele whose coordinate at the infinite place `w` is `x` and whose coordinate at every
other place is `1`. -/
def ideleSingleInfinite (w : InfinitePlace F) (x : (w.Completion)ˣ) : IdeleGroup F :=
  MulEquiv.prodUnits.symm
    (MulEquiv.piUnits.symm (Pi.mulSingle w x), (1 : (FiniteAdeleRing (𝓞 F) F)ˣ))

/-- The local component `χ_w` of a Hecke character at an infinite place `w`, a function on
`F_wˣ`. -/
def HeckeCharacter.localComponentInfinite (χ : HeckeCharacter F) (w : InfinitePlace F)
    (x : (w.Completion)ˣ) : ℂ :=
  ((χ (QuotientGroup.mk (ideleSingleInfinite w x)) : Circle) : ℂ)

open Classical in
/-- The real number `t_w` with `χ_w(x) = |x|_w^{i t_w}` for all `x ∈ F_wˣ` whose image in `ℂ` is
a positive real number (`|·|_w` is the normalized absolute value). -/
def HeckeCharacter.archExponent (χ : HeckeCharacter F) (w : InfinitePlace F) : ℝ :=
  if h : ∃ t : ℝ, ∀ x : (w.Completion)ˣ,
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
      0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re →
      χ.localComponentInfinite w x =
        ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ (t * Complex.I) then
    h.choose
  else 0

open Classical in
/-- The parity `a_w ∈ {0, 1}` of `χ` at a real place `w`: `χ_w(-1) = (-1)^{a_w}`. -/
def HeckeCharacter.archParity (χ : HeckeCharacter F) (w : InfinitePlace F) : ℕ :=
  if χ.localComponentInfinite w (-1) = 1 then 0 else 1

open Classical in
/-- The absolute value `|n_w|` of the weight of `χ` at a complex place `w`:
`χ_w(z) = z^{n_w}` for `|z| = 1` (for one of the two identifications `F_w ≅ ℂ`). -/
def HeckeCharacter.archWeight (χ : HeckeCharacter F) (w : InfinitePlace F) : ℕ :=
  if h : ∃ n : ℤ, ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x =
        (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ^ n then
    h.choose.natAbs
  else 0

open Classical in
/-- The Archimedean local factor `L(χ_w |·|_w^s)` of (3.2.1.4)–(3.2.1.5): for `w` real with
`χ_w = sgn^a |·|^{it}` it is `π^{-(s+it+a)/2} Γ((s+it+a)/2)`; for `w` complex with
`χ_w(z) = (z/|z|)^n |z|_w^{it}` it is `(2π)^{-(s+it+|n|/2)} Γ(s+it+|n|/2)`. -/
def HeckeCharacter.archLFactor (χ : HeckeCharacter F) (w : InfinitePlace F) (s : ℂ) : ℂ :=
  if w.IsReal then
    (Real.pi : ℂ) ^ (-((s + χ.archExponent w * Complex.I + χ.archParity w) / 2)) *
      Complex.Gamma ((s + χ.archExponent w * Complex.I + χ.archParity w) / 2)
  else
    (2 * Real.pi : ℂ) ^ (-(s + χ.archExponent w * Complex.I + (χ.archWeight w : ℂ) / 2)) *
      Complex.Gamma (s + χ.archExponent w * Complex.I + (χ.archWeight w : ℂ) / 2)

/-- The factor `Γ_F(s, χ) = ∏_{w | ∞} L(χ_w |·|_w^s)` of (3.2.1.3). -/
def HeckeCharacter.gammaFactor (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ∏ w : InfinitePlace F, χ.archLFactor w s

/-- The completed Hecke L-function `L(s, χ) = Γ_F(s, χ) L_f(s, χ)` (Definition 3.2.1.2), as a
meromorphic function on `ℂ` in normal form. -/
def completedHeckeLFunction (χ : HeckeCharacter F) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s => χ.gammaFactor s * heckeLFunction χ s) Set.univ

/-! ### The measure on `C_F^1` and homogeneous θ-functions -/

variable (F)

/-- The subgroup `C_F^1` of the idele class group, as a set: the classes of the ideles of
norm `1`. -/
def ideleClassNormOne : Set (IdeleClassGroup F) :=
  (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' {g | ideleNorm g = 1}

open Classical in
/-- The Tamagawa measure `μ₁` on `C_F^1` (Definition A.3.2.1), as a measure on `C_F` supported on
`C_F^1`: the measure invariant under translation by `C_F^1` with total mass `μ₁(C_F^1)` of
(A.3.2.1). -/
def tamagawaNormOne : Measure (IdeleClassGroup F) :=
  if h : ∃ μ : Measure (IdeleClassGroup F), μ (ideleClassNormOne F)ᶜ = 0 ∧
      μ Set.univ = ENNReal.ofReal (tamagawaClassVolume F) ∧
      ∀ x ∈ ideleClassNormOne F, μ.map (fun y => x * y) = μ then
    h.choose
  else 0

variable {F}

/-- Definition 2.2.5.1: the `ω`-homogeneous global adelic θ-function
`Φ_{F,ω}(f)(g) = ∫_{C_F^1} Φ_F(f)(h g) ω(h) dμ₁(h)`, for `ω = χ|_{C_F^1}` the restriction of a
Hecke character `χ`. -/
def adelicThetaHomogeneous (χ : HeckeCharacter F) (f : AdelicSchwartz F) (g : IdeleGroup F) : ℂ :=
  ∫ x : IdeleClassGroup F, adelicTheta f (x.out * g) * ((χ x : Circle) : ℂ) ∂(tamagawaNormOne F)

/-- The kernel of the operator `Φ_{F,ω}`, `ω = χ|_{C_F^1}`. -/
def adelicThetaHomogeneousKernel (χ : HeckeCharacter F) : Submodule ℂ (AdelicSchwartz F) :=
  Submodule.span ℂ {f | ∀ g : IdeleGroup F, adelicThetaHomogeneous χ f g = 0}

/-- Definition 5.2.2.1(1): the isotype `H_{0,cont}(ω, S(𝔸_F)) = S(𝔸_F) / ker Φ_{F,ω}` for
`ω = χ|_{C_F^1}`, with the quotient topology. -/
abbrev ThetaIsotype (χ : HeckeCharacter F) : Type _ :=
  AdelicSchwartz F ⧸ adelicThetaHomogeneousKernel χ

end

end MasulloGRH


