-- Prove2me | Definitions.Def_MasulloGRH_SLocalZetaIntegrals
-- name    : MasulloGRH_SLocalZetaIntegrals
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:22:31.108204+00:00
-- url     : https://prove2.me/theorems/16b8fd9f-c2b3-4198-a56f-2966b0900017
-- title:
--   §3.3.1, eqs. (3.3.1.1)–(3.3.1.3) — $S$-local zeta integrals $Z_S(f,c)$, the $S$-adelic Fourier transform, quasi-characters of $\mathrm{GL}_1(\mathbb A_{F,S})$ and the factor $\rho_S(c)$
-- statement:
--   **$S$-local zeta integrals and the objects of the $S$-local functional equation** (§3.3.1 and Theorem 3.3.1.1, eqs. (3.3.1.1)–(3.3.1.3), of the source, with the notation $\widehat c$ of (3.1.1.4)).
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$ be the ring of $S$-adeles, $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ the group of $S$-ideles with the $S$-idelic norm $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ (normalized absolute values), $\mu_S=\bigotimes_{v\in S}\mu_v$ the $S$-local multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbb A_{F,S})$, and $\mathcal S(\mathbb A_{F,S})$ the Schwartz–Bruhat space of $\mathbb A_{F,S}$. Let $\nu_S=\bigotimes_{v\in S}\nu_v$ be the $S$-local additive Tamagawa measure on $\mathbb A_{F,S}$ and $\psi_{S,\mathrm{std}}=\bigotimes_{v\in S}\psi_v$ the standard additive character of $\mathbb A_{F,S}$.
--
--   The file defines the following.
--
--   1. **Quasi-characters** (`IsSIdeleQuasiCharacter`). A function $c:\mathrm{GL}_1(\mathbb A_{F,S})\to\mathbb C$ is a quasi-character of the $S$-ideles if it is continuous, multiplicative and nowhere zero, i.e. a continuous homomorphism to $\mathbb C^\times$. The quasi-characters of $J_{F,S}=\mathrm{GL}_1(\mathbb A_{F,S})/\mathcal O_{F,S}^\times$ are those that are trivial on the $S$-units.
--   2. **Twist and dual** (`sQuasiTwist`, `sQuasiDual`). For $s\in\mathbb C$,
--   $$(c\,|\cdot|_{F,S}^s)(g)=c(g)\,|g|_{F,S}^s,\qquad\widehat c(g)=|g|_{F,S}\,c(g)^{-1}.$$
--   3. **$S$-adelic Fourier transform** (`sLocalFourier`). For $\varphi:\mathbb A_{F,S}\to\mathbb C$,
--   $$\widehat\varphi(y)=\int_{\mathbb A_{F,S}}\varphi(x)\,\psi_{S,\mathrm{std}}(xy)\,d\nu_S(x).$$
--   4. **$S$-local zeta integral** (`sZetaIntegralFun`, `sZetaIntegral`). For $\varphi:\mathbb A_{F,S}\to\mathbb C$, in particular for $\varphi=f\in\mathcal S(\mathbb A_{F,S})$,
--   $$Z_S(\varphi,c)=\int_{\mathrm{GL}_1(\mathbb A_{F,S})}\varphi(g)\,c(g)\,d\mu_S(g).$$
--   5. **The factor of the functional equation** (`sLocalRho`). $\rho_S(c)$ is the complex number $r$ such that $Z_S(f,c)=r\,Z_S(\widehat f,\widehat c)$ for every $f\in\mathcal S(\mathbb A_{F,S})$. This is Tate's $\rho$; it is the reciprocal of the local $\gamma$-factor in the convention $Z(\widehat f,\widehat c)=\gamma(c)\,Z(f,c)$.
--   6. **Restriction to $S$** (`sAdeleRestrict`, `sIdeleRestrict`). The coordinate projections $\mathbb A_F\to\mathbb A_{F,S}$ and $\mathrm{GL}_1(\mathbb A_F)\to\mathrm{GL}_1(\mathbb A_{F,S})$, $x\mapsto(x_v)_{v\in S}$.
--
--   These are the objects of Tate's local theory for the finite product $\prod_{v\in S}F_v$: on pure tensors $Z_S$ is the product of the local zeta integrals $Z_v$, and $\rho_S(c)=\prod_{v\in S}\rho_v(c_v)$. The source uses them for the Mellin transform of the $S$-local $\theta$-functions (Chapters 3–5), and relates the global zeta integral to them by Weil's identity.
--
--   **Formalization Note.** A finite set $S\supseteq S_\infty$ of places is represented by the finite set `Sf` of its finite places. All integrals are Bochner integrals, equal to $0$ when the integrand is not integrable; the theorems using these definitions assert integrability where it is needed. `sLocalRho Sf c` is defined by choice and is $0$ if no such $r$ exists; for a quasi-character of exponent in $(0,1)$ the number $r$ exists and is unique. The source defines $\rho_S$ as the product of Tate's explicit local factors; here it is characterized by the functional equation, which determines it for exponents in $(0,1)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 129, Theorem 3.3.1.1, eqs. (3.3.1.1)–(3.3.1.3); p. 128, §3.3.1; p. 119, eq. (3.1.1.4); p. 121, eqs. (3.1.2.7)–(3.1.2.8)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTheta
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Definitions.Def_MasulloGRH_SLocalStandardCharacter

/-!
# `S`-local zeta integrals: quasi-characters of the `S`-ideles, the `S`-adelic Fourier transform,
the zeta integrals `Z_S(f, c)` and the factor `ρ_S(c)` of the `S`-local functional equation

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Chapter 3:
§3.1.1, eq. (3.1.1.4) (p. 119); §3.1.2.3, eqs. (3.1.2.7)–(3.1.2.8) (p. 121); §3.3.1 (p. 128);
Theorem 3.3.1.1, eqs. (3.3.1.1)–(3.3.1.3) (p. 129).

As in `MasulloGRH.SAdeleRing`, a finite set `S` of places of the number field `F` containing all
archimedean places is represented by the finite set `Sf` of its finite places.  The measures are
the `S`-local Tamagawa measures `ν_S` (`MasulloGRH.sAdditiveTamagawa`) and `μ_S`
(`MasulloGRH.sMultiplicativeTamagawa`); the additive character is the standard character
`ψ_{S,std}` (`MasulloGRH.sStdCharacter`).
-/

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory NumberField IsDedekindDomain

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- A quasi-character of the `S`-idele group `GL₁(𝔸_{F,S}) = ∏_{v ∈ S} F_vˣ` (§3.1.1), as a
complex-valued function: a continuous homomorphism `GL₁(𝔸_{F,S}) → ℂˣ`.  The quasi-characters of
`J_{F,S} = GL₁(𝔸_{F,S}) / 𝒪_{F,S}ˣ` (3.1.2.1) are those that are moreover trivial on the
`S`-units. -/
def IsSIdeleQuasiCharacter (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) : Prop :=
  Continuous c ∧ (∀ g h : SIdeleGroup F Sf, c (g * h) = c g * c h) ∧
    ∀ g : SIdeleGroup F Sf, c g ≠ 0

/-- The twist `c |·|_{F,S}^s` of a function `c` on the `S`-ideles by a complex power of the
`S`-idelic norm. -/
def sQuasiTwist (Sf : Finset (HeightOneSpectrum (𝓞 F))) (c : SIdeleGroup F Sf → ℂ) (s : ℂ) :
    SIdeleGroup F Sf → ℂ :=
  fun g => c g * ((sIdeleNorm Sf g : ℝ) : ℂ) ^ s

/-- The dual quasi-character `\hat c = |·|_{F,S} c⁻¹` (3.1.1.4). -/
def sQuasiDual (Sf : Finset (HeightOneSpectrum (𝓞 F))) (c : SIdeleGroup F Sf → ℂ) :
    SIdeleGroup F Sf → ℂ :=
  fun g => ((sIdeleNorm Sf g : ℝ) : ℂ) * (c g)⁻¹

/-- The `S`-adelic Fourier transform `\hat φ(y) = ∫_{𝔸_{F,S}} φ(x) ψ_{S,std}(x y) dν_S(x)` of a
function on the `S`-adeles (§3.3.1), with respect to the standard additive character and the
`S`-local additive Tamagawa measure. -/
def sLocalFourier (Sf : Finset (HeightOneSpectrum (𝓞 F))) (φ : SAdeleRing F Sf → ℂ)
    (y : SAdeleRing F Sf) : ℂ :=
  ∫ x, φ x * sStdCharacter Sf (x * y) ∂(sAdditiveTamagawa F Sf)

/-- The `S`-local zeta integral `Z_S(φ, c) = ∫_{GL₁(𝔸_{F,S})} φ(g) c(g) dμ_S(g)` (3.3.1.1) of a
function `φ` on the `S`-adeles, with respect to the `S`-local multiplicative Tamagawa measure. -/
def sZetaIntegralFun (Sf : Finset (HeightOneSpectrum (𝓞 F))) (φ : SAdeleRing F Sf → ℂ)
    (c : SIdeleGroup F Sf → ℂ) : ℂ :=
  ∫ g : SIdeleGroup F Sf, φ (g : SAdeleRing F Sf) * c g ∂(sMultiplicativeTamagawa F Sf)

/-- The `S`-local zeta integral `Z_S(f, c)` of `f ∈ S(𝔸_{F,S})` (3.3.1.1). -/
def sZetaIntegral {Sf : Finset (HeightOneSpectrum (𝓞 F))} (f : SAdelicSchwartz F Sf)
    (c : SIdeleGroup F Sf → ℂ) : ℂ :=
  sZetaIntegralFun Sf f.eval c

open Classical in
/-- The factor `ρ_S(c)` of the `S`-local functional equation (3.3.1.2)–(3.3.1.3): the complex
number `r` with `Z_S(f, c) = r · Z_S(\hat f, \hat c)` for all `f ∈ S(𝔸_{F,S})`.  For a
quasi-character `c` of exponent in `(0, 1)` such an `r` exists and is unique; if no such `r`
exists the value is `0`.  This is Tate's `ρ`; it is the reciprocal of the local `γ`-factor in the
convention `Z(\hat f, \hat c) = γ(c) · Z(f, c)`. -/
def sLocalRho (Sf : Finset (HeightOneSpectrum (𝓞 F))) (c : SIdeleGroup F Sf → ℂ) : ℂ :=
  if h : ∃ r : ℂ, ∀ f : SAdelicSchwartz F Sf,
      sZetaIntegral f c = r * sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf c) then
    h.choose
  else 0

/-- The projection `𝔸_F → 𝔸_{F,S}` of the adele ring onto its coordinates at the places of `S`. -/
def sAdeleRestrict (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    AdeleRing (𝓞 F) F →+* SAdeleRing F Sf :=
  RingHom.prod (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    ((RingHom.pi fun v : Sf =>
        RestrictedProduct.evalRingHom
          (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (v : HeightOneSpectrum (𝓞 F))).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

@[simp] theorem sAdeleRestrict_apply (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (x : AdeleRing (𝓞 F) F) :
    sAdeleRestrict Sf x = (x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) := rfl

/-- The projection `GL₁(𝔸_F) → GL₁(𝔸_{F,S})` of the idele group onto its coordinates at the
places of `S`.  Restricted to the ideles with unit coordinates outside `S`
(`MasulloGRH.sIntegralIdeles`) it is surjective, with section the insertion `j_{F,S}` of
(3.1.2.7)–(3.1.2.8). -/
def sIdeleRestrict (Sf : Finset (HeightOneSpectrum (𝓞 F))) : IdeleGroup F →* SIdeleGroup F Sf :=
  Units.map (sAdeleRestrict Sf).toMonoidHom

end

end MasulloGRH


