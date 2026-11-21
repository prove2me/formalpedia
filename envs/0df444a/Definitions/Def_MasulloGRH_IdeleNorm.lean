-- Prove2me | Definitions.Def_MasulloGRH_IdeleNorm
-- name    : MasulloGRH_IdeleNorm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:17:24.592339+00:00
-- url     : https://prove2.me/theorems/2bb07043-bcde-4ba2-8ed1-e96cc581db4f
-- title:
--   Idelic norm, characters trivial on $C_F^1$, partial Hecke $L$-functions, upper density
-- statement:
--   This file adds the idelic norm and the objects defined from it.
--
--   Let $F$ be a number field, $\mathrm{GL}_1(\mathbb A_F)$ its idele group and $\chi$ a Hecke character.
--
--   1. The **idelic norm** of an idele $g=(g_v)_v$ is
--   $$|g|_F=\prod_{v}|g_v|_v ,$$
--   the product over all places of the normalized absolute values: the usual absolute value at a real place, its square at a complex place, and at a finite place $v$ the absolute value with $|\pi_v|_v=N(\mathfrak p_v)^{-1}$. All but finitely many factors are $1$.
--   2. $\chi$ is **trivial on $C_F^1$** if $\chi(g)=1$ for every idele $g$ with $|g|_F=1$.
--   3. $\chi=|\cdot|_F^{-it_0}$, for a real number $t_0$, means $\chi(g)=|g|_F^{-it_0}$ for every idele $g$.
--   4. $N(\mathfrak p_v)=q_v$ is the absolute norm of the prime ideal of a finite place $v$.
--   5. The **reciprocal local Euler factor** at a finite place $v$ is
--   $$L_v(\chi_v|\cdot|_v^s)^{-1}=1-\chi(\mathfrak p_v)\,N(\mathfrak p_v)^{-s},$$
--   which is $1$ if $\chi$ is ramified at $v$.
--   6. For a finite set $S$ of places containing the Archimedean places, with finite part $S_f$, the **partial Hecke $L$-function** is
--   $$L_{\Sigma_F-S}(s,\chi)=L_f(s,\chi)\prod_{v\in S_f}L_v(\chi_v|\cdot|_v^s)^{-1},$$
--   the finite Hecke $L$-function with the Euler factors at $S_f$ removed.
--   7. The **upper density** of a set $X\subset\mathbb R$ is
--   $$\limsup_{T\to+\infty}\frac{\lambda([-T,T]\cap X)}{2T},$$
--   with $\lambda$ the Lebesgue measure.
--
--   A character is trivial on $C_F^1$ exactly when it is of the form $|\cdot|_F^{-it_0}$; in that case $L_f(s,\chi)$ has a pole at $s=1+it_0$. The partial $L$-functions are the multipliers that relate statements for a finite set of places to global statements.
--
--   **Formalization Note** A set $S$ of places containing all Archimedean places is represented by the finite set $S_f$ of its finite places. In item 7 the outer Lebesgue measure is used, so $X$ need not be measurable.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Notation and terminology (p. 7); Proposition 3.2.1.3(2) (p. 123); §1.4.7 (p. 30); Definition B.5.3.1(1) (p. 632)

import Definitions.Def_MasulloGRH_HeckeLFunction

/-!
# The idelic norm, characters trivial on `C_F^1`, partial Hecke L-functions, upper density

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026),
"Notation and terminology" (p. 7), Proposition 3.2.1.3(2) (p. 123), §1.4.7 (p. 30),
Definition B.5.3.1(1) (p. 632).
-/

namespace MasulloGRH

open NumberField IsDedekindDomain

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The idelic norm `|g|_F = ∏_v |g_v|_v`, the product over all places of `F` of the normalized
absolute values: at an infinite place the usual absolute value, squared at a complex place; at a
finite place `v` the absolute value with `|π_v|_v = N(𝔭_v)⁻¹`. -/
def ideleNorm (g : IdeleGroup F) : ℝ :=
  (∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(g : AdeleRing (𝓞 F) F).2 v‖

/-- `χ|_{C_F^1} = 1`: the Hecke character `χ` is trivial on the classes of the ideles of
idelic norm `1`. -/
def HeckeCharacter.IsTrivialOnNormOne (χ : HeckeCharacter F) : Prop :=
  ∀ g : IdeleGroup F, ideleNorm g = 1 → χ (QuotientGroup.mk g) = 1

/-- `χ = |·|_F^{-i t₀}`: for every idele `g`, `χ(g) = |g|_F^{-i t₀}`. -/
def HeckeCharacter.IsNormPower (χ : HeckeCharacter F) (t₀ : ℝ) : Prop :=
  ∀ g : IdeleGroup F,
    ((χ (QuotientGroup.mk g) : Circle) : ℂ) = ((ideleNorm g : ℝ) : ℂ) ^ (-(t₀ * Complex.I))

/-- The norm `N(𝔭_v) = q_v` of the prime ideal of a finite place, as a complex number. -/
def primeNorm (v : HeightOneSpectrum (𝓞 F)) : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

/-- The reciprocal `L_v(χ_v|·|_v^s)⁻¹ = 1 - χ(𝔭_v) N(𝔭_v)^{-s}` of the local Euler factor of
`χ` at the finite place `v` (equal to `1` if `χ` is ramified at `v`). -/
def eulerFactorInv (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  1 - χ.primeValue v * primeNorm v ^ (-s)

/-- The partial Hecke L-function `L_{Σ_F - S}(s, χ) = L_f(s, χ) · ∏_{v ∈ S_f} L_v(χ_v|·|_v^s)⁻¹`,
with the Euler factors at the finite places in `S` removed.  A finite set `S` of places containing
all Archimedean places is represented by the finite set `Sf` of its finite places. -/
def partialHeckeLFunction (χ : HeckeCharacter F) (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (s : ℂ) : ℂ :=
  heckeLFunction χ s * ∏ v ∈ Sf, eulerFactorInv χ v s

/-- The upper density `limsup_{T → +∞} λ([-T, T] ∩ X) / (2T)` of a subset `X` of `ℝ`
(Definition B.5.3.1(1)), with `λ` the Lebesgue measure. -/
def upperDensity (X : Set ℝ) : ℝ :=
  Filter.limsup
    (fun T : ℝ => (MeasureTheory.volume (Set.Icc (-T) T ∩ X)).toReal / (2 * T)) Filter.atTop

end

end MasulloGRH


