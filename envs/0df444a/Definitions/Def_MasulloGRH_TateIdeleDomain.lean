-- Prove2me | Definitions.Def_MasulloGRH_TateIdeleDomain
-- name    : MasulloGRH_TateIdeleDomain
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T09:22:25.231221+00:00
-- url     : https://prove2.me/theorems/b184344f-aeb9-41de-826f-3966d3ebbfd8
-- title:
--   Definition A.2.3.6 — Tate's idelic fundamental domain $E_F^1=\bigcup_i g_i(E_0\times\widehat{\mathcal O}_F^\times)$, and the ideal class of an idele
-- statement:
--   **Tate's idelic fundamental domain $E_F^1$** (Definition A.2.3.6, eq. (A.2.3.14) of the source, with the ideal class map of (A.2.3.12)).
--
--   Let $F$ be a number field with ring of integers $\mathcal O_F$, class number $h_F$, adele ring $\mathbb A_F$ and idele group $\mathbb I_F=\mathrm{GL}_1(\mathbb A_F)$. For an idele $g=(g_v)_v$ and a finite place $\mathfrak p$ let $\operatorname{ord}_{\mathfrak p}(g_{\mathfrak p})\in\mathbb Z$ be the normalized valuation of its component at $\mathfrak p$; it vanishes for almost all $\mathfrak p$. The file defines three objects.
--
--   1. `ideleIdealClass`: the natural map $\mathbb I_F\to\mathrm{Pic}(\mathcal O_F)$ to the ideal class group,
--   $$g\longmapsto\Big[\prod_{\mathfrak p}\mathfrak p^{\operatorname{ord}_{\mathfrak p}(g_{\mathfrak p})}\Big],$$
--   the class of the fractional ideal attached to $g$.
--   2. `tateUnitIdeleDomain`: the set
--   $$E_0\times\widehat{\mathcal O}_F^\times=\{e\in\mathbb I_F:\ e_\infty\in E_0,\ e_v\in\mathcal O_{F_v}^\times\ \text{for every finite place }v\},$$
--   where $e_\infty=(e_v)_{v\mid\infty}$ is the archimedean part of $e$, $\widehat{\mathcal O}_F^\times=\prod_{v\nmid\infty}\mathcal O_{F_v}^\times$, and $E_0\subset\mathbb I_\infty^1$ is Tate's archimedean domain (`MasulloGRH.tateArchimedeanDomain`, depending on a $\mathbb Z$-basis of $\mathcal O_F^\times/\mu_F$, an archimedean place $v_0$ and an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ or $\mathbb C$).
--   3. `tateIdeleDomain`: for ideles $g_1,\dots,g_{h_F}$,
--   $$E_F^1=\bigcup_{i=1}^{h_F}g_i\,\big(E_0\times\widehat{\mathcal O}_F^\times\big)\subset\mathbb I_F .$$
--
--   In the source the ideles $g_1=1,g_2,\dots,g_{h_F}$ are chosen in the group $\mathbb I_F^1$ of ideles of idelic norm one so that their ideal classes are the $h_F$ distinct elements of $\mathrm{Pic}(\mathcal O_F)$ ((A.2.3.12)); then $E_F^1\subset\mathbb I_F^1$, and $E_F^1$ is a relatively compact fundamental domain for the action of $F^\times$ on $\mathbb I_F^1$ (Proposition A.2.3.10). By Remark A.2.3.7 of the source, $E_F^1$ is the fundamental domain of Tate's thesis ([CF, Ch. XV, Def. 4.3.2]). It is used throughout the paper to unfold integrals over the idele class group $C_F=\mathbb I_F/F^\times$ and to compute the volume of $C_F^1$.
--
--   **Formalization Note.** $\mathbb I_F$ is the platform's `MasulloGRH.IdeleGroup F = (AdeleRing (𝓞 F) F)ˣ`. The ideal class group is Mathlib's `ClassGroup (𝓞 F)` (canonically isomorphic to $\mathrm{Pic}(\mathcal O_F)$ via `ClassGroup.equivPic`), and `ideleIdealClass g` is the finite product `∏ᶠ v, ClassGroup.mk0 𝔭_v ^ (-log (Valued.v g_v))`, with Mathlib's convention $\mathrm{Valued.v}(x)=\exp(-\operatorname{ord}_v(x))$. The representatives are given by an arbitrary map `r : ClassGroup (𝓞 F) → IdeleGroup F` ($g_c=r(c)$, indexed by the ideal classes instead of $1,\dots,h_F$); the conditions of the source — `r 1 = 1`, `ideleNorm (r c) = 1` and `ideleIdealClass F (r c) = c` for all `c` — are hypotheses of the theorems about $E_F^1$, not part of the definition. `tateIdeleDomain` is a subset of the whole idele group; that it lies in the norm-one ideles is part of the first of those theorems. The local unit condition is `Valued.v (e_v) = 1`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 549, §A.2.3.2, eq. (A.2.3.12) and Definition A.2.3.6, eq. (A.2.3.14); classical reference (cited in Remark A.2.3.7, p. 549): J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, Def. 4.3.2

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm
import Definitions.Def_MasulloGRH_TateArchimedeanDomain

/-!
# Tate's idelic fundamental domain `E_F¹` for `Fˣ` acting on the norm-one ideles

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix A, §A.2.3,
eq. (A.2.3.12) and Definition A.2.3.6, eq. (A.2.3.14) (p. 549).  The paper identifies the
construction with [CF, Ch. XV, Def. 4.3.2] (Remark A.2.3.7).
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace MasulloGRH

open NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The natural map `GL₁(𝔸_F) → Pic(𝒪_F)` of (A.2.3.12), with values in Mathlib's ideal class
group `ClassGroup (𝓞 F)`: the class `∏_𝔭 [𝔭]^{ord_𝔭(g_𝔭)}` of the fractional ideal attached to
the idele `g`, where `ord_𝔭(x) = -log (Valued.v x)` is the normalized additive valuation (a finite
product, because `g_𝔭` is a unit at almost all finite places `𝔭`). -/
def ideleIdealClass (g : IdeleGroup F) : ClassGroup (𝓞 F) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ ^
      (-WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v)))

/-- The set `E₀ × 𝒪̂_Fˣ` of (A.2.3.14): the ideles whose archimedean component lies in Tate's
archimedean domain `E₀` (a subset of the norm-one archimedean ideles) and whose component at every
finite place is a local unit. -/
def tateUnitIdeleDomain
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) : Set (IdeleGroup F) :=
  {e | (∃ a ∈ tateArchimedeanDomain F b v₀ σ,
          (e : AdeleRing (𝓞 F) F).1 = ((a : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) ∧
       ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((e : AdeleRing (𝓞 F) F).2 v) = 1}

/-- **Tate's idelic fundamental domain** `E_F¹ = ⋃ᵢ gᵢ (E₀ × 𝒪̂_Fˣ)` (Definition A.2.3.6,
eq. (A.2.3.14)), as a subset of the idele group.  The ideles `g₁, …, g_{h_F}` are given by the map
`r : ClassGroup (𝓞 F) → GL₁(𝔸_F)`, indexed by the ideal classes.  The definition is the one of the
paper when `r` takes values in the norm-one ideles, `r c` has ideal class `c` for every `c`, and
`r 1 = 1`; these are hypotheses of the theorems about `E_F¹`, not part of the definition. -/
def tateIdeleDomain
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (r : ClassGroup (𝓞 F) → IdeleGroup F) :
    Set (IdeleGroup F) :=
  {g | ∃ c : ClassGroup (𝓞 F), ∃ e ∈ tateUnitIdeleDomain F b v₀ σ, g = r c * e}

end

end MasulloGRH


