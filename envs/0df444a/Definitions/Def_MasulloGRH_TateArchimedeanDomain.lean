-- Prove2me | Definitions.Def_MasulloGRH_TateArchimedeanDomain
-- name    : MasulloGRH_TateArchimedeanDomain
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T09:20:44.449814+00:00
-- url     : https://prove2.me/theorems/d45748b3-45f9-4e96-ae54-01f93dc48097
-- title:
--   Definition A.2.3.6 (archimedean part) — Tate's fundamental domain $E_0$ for $\mathcal O_F^\times$ acting on the norm-one archimedean ideles
-- statement:
--   **Tate's archimedean fundamental domain $E_0$** (Definition A.2.3.6, eq. (A.2.3.13) of the source).
--
--   Let $F$ be a number field with $r_1$ real and $r_2$ complex places, $S_\infty$ its set of archimedean places, $\mu_F\subset\mathcal O_F^\times$ the group of roots of unity of $F$ and $w_F=|\mu_F|$. Write
--   $$\mathbb I_\infty=\mathrm{GL}_1(\mathbb A_{F,S_\infty})=\prod_{v\in S_\infty}F_v^\times,\qquad |g|_\infty=\prod_{v\in S_\infty}|g_v|_v,\qquad \mathbb I_\infty^1=\{g\in\mathbb I_\infty:\ |g|_\infty=1\},$$
--   where $|\cdot|_v$ is the normalized absolute value (the usual absolute value at a real place, its square at a complex place). The logarithm map is
--   $$\mathscr L\colon\mathbb I_\infty\to\mathbb R^{S_\infty},\qquad\mathscr L(g)=(\log|g_v|_v)_{v\in S_\infty};$$
--   it maps $\mathbb I_\infty^1$ into the hyperplane $H_{\log}=\{x\in\mathbb R^{S_\infty}:\ \sum_vx_v=0\}$, and by Dirichlet's unit theorem $\mathscr L(\mathcal O_F^\times)$ is a lattice in $H_{\log}$ with $\ker(\mathscr L|_{\mathcal O_F^\times})=\mu_F$.
--
--   The construction depends on three choices:
--
--   - units $\varepsilon_1,\dots,\varepsilon_r$, $r=r_1+r_2-1$, whose classes form a $\mathbb Z$-basis of the free abelian group $\mathcal O_F^\times/\mu_F$;
--   - an archimedean place $v_0$ of $F$;
--   - an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ (if $v_0$ is real) or with $\mathbb C$ (if $v_0$ is complex; there are two such identifications, differing by complex conjugation).
--
--   The file defines three objects.
--
--   1. `unitsToInfiniteIdeles`: the diagonal embedding $\mathcal O_F^\times\to\mathbb I_\infty$, $u\mapsto(u)_{v\in S_\infty}$.
--   2. `logParallelotopePreimage`: the subset $\mathscr L^{-1}(P)$ of $\mathbb I_\infty^1$, where
--   $$P=\Big\{\sum_{i=1}^{r}x_i\,\mathscr L(\varepsilon_i):\ 0\le x_i<1\Big\}\subset H_{\log}$$
--   is the half-open parallelotope spanned by the logarithms of the chosen units ((A.2.3.9)–(A.2.3.10)).
--   3. `tateArchimedeanDomain`: Tate's archimedean domain
--   $$E_0=\big\{g\in\mathscr L^{-1}(P):\ \arg\big(\iota_{v_0}(g_{v_0})\big)\in[0,2\pi/w_F)\big\}\subset\mathbb I_\infty^1 .$$
--   If $v_0$ is real (then $w_F=2$), the angular condition says that $\iota_{v_0}(g_{v_0})$ is positive; if $v_0$ is complex, it says that $\iota_{v_0}(g_{v_0})$ lies in the half-open sector $\mathbb R_{>0}\,e^{i[0,2\pi/w_F)}$.
--
--   $E_0$ is the archimedean building block of the fundamental domain $E_F^1=\bigcup_ig_i(E_0\times\widehat{\mathcal O}_F^\times)$ of Tate's thesis for the action of $F^\times$ on the norm-one ideles: the parallelotope takes care of the units modulo torsion and the sector of the roots of unity, so that $E_0$ is a strict fundamental domain for $\mathcal O_F^\times$ acting on $\mathbb I_\infty^1$ (Lemma A.2.3.8). The paper uses $E_0$ and $E_F^1$ throughout Chapter 2 and Appendix A (Haar measure computations, theta functions on the idele class group).
--
--   **Formalization Note.** $\mathbb I_\infty$ is `(InfiniteAdeleRing F)ˣ` and $\mathbb I_\infty^1$ is the kernel of the platform homomorphism `RiemannMasullo.infiniteIdeleNorm : (InfiniteAdeleRing F)ˣ →* ℝ≥0ˣ`; `logParallelotopePreimage` and `tateArchimedeanDomain` are sets in this subgroup. The basis is `b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F))`. The parallelotope is the platform's `RiemannMasullo.regulatorParallelotope F b`, which lives in Mathlib's `logSpace F = ({w // w ≠ w₀} → ℝ)`, i.e. $\mathbb R^{S_\infty}$ with the coordinate at Mathlib's distinguished place $w_0$ removed. Because $\mathscr L(\mathbb I_\infty^1)\subset H_{\log}$ and the projection $H_{\log}\to\mathbb R^{S_\infty\setminus\{w_0\}}$ is a linear isomorphism carrying $P$ to `regulatorParallelotope F b`, the condition $\mathscr L(g)\in P$ for $g\in\mathbb I_\infty^1$ is expressed through the coordinates $w\ne w_0$ of `RiemannMasullo.infiniteIdeleLog` ($=\,$`mult w * log ‖g_w‖`). The identification is $\iota_{v_0}=\sigma\circ{}$`extensionEmbedding v₀` with $\sigma\in\mathrm{Aut}_{\mathbb R}(\mathbb C)=\{\mathrm{id},\text{conj}\}$, and the angular condition is the platform predicate `RiemannMasullo.inTorsionSector` (with `Complex.arg ∈ (-π, π]` and $w_F=$ `Units.torsionOrder F`). Hypotheses on the data are not needed: every basis, place and $\sigma$ gives a valid $E_0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 548–549, §A.2.3.2, eqs. (A.2.3.7)–(A.2.3.10) and Definition A.2.3.6, eq. (A.2.3.13); classical reference (cited in Remark A.2.3.7, p. 549): J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, Def. 4.3.2

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
import Definitions.Def_RiemannMasullo_RegulatorParallelotope
import Definitions.Def_RiemannMasullo_TorsionSector

/-!
# Tate's archimedean fundamental domain `E₀` for the units of a number field

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix A, §A.2.3,
Definition A.2.3.6, eq. (A.2.3.13) (p. 549); the data are fixed in (A.2.3.7)–(A.2.3.10)
(pp. 548–549).  The paper identifies the construction with [CF, Ch. XV, Def. 4.3.2]
(Remark A.2.3.7).

Notation of the paper: `𝕀_∞ = GL₁(𝔸_{F,S_∞}) = ∏_{v ∣ ∞} F_vˣ` is the group of archimedean ideles,
`|g|_∞ = ∏_{v ∣ ∞} |g_v|_v` (normalized absolute values) and `𝕀_∞¹ = ker |·|_∞`.
-/

set_option autoImplicit false
-- needed to find the `ℤ`-module structure on `Additive ((𝓞 F)ˣ ⧸ Units.torsion F)`
set_option maxSynthPendingDepth 8

namespace MasulloGRH

open NumberField

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The diagonal embedding `𝒪_Fˣ → 𝕀_∞ = ∏_{v ∣ ∞} F_vˣ` of the global units into the archimedean
ideles. -/
def unitsToInfiniteIdeles : (𝓞 F)ˣ →* (InfiniteAdeleRing F)ˣ :=
  Units.map ((algebraMap F (InfiniteAdeleRing F)).comp (algebraMap (𝓞 F) F)).toMonoidHom

/-- The preimage `ℒ⁻¹(P)` of the regulator parallelotope under the logarithm map, as a subset of
the norm-one archimedean ideles `𝕀_∞¹`.  Here `ℒ(g) = (log |g_v|_v)_{v ∣ ∞}` and
`P = {∑ᵢ xᵢ ℒ(εᵢ) : 0 ≤ xᵢ < 1}` for the basis `b = (ε₁, …, ε_r)` of `𝒪_Fˣ / μ_F`.  Since `ℒ`
maps `𝕀_∞¹` into the hyperplane `H_log = {∑_v x_v = 0}`, on which dropping the coordinate at
Mathlib's distinguished place `w₀` is injective, the condition `ℒ(g) ∈ P` is expressed in
Mathlib's `logSpace F = ({w // w ≠ w₀} → ℝ)`. -/
def logParallelotopePreimage
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F))) :
    Set (MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F)) :=
  {g | (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦
          RiemannMasullo.infiniteIdeleLog F g.val w.val) ∈
        RiemannMasullo.regulatorParallelotope F b}

/-- **Tate's archimedean fundamental domain** `E₀` (Definition A.2.3.6, eq. (A.2.3.13)):
`E₀ = {g ∈ ℒ⁻¹(P) : arg(ι_{v₀}(g_{v₀})) ∈ [0, 2π / w_F)}`, a subset of the norm-one archimedean
ideles `𝕀_∞¹`.  The data are a `ℤ`-basis `b` of `𝒪_Fˣ / μ_F`, an archimedean place `v₀`, and
`σ ∈ Aut_ℝ(ℂ) = {id, conj}`, which selects the identification `ι_{v₀} = σ ∘ extensionEmbedding v₀`
of `F_{v₀}` with a subfield of `ℂ` (for real `v₀` the condition says `g_{v₀} > 0`, for either
`σ`). -/
def tateArchimedeanDomain
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) :
    Set (MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F)) :=
  {g | g ∈ logParallelotopePreimage F b ∧
       RiemannMasullo.inTorsionSector F v₀ σ
         (Units.map (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v₀).toMonoidHom
           g.val)}

end

end MasulloGRH


