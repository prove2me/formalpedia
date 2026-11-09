-- Prove2me | Definitions.Def_ModLatSVP_IsStar
-- name    : ModLatSVP_IsStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:28.839734+00:00
-- url     : https://prove2.me/theorems/31369e4e-ecb2-484a-ba64-3d09c61a7fd6
-- title:
--   The involution $\star$ of a totally real or CM field, and the root discriminant $\mathrm{rd}(K)$
-- statement:
--   Let $K$ be a number field of degree $d=[K:\mathbb Q]$. An automorphism $\tau$ of $K$ is an **involution $\star$** of $K$ if
--
--   $$\sigma(\tau x)=\overline{\sigma(x)}\qquad\text{for every embedding }\sigma:K\to\mathbb C\text{ and every }x\in K .$$
--
--   For a totally real field this is the identity, for a CM field it is complex conjugation; we write $x^\star=\tau x$.
--
--   The **root discriminant** of $K$ is $\mathrm{rd}(K)=|\Delta_K|^{1/d}$, where $\Delta_K$ is the field discriminant, the determinant of the trace form $(x,y)\mapsto \mathrm{Tr}_{K/\mathbb Q}(xy)$ on an integral basis of $\mathcal O_K$. It is written $\rho$ throughout the paper.
--
--   Both objects appear in every statement of the mission: $\star$ makes multiplication by $\alpha^\star$ the adjoint of multiplication by $\alpha$, and $\rho$ controls the geometry of rank-one modules.
--
--   **Formalization Note** The involution is given by its defining property rather than by Mathlib's $\texttt{IsCMField.complexConj}$, so that the totally real case is covered too. $\Delta_K$ is Mathlib's $\texttt{NumberField.discr}$.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2.2, p.12 (PDF p.12); §1.1, p.2 and §2, p.11 (root discriminant)

import Mathlib

open NumberField

namespace ModLatSVP

/-- The involution `⋆` of a totally real or CM field. Kim, Lee, Son, *Exact SVP and CVP in Structured
Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…), §2.2, p.12 (PDF p.12): "there is an automorphism ⋆ satisfying σ(α⋆) = conj(σ(α)) for every
α ∈ K and every embedding σ. It is the identity for totally real fields and complex conjugation for CM
fields."

`IsStar K τ` says that the field automorphism `τ` is such an involution: `σ (τ x) = conj (σ x)` for
every embedding `σ : K →+* ℂ` and every `x ∈ K`.

**Formalization Note.** The involution is characterized by its defining property, not by
`IsCMField.complexConj`, so that the totally real case (`τ = id`) is covered by the same predicate. -/
def IsStar (K : Type*) [Field K] [CharZero K] (τ : K ≃ₐ[ℚ] K) : Prop :=
  ∀ (σ : K →+* ℂ) (x : K), σ (τ x) = (starRingEnd ℂ) (σ x)

/-- The root discriminant `rd(K) = |∆_K|^{1/[K:ℚ]}` (p.2 and §2, p.11: "ρ = rd(K) = |∆_K|^{1/d} the
root discriminant of K, where ∆_K is the field discriminant").

**Formalization Note.** `∆_K` is Mathlib's `NumberField.discr K`, the determinant of the trace form on an
integral basis of `𝓞 K` (§2.2, p.12); `|∆_K| ≥ 1`, so the real power is that of a positive number. -/
noncomputable def rd (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(discr K : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ K)

end ModLatSVP


