-- Prove2me | Definitions.Def_SamplingAC0_Supplement_cellLaw
-- name    : SamplingAC0_Supplement_cellLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:38:17.718806+00:00
-- url     : https://prove2.me/theorems/67b6d5d0-3f32-4ae9-976b-2b5c94e7ec0e
-- title:
--   Output distribution $f(U)$ on a uniform input from a finite domain
-- statement:
--   Let $\sigma$ be a finite nonempty set and $f:\sigma\to B$ a map. The **output distribution** $f(U)$ is the law of $f(u)$ when $u$ is uniform on $\sigma$:
--   $$\Pr[f(U)=b]=\frac{|\{u\in\sigma : f(u)=b\}|}{|\sigma|}.$$
--
--   In Theorem 6, $\sigma=[n]^s$ is the set of inputs of $s$ cells with values in $[n]$, and $f(U)$ is the distribution sampled by a cell-probe sampler $f:[n]^s\to\{0,1\}^n$.
--
--   **Formalization Note** The base mission's output distribution covers only bit inputs $\{0,1\}^\iota$; this is the same construction for an arbitrary finite input domain.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Notation p.2; Theorem 6 p.4

import Mathlib
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- **Output distribution on a uniform input over an arbitrary finite domain.** Riazanov–Viola,
*Sampling Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…),
Notation, p.2 ("U for the uniform distribution (over suitable domain)"), and p.4 (Theorem 6: the
input of `f : [n]^s → {0,1}^n` is a uniform element of `[n]^s`).

`cellLaw f` is the distribution `f(U)` of `f` applied to a uniform element `U` of the finite
nonempty set `σ`. Theorem 6 uses `σ = Fin s → Fin n`, the `s` input cells with values in `[n]`.

**Formalization Note.** The base mission's `SamplingAC0.law` covers only bit inputs `ι → Bool`;
this is the same pushforward for a general finite input domain. -/
noncomputable def cellLaw {σ β : Type} [Fintype σ] [Nonempty σ] (f : σ → β) : PMF β :=
  (PMF.uniformOfFintype σ).map f

end SamplingAC0.Supplement


