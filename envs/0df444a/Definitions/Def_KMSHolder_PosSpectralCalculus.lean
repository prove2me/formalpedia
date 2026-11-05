-- Prove2me | Definitions.Def_KMSHolder_PosSpectralCalculus
-- name    : KMSHolder_PosSpectralCalculus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:19.461066+00:00
-- url     : https://prove2.me/theorems/536976d2-34ed-4731-afec-b748e40272a6
-- title:
--   Positive self-adjoint operator, given by its functional calculus
-- statement:
--   A **positive self-adjoint operator** $T$ on $H$, possibly unbounded and possibly with a nontrivial kernel, is encoded by its bounded continuous functional calculus $f \mapsto f(T)$: a nondegenerate $*$-homomorphism from the bounded continuous functions on $\mathbb R$ into $B(H)$ whose spectral support lies in $[0, \infty)$, that is, $f(T) = 0$ whenever $f$ vanishes on $[0,\infty)$.
--
--   It is used for the relative modular operators $\Delta_{\phi,\Omega}$ of positive normal functionals $\phi$. Unlike the modular operator, $\Delta_{\phi,\Omega}$ has a kernel when $\phi$ is not faithful, so it is described through $T$ itself rather than through $\log T$.
--
--   **Formalization Note** The calculus is the published `OAI.BoundedRecovery.RealSpectralCalculus`, with the support condition `HasSpectralSupport (Set.Ici 0)` imposed on every vector.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §3.1, p.4 (Δ_{φ,Ω} is a positive, in general unbounded, operator)

import Mathlib
import Definitions.Def_BoundedRecovery

open OAI.BoundedRecovery

namespace KMSHolder

/-- A positive self-adjoint operator `T` (possibly unbounded, possibly with a kernel), encoded by
its bounded continuous functional calculus `f ↦ f(T)`: a nondegenerate spectral calculus
(`OAI.BoundedRecovery.RealSpectralCalculus`) whose spectrum lies in `[0, ∞)`, i.e. `f(T) = 0`
whenever `f` vanishes on `[0, ∞)`.

Used for the relative modular operators `Δ_{φ,Ω}` of Jäkel–Robl, arXiv:1103.3608v2, §3.1, p.4
("`Δ_{φ,Ω} = S*_{φ,Ω} \overline{S_{φ,Ω}}` is a positive, in general unbounded, operator on the
original Hilbert space"). Unlike the modular operator, `Δ_{φ,Ω}` has a kernel when `φ` is not
faithful, so it is encoded through `T` itself rather than through `log T`. -/
structure PosSpectralCalculus (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The calculus `f ↦ f(T)`. -/
  toCalc : RealSpectralCalculus H
  /-- The spectrum of `T` lies in `[0, ∞)`. -/
  spectrum_nonneg : ∀ h : H, toCalc.HasSpectralSupport (Set.Ici 0) h

end KMSHolder


