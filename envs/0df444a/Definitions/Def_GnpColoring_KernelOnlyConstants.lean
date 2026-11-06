-- Prove2me | Definitions.Def_GnpColoring_KernelOnlyConstants
-- name    : GnpColoring_KernelOnlyConstants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:39.859863+00:00
-- url     : https://prove2.me/theorems/831a5e54-23de-4131-b53d-9ea56bc606f6
-- title:
--   The kernel of a generator consists of constants
-- statement:
--   A generator $\mathcal L$ on $L^2(\mu)$ has **only constants in its kernel** if $\mathcal Lf=0$ on the support of $\mu$ implies that $f$ is constant on the support of $\mu$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Lemma 3.4, p.16; Lemma 5.9, p.54

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The kernel of a generator consists only of constants** (in `L²(µ)`): if `𝓛 f = 0` on the
support of `µ`, then `f` is constant on the support of `µ`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Lemma 3.4, p.16 ("the kernel of L consists only of constants") and Lemma 5.9, p.54 ("both
generators have only constants in their kernel").

**Formalization Note** `L²(µ)` is the functions on the support of `µ` (Section 2.2, p.13). -/
def KernelOnlyConstants {n q : ℕ} (μ : (Fin n → Fin q) → ℝ)
    (𝓛 : ((Fin n → Fin q) → ℝ) → ((Fin n → Fin q) → ℝ)) : Prop :=
  ∀ f : (Fin n → Fin q) → ℝ, (∀ x, 0 < μ x → 𝓛 f x = 0) →
    ∃ c : ℝ, ∀ x, 0 < μ x → f x = c

end GnpColoring


