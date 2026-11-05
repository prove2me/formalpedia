-- Prove2me | Definitions.Def_BundleGerbeStable_IsExpBoundary
-- name    : BundleGerbeStable_IsExpBoundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:39.21092+00:00
-- url     : https://prove2.me/theorems/fd325b17-b49c-4c19-a99f-a08cfe2e0034
-- title:
--   The relation behind $H^2(M,\mathbb C^\times)\simeq H^3(M,\mathbb Z)$
-- statement:
--   `IsExpBoundary a c` holds for $a\in H^2(M,\mathbb C^\times)$ and $c\in H^3(M,\mathbb Z)$ when on some open cover there are a $\mathbb C^\times$-valued 2-cocycle $g$ representing $a$, a smooth $\mathbb C$-valued 2-cochain $f$ with
--   $$\exp(2\pi i f)=g,$$
--   and a locally constant $\mathbb Z$-valued 3-cocycle $n$ representing $c$ with $n=\delta f$ as $\mathbb C$-valued cochains.
--
--   This is the connecting map of the exponential sequence $0\to\mathbb Z\to\mathbb C\to\mathbb C^\times\to 0$, which the paper uses without further comment to pass from $H^2(M,\mathbb C^\times)$ to $H^3(M,\mathbb Z)$.
--
--   **Formalization Note.** The paper fixes no sign. The sign here is $n=+\delta f$; it changes neither the bijection of Theorem 3.3 nor Theorems 2.1 and 2.2.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3

import Mathlib
import Definitions.Def_BundleGerbeStable_Coefficients

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M] [DiffeologicalSpace M]

/-- The relation behind the isomorphism `H²(M, ℂ×) ≃ H³(M, ℤ)` (Murray, Stevenson, *Bundle gerbes:
stable isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3): on some cover there are a
ℂˣ-valued 2-cocycle `g` representing `a`, a smooth `ℂ`-valued 2-cochain `f` with `exp(2πi f) = g`, and a
locally constant `ℤ`-valued 3-cocycle `n` representing `c` with `n = δf` as `ℂ`-valued cochains.

**Formalization Note.** The paper fixes no sign for the isomorphism; this one is `n = +δf`. The sign
changes neither the bijection of Theorem 3.3 nor Theorems 2.1 and 2.2. -/
def IsExpBoundary (a : H2Cx M) (c : H3 M) : Prop :=
  ∃ (𝒰 : Cover M) (g : Cocycle (smoothUnits M) 𝒰 2) (f : Cochain (smoothC M) 𝒰 2)
    (n : Cocycle (locConstZ M) 𝒰 3),
    cechClass (smoothUnits M) g = a ∧ cechClass (locConstZ M) n = c ∧
    (∀ i x, Complex.exp (2 * Real.pi * Complex.I * complexVal (f i) x) =
      (unitsVal (g.1 i) x : ℂ)) ∧
    ∀ i x, complexVal (coboundary (smoothC M) 𝒰 2 f i) x = (intVal (n.1 i) x : ℂ)

end BundleGerbeStable


