-- Prove2me | Definitions.Def_TIESharp_WeakStarTendsto
-- name    : TIESharp_WeakStarTendsto
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:55.555213+00:00
-- url     : https://prove2.me/theorems/7f04d646-e22f-41b2-9077-c2f21f52816e
-- title:
--   Weak-star convergence on every bounded profile box
-- statement:
--   A sequence of functions $f_\ell$ on $\mathbb R^{n\times m}$ **converges weak-star on every bounded profile box** to $g$ if, for every $M>0$, on the box $B_M=(0,M)^{n\times m}$ the functions $f_\ell$ and $g$ are measurable and essentially bounded (the $f_\ell$ uniformly in $\ell$), and
--   $$\int_{B_M}f_\ell(t)\,\varphi(t)\,dt\ \longrightarrow\ \int_{B_M}g(t)\,\varphi(t)\,dt\qquad(\ell\to\infty)$$
--   for every test function $\varphi\in L^1(B_M)$. This is convergence in the weak-star topology of $L^\infty(B_M)=L^1(B_M)^*$, as in the proof of Lemma 4.3.
--
--   **Formalization Note.** Lebesgue measure on `Fin n → Fin m → ℝ` restricted to the open box. Measurability and boundedness are built in, so no integral is a junk Bochner value.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §4.2.1, p.17

import Mathlib

set_option autoImplicit false

namespace TIESharp

open MeasureTheory Filter Topology

/-- **Weak-star convergence on every bounded profile box** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §4.2.1, p.17): on each box
`(0, M)^{n×m}`, `M > 0`, the functions `f ℓ` and `g` are (essentially) bounded and measurable,
the `f ℓ` uniformly in `ℓ`, and "the integral of each displayed coordinate against any `L¹` test
function on the box converges": `∫_box f_ℓ φ → ∫_box g φ` as `ℓ → ∞` for every `φ ∈ L¹(box)`.
This is weak-star convergence in `L^∞(box) = (L¹(box))*`.

**Formalization Note.** Lebesgue measure `volume` on `Fin n → Fin m → ℝ` restricted to the open
box. Measurability and boundedness on the box are part of the definition, so the integrals are
never junk Bochner values. -/
def WeakStarTendsto {n m : ℕ} (f : ℕ → (Fin n → Fin m → ℝ) → ℝ)
    (g : (Fin n → Fin m → ℝ) → ℝ) : Prop :=
  ∀ M : ℝ, 0 < M →
    (∀ ℓ, AEStronglyMeasurable (f ℓ)
      (volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M})) ∧
    AEStronglyMeasurable g
      (volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M}) ∧
    (∃ C : ℝ, ∀ ℓ, ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M}),
      |f ℓ t| ≤ C) ∧
    (∃ C : ℝ, ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M}),
      |g t| ≤ C) ∧
    ∀ φ : (Fin n → Fin m → ℝ) → ℝ,
      Integrable φ (volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M}) →
      Tendsto
        (fun ℓ => ∫ t in {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M}, f ℓ t * φ t)
        atTop
        (𝓝 (∫ t in {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M}, g t * φ t))

end TIESharp


