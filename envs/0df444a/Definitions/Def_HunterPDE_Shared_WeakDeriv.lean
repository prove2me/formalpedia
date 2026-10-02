-- Prove2me | Definitions.Def_HunterPDE_Shared_WeakDeriv
-- name    : HunterPDE_Shared_WeakDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:31:18.222978+00:00
-- url     : https://prove2.me/theorems/673357e9-be57-4dc4-aab5-836799a8ab91
-- title:
--   Test functions C_c^∞(Ω) and weak derivatives (Definitions 3.1–3.2)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open. A **test function** $\phi \in C_c^\infty(\Omega)$ is an infinitely differentiable function $\phi : \mathbb{R}^n \to \mathbb{R}$ with compact support contained in $\Omega$.
--
--   Let $f, g \in L^1_{\mathrm{loc}}(\Omega)$ and $\alpha \in \mathbb{N}_0^n$. Then $g$ is the **weak derivative** $\partial^\alpha f$ of $f$ on $\Omega$ if
--   $$\int_\Omega g\,\phi \, dx = (-1)^{|\alpha|} \int_\Omega f\,\partial^\alpha \phi \, dx \qquad \text{for all } \phi \in C_c^\infty(\Omega).$$
--   The weak derivative is unique up to equality almost everywhere in $\Omega$. The pointwise length of the weak gradient is $|Df|(x) = \big(\sum_i (\partial_i f(x))^2\big)^{1/2}$.
--
--   It serves two missions of the series: Sobolev compactness and the half-space results (mission IV, Definition 3.23 and Theorems 3.41–3.48, pp. 58, 71–75) and interior elliptic regularity through difference quotients (mission VI, Proposition 4.52 and Theorem 4.53, pp. 124–125, and Theorems 4.27–4.29, pp. 112–114).
--
--   **Formalization Note.** Functions are real-valued on all of $\mathbb{R}^n$ (`EuclideanSpace ℝ (Fin n)`), and only their values on $\Omega$ matter. "$C^\infty$" is `ContDiff ℝ ∞` (smooth, not analytic). $\partial^\alpha \phi$ is the classical multi-index derivative of `HunterPDE.Shared.PartialDeriv`. `weakDeriv Ω α f` is a chosen representative when a weak derivative exists, and is the junk value $0$ otherwise; every statement that uses it assumes existence (through `MemW` or `HasWeakDeriv`). `weakGradNorm` uses the first-order multi-indices `Pi.single i 1`, with 0-based coordinates.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 47–48, Definitions 3.1–3.2

import Mathlib
import Definitions.Def_HunterPDE_Shared_PartialDeriv

open MeasureTheory
open scoped ContDiff

namespace HunterPDE.Shared

/-- `φ ∈ C_c^∞(Ω)`: `φ : ℝⁿ → ℝ` is infinitely differentiable (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`,
i.e. `C^∞`, not analytic), has compact support, and its (closed) support lies in `Ω`. -/
def IsTestFunction {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- Definition 3.2 (and 3.1 for `|α| = 1`) of Hunter, *Notes on PDEs*: `g` is a weak derivative
`∂^α f` of `f` on the open set `Ω`. Both `f` and `g` are locally integrable on `Ω`, and
`∫_Ω g φ dx = (-1)^{|α|} ∫_Ω f ∂^α φ dx` for every `φ ∈ C_c^∞(Ω)`. Real-valued functions,
multi-index `α : Fin n → ℕ` with `|α| = ∑ i, α i`, coordinates 0-based. Only the values of `f`
and `g` on `Ω` matter. -/
def HasWeakDeriv {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (α : Fin n → ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LocallyIntegrableOn f Ω volume ∧ LocallyIntegrableOn g Ω volume ∧
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, IsTestFunction Ω φ →
      ∫ x in Ω, g x * φ x = (-1 : ℝ) ^ (∑ i, α i) * ∫ x in Ω, f x * multiDeriv φ α x

open Classical in
/-- The weak derivative `∂^α f` on `Ω`, when one exists (it is then unique up to a.e. equality on
`Ω`, as the book notes after Definition 3.1); a chosen representative. When `f` has no weak
`∂^α` on `Ω` the value is the junk function `0`: every use in this development is guarded by a
hypothesis that the weak derivative exists. -/
noncomputable def weakDeriv {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (α : Fin n → ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  if h : ∃ g, HasWeakDeriv Ω α f g then h.choose else 0

/-- The pointwise Euclidean length `|Df(x)| = (∑ᵢ (∂ᵢ f(x))²)^{1/2}` of the weak gradient of `f`
on `Ω`, where `∂ᵢ f = weakDeriv Ω (Pi.single i 1) f` is the weak first partial derivative. -/
noncomputable def weakGradNorm {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ i : Fin n, (weakDeriv Ω (Pi.single i 1) f x) ^ 2)

end HunterPDE.Shared


