-- Prove2me | Definitions.Def_HunterPDE_Sobolev_SobolevSpace
-- name    : HunterPDE_Sobolev_SobolevSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:18:18.390977+00:00
-- url     : https://prove2.me/theorems/1a45dc54-ee8e-406e-a3d7-bea90ba86e29
-- title:
--   Definitions 3.1, 3.2 and 3.23 — weak derivatives, W^{k,p}(Ω) and its norm
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open. A **test function** $\varphi \in C_c^\infty(\Omega)$ is an infinitely differentiable function whose support is a compact subset of $\Omega$. For $i = 1, \dots, n$, $\partial_i$ denotes the partial derivative in the $i$th coordinate direction, and for a multi-index $\alpha = (\alpha_1, \dots, \alpha_n) \in \mathbb{N}_0^n$ of order $|\alpha| = \alpha_1 + \dots + \alpha_n$ we write $\partial^\alpha = \partial_1^{\alpha_1} \cdots \partial_n^{\alpha_n}$.
--
--   **Definition 3.1.** A function $f \in L^1_{\mathrm{loc}}(\Omega)$ is **weakly differentiable with respect to $x_i$** if there is $g_i \in L^1_{\mathrm{loc}}(\Omega)$ with
--   $$\int_\Omega f\, \partial_i \varphi \, dx = -\int_\Omega g_i\, \varphi \, dx \qquad \text{for all } \varphi \in C_c^\infty(\Omega);$$
--   $g_i$ is the weak $i$th partial derivative $\partial_i f$.
--
--   **Definition 3.2.** $f \in L^1_{\mathrm{loc}}(\Omega)$ has **weak derivative** $\partial^\alpha f = g \in L^1_{\mathrm{loc}}(\Omega)$ if
--   $$\int_\Omega g\, \varphi \, dx = (-1)^{|\alpha|} \int_\Omega f\, \partial^\alpha \varphi \, dx \qquad \text{for all } \varphi \in C_c^\infty(\Omega).$$
--
--   **Definition 3.23.** For $k \in \mathbb{N}$ and $1 \le p \le \infty$, the **Sobolev space** $W^{k,p}(\Omega)$ consists of the locally integrable $f : \Omega \to \mathbb{R}$ such that $\partial^\alpha f$ exists weakly and lies in $L^p(\Omega)$ for $0 \le |\alpha| \le k$. Its norm is
--   $$\|f\|_{W^{k,p}(\Omega)} = \Big( \sum_{|\alpha| \le k} \int_\Omega |\partial^\alpha f|^p \, dx \Big)^{1/p} \quad (1 \le p < \infty), \qquad \|f\|_{W^{k,\infty}(\Omega)} = \max_{|\alpha| \le k} \sup_\Omega |\partial^\alpha f|.$$
--
--   These are the objects on which the approximation theorem (3.24) and the embedding $W^{1,p} \hookrightarrow L^q$ (3.31) are stated.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure; functions are defined on all of $\mathbb{R}^n$ and only their values on $\Omega$ matter. Coordinates are 0-based (`i : Fin n` is the book's $x_{i+1}$); a multi-index is `α : Fin n → ℕ`. Smoothness of test functions is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. $C^\infty$ (not `ContDiff ℝ ⊤`, which means analytic in current Mathlib and would leave only the zero test function); "support compactly contained in $\Omega$" is `HasCompactSupport φ ∧ tsupport φ ⊆ Ω`. $L^1_{\mathrm{loc}}(\Omega)$ is `LocallyIntegrableOn · Ω`. The classical $\partial^\alpha\varphi$ is obtained by iterating the coordinate partial derivatives `fderiv ℝ φ x (EuclideanSpace.single i 1)`. The norm is valued in $[0,\infty]$; it reads a chosen weak derivative `weakDeriv` (unique a.e. on $\Omega$, so the norm does not depend on the choice) and is meaningful for $f \in W^{k,p}(\Omega)$; for $p = \infty$ the supremum is the essential supremum, as functions are identified a.e. `WeaklyDifferentiable Ω f` means weakly differentiable with respect to every $x_i$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 47, Definition 3.1; p. 48, Definition 3.2; p. 58, Definition 3.23

import Mathlib

open MeasureTheory

namespace HunterPDE.Sobolev

/-- `φ ∈ C_c^∞(Ω)` (Hunter, *Notes on PDEs*, p. 2): `φ` is infinitely differentiable and its
support is a compact subset of the open set `Ω`. Smoothness is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`,
i.e. `C^∞`; note that `ContDiff ℝ ⊤` would mean *analytic* in current Mathlib and is deliberately
not used. -/
def IsTestFunction {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- The classical partial derivative `∂ᵢu(x)` in the coordinate direction `eᵢ`
(coordinates are 0-based: `i : Fin n` is the book's `x_{i+1}`). -/
noncomputable def partialDeriv {n : ℕ} (i : Fin n) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => fderiv ℝ u x (EuclideanSpace.single i 1)

/-- The classical derivative `∂^α u = ∂₁^{α₁} ⋯ ∂ₙ^{αₙ} u` for a multi-index `α : Fin n → ℕ`,
obtained by iterating the coordinate partial derivatives (for the smooth test functions to which
it is applied, the order of differentiation is irrelevant). -/
noncomputable def iteratedPartial {n : ℕ} (α : Fin n → ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  (List.finRange n).foldr (fun i v => (partialDeriv i)^[α i] v) u

/-- Definition 3.1 of Hunter, *Notes on PDEs*, p. 47: `g ∈ L¹_loc(Ω)` is the weak `i`th partial
derivative of `f ∈ L¹_loc(Ω)` if `∫_Ω f ∂ᵢφ dx = -∫_Ω g φ dx` for all `φ ∈ C_c^∞(Ω)`. -/
def HasWeakPartialDeriv {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (i : Fin n)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LocallyIntegrableOn f Ω ∧ LocallyIntegrableOn g Ω ∧
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, IsTestFunction Ω φ →
      ∫ x in Ω, f x * partialDeriv i φ x = -∫ x in Ω, g x * φ x

/-- Definition 3.1: `f` is weakly differentiable in `Ω` with respect to every coordinate. -/
def WeaklyDifferentiable {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, HasWeakPartialDeriv Ω i f g

/-- Definition 3.2 of Hunter, *Notes on PDEs*, p. 48: for a multi-index `α`, `f ∈ L¹_loc(Ω)` has
weak derivative `∂^α f = g ∈ L¹_loc(Ω)` if
`∫_Ω g φ dx = (-1)^{|α|} ∫_Ω f ∂^α φ dx` for all `φ ∈ C_c^∞(Ω)`, where `|α| = ∑ᵢ αᵢ`. -/
def HasWeakDeriv {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (α : Fin n → ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LocallyIntegrableOn f Ω ∧ LocallyIntegrableOn g Ω ∧
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, IsTestFunction Ω φ →
      ∫ x in Ω, g x * φ x = (-1 : ℝ) ^ (∑ i, α i) * ∫ x in Ω, f x * iteratedPartial α φ x

open Classical in
/-- A chosen weak derivative `∂^α f` (unique up to a.e. equality on `Ω` when it exists; `0` when
it does not — only used under the hypothesis that it exists). -/
noncomputable def weakDeriv {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (α : Fin n → ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  if h : ∃ g, HasWeakDeriv Ω α f g then h.choose else 0

/-- Definition 3.23 of Hunter, *Notes on PDEs*, p. 58: `f ∈ W^{k,p}(Ω)` if `f` is locally
integrable on `Ω` and every weak derivative `∂^α f`, `0 ≤ |α| ≤ k`, exists and lies in `Lᵖ(Ω)`. -/
def MemW {n : ℕ} (k : ℕ) (p : ENNReal) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LocallyIntegrableOn f Ω ∧
    ∀ α : Fin n → ℕ, ∑ i, α i ≤ k →
      ∃ g, HasWeakDeriv Ω α f g ∧ MemLp g p (volume.restrict Ω)

/-- The finite set of multi-indices `α ∈ ℕ₀ⁿ` with `|α| ≤ k`. -/
def multiIndices (n k : ℕ) : Finset (Fin n → ℕ) :=
  ((Finset.univ : Finset (Fin n → Fin (k + 1))).image (fun a i => (a i : ℕ))).filter
    (fun α => ∑ i, α i ≤ k)

/-- The norm of Definition 3.23 (p. 58):
`‖f‖_{W^{k,p}(Ω)} = (∑_{|α| ≤ k} ∫_Ω |∂^α f|^p dx)^{1/p}` for `1 ≤ p < ∞`, and
`‖f‖_{W^{k,∞}(Ω)} = max_{|α| ≤ k} sup_Ω |∂^α f|` (essential supremum, functions being identified
a.e.) for `p = ∞`. Valued in `ℝ≥0∞`; meaningful for `f ∈ W^{k,p}(Ω)`. -/
noncomputable def sobolevNorm {n : ℕ} (k : ℕ) (p : ENNReal) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ENNReal :=
  if p = ⊤ then
    (multiIndices n k).sup (fun α => eLpNorm (weakDeriv Ω α f) ⊤ (volume.restrict Ω))
  else
    (∑ α ∈ multiIndices n k, eLpNorm (weakDeriv Ω α f) p (volume.restrict Ω) ^ p.toReal)
      ^ (1 / p.toReal)

end HunterPDE.Sobolev


