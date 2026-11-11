-- Prove2me | Definitions.Def_IteratedLP_Gaussian_MinMax
-- name    : IteratedLP_Gaussian_MinMax
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:20:51.595585+00:00
-- url     : https://prove2.me/theorems/1e3c6c3b-21f7-414e-9e5c-0d02de819d18
-- title:
--   Primary and auxiliary min–max values of the Gaussian comparison (§3.1)
-- statement:
--   Let $C\subset\mathbb R^n$, $D\subset\mathbb R^m$ be nonempty compact sets and $\psi:C\times D\to\mathbb R$ continuous, and let $G\in\mathbb R^{m\times n}$, $g\in\mathbb R^m$, $h\in\mathbb R^n$ have mutually independent standard Gaussian entries. The **primary** and **auxiliary** values are
--   $$\Phi(G)=\min_{w\in C}\max_{u\in D}\{u^\top Gw+\psi(w,u)\},\qquad \phi(g,h)=\min_{w\in C}\max_{u\in D}\{\|w\|g^\top u+\|u\|h^\top w+\psi(w,u)\},$$
--   with $\|\cdot\|$ the Euclidean norm; the max–min versions exchange the order of the two optimizations. A **primary minimizer** is a $w\in C$ at which the inner maximum equals $\Phi(G)$ (and symmetrically for a primary maximizer of a max–min problem).
--
--   These are the objects of the Gaussian min–max comparison (Theorem 3.1) and of the localization Corollary 3.2.
--
--   **Formalization Note.** `eNorm w = √(Σ wᵢ²)` (Lean's default norm on `Fin n → ℝ` is the sup norm). `minMax C D f = ⨅ w : C, ⨆ u : D, f w u` and `maxMin` are real infima and suprema over subtypes; for nonempty compact $C,D$ and $f$ continuous on $C\times D$ both are attained, so they are the paper's min and max. `gaussTriple m n` is the product law of $(G,g,h)$.
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 13, §3.1, eqs. (3.1)–(3.2)

import Mathlib

open MeasureTheory ProbabilityTheory Matrix

namespace IteratedLP.Gaussian

/-- The Euclidean norm `‖w‖ = (Σ_i w_i²)^{1/2}` on `ℝ^n` (Lean's default norm on `Fin n → ℝ` is
the sup norm, which is not the paper's). -/
noncomputable def eNorm {n : ℕ} (w : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, w i ^ 2)

/-- The law of `(G, g, h)` with `G ∈ ℝ^{m×n}`, `g ∈ ℝ^m`, `h ∈ ℝ^n` having mutually independent
standard Gaussian entries (§3.1, p. 13). -/
noncomputable def gaussTriple (m n : ℕ) :
    Measure ((Fin m → Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => gaussianReal 0 1))).prod
    ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)))

/-- The primary payoff `u⊤ G w + ψ(w, u)`. -/
def primaryPayoff {m n : ℕ} (ψ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (G : Fin m → Fin n → ℝ)
    (w : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  u ⬝ᵥ (Matrix.of G *ᵥ w) + ψ w u

/-- The auxiliary payoff `‖w‖ g⊤u + ‖u‖ h⊤w + ψ(w, u)` (Euclidean norms). -/
noncomputable def auxPayoff {m n : ℕ} (ψ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (g : Fin m → ℝ)
    (h : Fin n → ℝ) (w : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  eNorm w * (g ⬝ᵥ u) + eNorm u * (h ⬝ᵥ w) + ψ w u

/-- `min_{w ∈ C} max_{u ∈ D} f(w, u)`. For nonempty compact `C`, `D` and `f` continuous on
`C × D` both extrema are attained, so the real infimum and supremum are the min and max. -/
noncomputable def minMax {m n : ℕ} (C : Set (Fin n → ℝ)) (D : Set (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) : ℝ :=
  ⨅ w : C, ⨆ u : D, f w u

/-- `max_{w ∈ C} min_{u ∈ D} f(w, u)` (max–min order, Corollary 3.2(ii)). -/
noncomputable def maxMin {m n : ℕ} (C : Set (Fin n → ℝ)) (D : Set (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) : ℝ :=
  ⨆ w : C, ⨅ u : D, f w u

/-- `w` is a minimizer of the min–max problem: `w ∈ C` and `max_{u ∈ D} f(w, u)` equals the
min–max value. -/
def IsMinMaxMinimizer {m n : ℕ} (C : Set (Fin n → ℝ)) (D : Set (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (w : Fin n → ℝ) : Prop :=
  w ∈ C ∧ (⨆ u : D, f w u) = minMax C D f

/-- `w` is a maximizer of the max–min problem: `w ∈ C` and `min_{u ∈ D} f(w, u)` equals the
max–min value. -/
def IsMaxMinMaximizer {m n : ℕ} (C : Set (Fin n → ℝ)) (D : Set (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (w : Fin n → ℝ) : Prop :=
  w ∈ C ∧ (⨅ u : D, f w u) = maxMin C D f

end IteratedLP.Gaussian


