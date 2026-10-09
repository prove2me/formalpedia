-- Prove2me | Definitions.Def_LocalPF_Block_Dobrushin
-- name    : LocalPF_Block_Dobrushin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:27.494353+00:00
-- url     : https://prove2.me/theorems/1c72bfb7-7bfe-457c-a85f-1442ed9853a7
-- title:
--   §3.2, pp. 26–27 — versions of single-site conditional distributions, Dobrushin's matrix C and the local errors b
-- statement:
--   Let $I$ be a finite set and $\mathbb S=\prod_{i\in I}\mathbb S^i$ a product of Polish spaces, and let $\rho$ be a probability measure on $\mathbb S$. A **version of the regular conditional probability**
--   $$\rho^i_x(A)=\rho(X^i\in A\mid X^{I\setminus\{i\}}=x^{I\setminus\{i\}})$$
--   is a probability kernel $x\mapsto\rho^i_x$ from $\mathbb S$ to $\mathbb S^i$ such that $\rho^i_x$ depends on $x$ only through $x^{I\setminus\{i\}}$, and $\rho(B\cap\{X^i\in A\})=\int_B\rho^i_x(A)\,\rho(dx)$ for every measurable $A\subseteq\mathbb S^i$ and every measurable $B\subseteq\mathbb S$ that depends only on the coordinates in $I\setminus\{i\}$.
--
--   Given versions $\rho^i_\cdot$ of $\rho$ and $\tilde\rho^i_\cdot$ of a second probability measure $\tilde\rho$, Dobrushin's interdependence matrix and the local errors are
--   $$C_{ij}=\frac12\sup_{x,z\in\mathbb S:\,x^{I\setminus\{j\}}=z^{I\setminus\{j\}}}\|\rho^i_x-\rho^i_z\|,\qquad b_j=\sup_{x\in\mathbb S}\|\rho^j_x-\tilde\rho^j_x\|,$$
--   with $\|\cdot\|$ the norm $\sup_{|f|\le1}|\mu(f)-\nu(f)|$ of the Setting file.
--
--   These are the objects of the Dobrushin comparison theorem (Theorem 3.1).
--
--   **Formalization Note** $C_{ij}$ and $b_j$ are computed as suprema in $[0,\infty]$ and then converted to real numbers; for probability kernels they lie in $[0,1]$ and $[0,2]$, so the conversion loses nothing. Both depend on the chosen versions; Theorem 3.1 is stated for arbitrary versions.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), pp. 26–27, §3.2, Theorem 3.1

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

namespace LocalPF.Block

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {I : Type*} {Ss : I → Type*} [∀ i, MeasurableSpace (Ss i)]

/-- `γ` is a version of the regular conditional probability
`ρ^i_x(A) = ρ(X^i ∈ A | X^{I∖{i}} = x^{I∖{i}})` (§3.2, p. 26): `γ x` depends on `x` only through
`x^{I∖{i}}`, and for every measurable `A ⊆ 𝕊^i` and every measurable `B ⊆ 𝕊` that depends only
on the coordinates in `I∖{i}`, `ρ(B ∩ {X^i ∈ A}) = ∫_B γ_x(A) ρ(dx)`. -/
def IsCondVersion (ρ : Measure (∀ j, Ss j)) (i : I)
    (γ : ProbabilityTheory.Kernel (∀ j, Ss j) (Ss i)) : Prop :=
  (∀ x z : ∀ j, Ss j, (∀ j, j ≠ i → x j = z j) → γ x = γ z) ∧
  ∀ (A : Set (Ss i)) (B : Set (∀ j, Ss j)), MeasurableSet A → MeasurableSet B →
    (∀ x z : ∀ j, Ss j, (∀ j, j ≠ i → x j = z j) → (x ∈ B ↔ z ∈ B)) →
    ρ (B ∩ {x | x i ∈ A}) = ∫⁻ x in B, γ x A ∂ρ

/-- Dobrushin's interdependence matrix
`C_{ij} = (1/2) sup_{x, z : x^{I∖{j}} = z^{I∖{j}}} ‖ρ^i_x − ρ^i_z‖` (Theorem 3.1, p. 27), as a real
number (it lies in `[0, 1]` when every `ρ^i_x` is a probability measure). -/
def dobC (γ : ∀ i, ProbabilityTheory.Kernel (∀ j, Ss j) (Ss i)) (i j : I) : ℝ :=
  ((1 / 2 : ℝ≥0∞) * ⨆ (x : ∀ l, Ss l) (z : ∀ l, Ss l) (_ : ∀ l, l ≠ j → x l = z l),
    tv (γ i x) (γ i z)).toReal

/-- `b_j = sup_x ‖ρ^j_x − ρ̃^j_x‖` (Theorem 3.1, p. 27), as a real number (it lies in `[0, 2]`
when the conditionals are probability measures). -/
def dobB (γ γ' : ∀ i, ProbabilityTheory.Kernel (∀ j, Ss j) (Ss i)) (j : I) : ℝ :=
  (⨆ x : ∀ l, Ss l, tv (γ j x) (γ' j x)).toReal

end

end LocalPF.Block


