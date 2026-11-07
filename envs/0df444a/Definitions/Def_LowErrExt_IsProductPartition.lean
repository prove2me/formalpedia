-- Prove2me | Definitions.Def_LowErrExt_IsProductPartition
-- name    : LowErrExt_IsProductPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:35.390729+00:00
-- url     : https://prove2.me/theorems/93872258-e8b8-406b-adf4-4350c8a9bc03
-- title:
--   Product partition and the two sides of a fiber
-- statement:
--   A function $\Gamma:A\times B\to\Sigma$ is a **product partition** if every fiber $\Gamma^{-1}(\gamma)$ is a Cartesian product $A'\times B'$. For $\gamma\in\Sigma$ the module also defines the two sides of the fiber,
--   $$A_\gamma=\{x:\exists y,\ \Gamma(x,y)=\gamma\},\qquad B_\gamma=\{y:\exists x,\ \Gamma(x,y)=\gamma\}.$$
--   For a product partition and $\gamma$ in the image, $\Gamma^{-1}(\gamma)=A_\gamma\times B_\gamma$, so for independent $\mathbf X,\mathbf Y$ the conditional pair $(\mathbf X,\mathbf Y)|_{\Gamma(\mathbf X,\mathbf Y)=\gamma}$ is the independent pair $(\mathbf X|_{\mathbf X\in A_\gamma},\mathbf Y|_{\mathbf Y\in B_\gamma})$.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 2.21, p.19

import Mathlib

namespace LowErrExt

/-- **Product partition.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 2.21, p.19: "We say that a function Γ : X × Y → Σ is a product partition if every fiber
of Γ is a Cartesian product X′ × Y′ ⊆ X × Y." -/
def IsProductPartition {A B S : Type*} (Γ : A × B → S) : Prop :=
  ∀ γ : S, ∃ (A' : Set A) (B' : Set B), Γ ⁻¹' {γ} = A' ×ˢ B'

/-- **Left side of a fiber.** `fiberLeft Γ γ = {x | ∃ y, Γ(x, y) = γ}`. For a product partition
and `γ` in the image of `Γ`, the fiber `Γ⁻¹(γ)` is `fiberLeft Γ γ × fiberRight Γ γ`. -/
def fiberLeft {A B S : Type*} (Γ : A × B → S) (γ : S) : Set A :=
  {x | ∃ y, Γ (x, y) = γ}

/-- **Right side of a fiber.** `fiberRight Γ γ = {y | ∃ x, Γ(x, y) = γ}`.

**Formalization Note.** For independent `X, Y` and a product partition `Γ`, the conditional law
`(X, Y) | Γ(X, Y) = γ` is the independent pair `(X | X ∈ fiberLeft Γ γ, Y | Y ∈ fiberRight Γ γ)`;
statements condition each source on its side of the fiber. -/
def fiberRight {A B S : Type*} (Γ : A × B → S) (γ : S) : Set B :=
  {y | ∃ x, Γ (x, y) = γ}

end LowErrExt


