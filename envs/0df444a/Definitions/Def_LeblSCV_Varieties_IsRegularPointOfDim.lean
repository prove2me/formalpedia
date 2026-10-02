-- Prove2me | Definitions.Def_LeblSCV_Varieties_IsRegularPointOfDim
-- name    : LeblSCV_Varieties_IsRegularPointOfDim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:28.519979+00:00
-- url     : https://prove2.me/theorems/1fa31ca7-316a-41a5-aa71-a2c895fe5604
-- title:
--   Definition 6.5.5 — regular point of dimension $k$
-- statement:
--   Let $X \subset \mathbb{C}^n$ and $p \in X$. The point $p$ is a **regular point of $X$ of dimension $k$** (and one writes $\dim_p X = k$) if, after a permutation of the coordinates, written $z = (z', z'') \in \mathbb{C}^k \times \mathbb{C}^{n-k}$ for some $k \in \{0, 1, \dots, n\}$, there are a neighborhood $U' \times U'' \subset \mathbb{C}^k \times \mathbb{C}^{n-k}$ of $p$ and a holomorphic map $g : U' \to \mathbb{C}^{n-k}$ such that
--   $$X \cap (U' \times U'') = \Gamma_g = \{ (z', z'') \in U' \times \mathbb{C}^{n-k} : z'' = g(z') \}.$$
--   The case $k = 0$ covers isolated points of $X$, and $k = n$ covers points near which $X$ is open.
--
--   Near a regular point a subvariety is a complex submanifold; this definition underlies $X_{\mathrm{reg}}$, $X_{\mathrm{sing}}$ and the notion of dimension.
--
--   **Formalization Note.** The permutation together with the split is an equivalence `e : Fin n ≃ Fin k ⊕ Fin m` (so $k + m = n$, with no natural-number subtraction); $z'$ and $z''$ are the coordinates of $z$ indexed through `e`. $U'$, $U''$ are open, $g$ is `DifferentiableOn ℂ` on $U'$, and the graph condition is a set equality, so it forces $g(U') \subset U''$ exactly as the book's equality does.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 185, Definition 6.5.5 (graph Γ_f defined on p. 184)

import Mathlib

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.5.5: `p ∈ X` is a **regular point of `X` of dimension `k`** (`dim_p X = k`):
after a relabeling of the coordinates, written `z ↦ (z', z'') ∈ ℂᵏ × ℂᵐ` with `k + m = n`
(the relabeling is the equivalence `e : Fin n ≃ Fin k ⊕ Fin m`), there are open sets
`U' ⊆ ℂᵏ`, `U'' ⊆ ℂᵐ` with `p ∈ U' × U''` and a holomorphic `g : U' → ℂᵐ` such that
`X ∩ (U' × U'') = Γ_g = {(z', z'') : z' ∈ U', z'' = g(z')}`.
`k = 0` (isolated points) and `k = n` (open pieces) are included. -/
def IsRegularPointOfDim {n : ℕ} (X : Set (Fin n → ℂ)) (p : Fin n → ℂ) (k : ℕ) : Prop :=
  p ∈ X ∧
    ∃ (m : ℕ) (e : Fin n ≃ Fin k ⊕ Fin m) (U' : Set (Fin k → ℂ)) (U'' : Set (Fin m → ℂ))
      (g : (Fin k → ℂ) → (Fin m → ℂ)),
      IsOpen U' ∧ IsOpen U'' ∧
      (fun i => p (e.symm (Sum.inl i))) ∈ U' ∧ (fun j => p (e.symm (Sum.inr j))) ∈ U'' ∧
      DifferentiableOn ℂ g U' ∧
      X ∩ {z | (fun i => z (e.symm (Sum.inl i))) ∈ U' ∧ (fun j => z (e.symm (Sum.inr j))) ∈ U''} =
        {z | (fun i => z (e.symm (Sum.inl i))) ∈ U' ∧
          (fun j => z (e.symm (Sum.inr j))) = g (fun i => z (e.symm (Sum.inl i)))}

end LeblSCV.Varieties


