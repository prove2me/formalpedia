-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope
-- name    : MomentPolytopes_QuantumFunctionals_EntanglementPolytope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:03:34.080079+00:00
-- url     : https://prove2.me/theorems/9b2238ca-3180-4421-a33b-3db7acc0ce9c
-- title:
--   Weyl chamber and the entanglement polytope Δ(T) (with closure)
-- statement:
--   Identify the Cartan subspace $A$ of tuples of real diagonal matrices with $\mathbb R^{n_1}\times\dots\times\mathbb R^{n_d}$, and the Weyl chamber with
--   $$C=\mathbb R^{n_1}_\downarrow\times\dots\times\mathbb R^{n_d}_\downarrow .$$
--   For a tuple $X$ of Hermitian matrices, $\operatorname{spec}X=(\operatorname{spec}X_1,\dots,\operatorname{spec}X_d)$ (each sorted nonincreasingly).
--
--   The **entanglement polytope** of a tensor tuple $T\ne0$ is the closure
--   $$\Delta(T)=\overline{\Big\{\big(\operatorname{spec}\mu(S)_1,\dots,\operatorname{spec}\mu(S)_d\big)\ \Big|\ S=(I\otimes g_1\otimes\dots\otimes g_d)T,\ g_\ell\in\mathrm{GL}(n_\ell)\Big\}}\subseteq C ,$$
--   where $\mu(S)_\ell=S^{(\ell)}S^{(\ell)\dagger}/\|S\|^2$. It is compact (and a convex polytope, which is not used).
--
--   **Formalization Note** The closure is taken in the product topology of $\prod_\ell\mathbb R^{n_\ell}$.
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 44, eq. (6.32); Example 2.1, p. 16

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction

set_option autoImplicit false

namespace MomentPolytopes.QuantumFunctionals

/-- Tuples of real vectors `(p_1, …, p_d) ∈ ℝ^{n_1} × ⋯ × ℝ^{n_d}`, identified with the Cartan
subspace `A` of tuples of real diagonal matrices (Example 2.1, p. 16; p. 44). -/
abbrev SpecTuple {d : ℕ} (n : Fin d → ℕ) : Type := (ℓ : Fin d) → Fin (n ℓ) → ℝ

variable {d n0 : ℕ} {n : Fin d → ℕ}

/-- Componentwise sorted spectra `spec(X_1, …, X_d) = (spec X_1, …, spec X_d)`, each in
nonincreasing order (Example 2.1, p. 16). -/
noncomputable def specTuple (X : MatTuple n) : SpecTuple n :=
  fun ℓ => spec (X ℓ)

/-- The Weyl chamber `C ≅ ℝ^{n_1}_↓ × ⋯ × ℝ^{n_d}_↓`: tuples of vectors with nonincreasing
entries (Example 2.1, p. 16; p. 44). -/
def weylChamber : Set (SpecTuple n) :=
  {p | ∀ ℓ, Antitone (p ℓ)}

/-- The entanglement polytope (eq. (6.32), p. 44): the **closure** of
`{(spec S^{(1)}S^{(1)†}/‖S‖², …, spec S^{(d)}S^{(d)†}/‖S‖²) | S = (I ⊗ g_1 ⊗ ⋯ ⊗ g_d) T,
g_ℓ ∈ GL(n_ℓ)}`, with `S^{(ℓ)}S^{(ℓ)†}/‖S‖² = µ(S)_ℓ`. -/
noncomputable def entanglementPolytope (T : Ten d n0 n) : Set (SpecTuple n) :=
  closure {p | ∃ g : GTuple n, p = specTuple (momentMap (gact g T))}

end MomentPolytopes.QuantumFunctionals


