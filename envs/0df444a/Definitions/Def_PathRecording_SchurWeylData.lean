-- Prove2me | Definitions.Def_PathRecording_SchurWeylData
-- name    : PathRecording_SchurWeylData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:41.56883+00:00
-- url     : https://prove2.me/theorems/a6bfea7d-09cd-4f89-bdf8-967cbfd86c17
-- title:
--   Schur–Weyl data: a Schur transform for $V^{\otimes t}$
-- statement:
--   Let $\rho:G\to U(N)$ be a continuous unitary representation and $t\ge0$. **Schur–Weyl data** for $\rho^{\otimes t}$ consist of:
--
--   1. a finite set of labels $\widehat G_t$;
--   2. for each $\lambda\in\widehat G_t$, an irreducible continuous unitary representation $\rho_\lambda:G\to U(V^\lambda_G)$ with $V^\lambda_G=\mathbb C^{\dim V^\lambda_G}$, such that distinct labels carry inequivalent representations;
--   3. for each $\lambda$, a multiplicity space $V^\lambda_{\mathcal A_t}=\mathbb C^{\dim V^\lambda_{\mathcal A_t}}$ with $\dim V^\lambda_{\mathcal A_t}>0$;
--   4. a unitary **Schur transform** $\mathrm{Schur}_t:V^{\otimes t}\to\bigoplus_{\lambda}V^\lambda_G\otimes V^\lambda_{\mathcal A_t}$ such that for all $g\in G$
--   $$\mathrm{Schur}_t\,\rho^{\otimes t}(g)\,\mathrm{Schur}_t^\dagger=\bigoplus_{\lambda\in\widehat G_t}\rho_\lambda(g)\otimes I_{V^\lambda_{\mathcal A_t}}.$$
--
--   The Schur basis vectors are $|\lambda,X,T\rangle$ with $X$ a basis index of $V^\lambda_G$ and $T$ one of $V^\lambda_{\mathcal A_t}$. The reachable tableau space is $\mathrm{Tab}_t=\bigoplus_{\lambda\in\widehat G_t}V^\lambda_G\otimes\overline{V^\lambda_G}$, with basis $|\lambda,X,Y\rangle$, and the path space $\mathrm{Path}_t=V^{\otimes t}\otimes\overline V^{\otimes t}$ has basis $|\vec x,\vec y\rangle$.
--
--   All operators of the path-recording oracle are built from these data, and every theorem of the mission holds for every choice of them. Their existence for every $t$ is Schur–Weyl duality (Theorem 3.11).
--
--   **Formalization Note** Irreducibility and isomorphism of the irreps are the published predicates `SymTensorNet.IsIrrep` ($d>0$ and no invariant subspace other than $0$ and $\mathbb C^d$) and `SymTensorNet.RepEquiv` (an invertible intertwiner); distinct labels are required to be non-isomorphic. Labels form a `Fintype` `ι`; the Schur transform is a matrix indexed by `Σ λ, Fin (dG λ) × Fin (dA λ)` and `Fin t → Fin N`, unitary in both orders. Only labels with $\dim V^\lambda_{\mathcal A_t}>0$ occur, matching $\widehat G_t=\{\lambda:\dim V^\lambda_{\mathcal A_t}>0\}$ (p.62).
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 3.11, p.34; Definition 3.22, p.40; §5.1–5.2, pp.60–62 (Ĝ_t, Tab_t, Path_t)

import Mathlib
import Definitions.Def_PathRecording_tensorPow
import Definitions.Def_SymTensorNet_IrrepCatalogue

set_option autoImplicit false

namespace PathRecording

/-!
# Schur–Weyl data: a Schur transform for `V^{⊗t}`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 3.11, p.34, Definition 3.22, p.40 and §5.1–5.2, pp.60–62.

Definition 3.22: "A Schur transform is any family of unitary, G-respecting isomorphisms
Schur_{ρ,t} : V^{⊗t} → ⨁_λ (V^λ_G ⊗ V^λ_{𝒜_t}), meaning that for all g ∈ G,
Schur_{ρ,t} ρ(g)^{⊗t} Schur†_{ρ,t} = ⨁_{λ∈Ĝ} (ρ_λ(g) ⊗ I_{V^λ_{𝒜_t}})", where the `V^λ_G` are
irreducible representations of `G` (Theorem 3.11). The labels that occur form
`Ĝ_t = {λ ∈ Ĝ : dim V^λ_{𝒜_t} > 0}` (p.62).

**Formalization Note.**
* The labels `λ ∈ Ĝ_t` form a finite type `ι`. For each label, `V^λ_G = ℂ^{dG λ}` carries the
  irreducible continuous unitary representation `irrep λ` (in a fixed orthonormal basis, the
  `|X⟩` of Definition 3.7; irreducibility and equivalence are the published predicates
  `SymTensorNet.IsIrrep` and `SymTensorNet.RepEquiv`), and `V^λ_{𝒜_t} = ℂ^{dA λ}` with `dA λ > 0` (only labels of `Ĝ_t` occur).
  Distinct labels carry inequivalent irreps (they are distinct elements of `Ĝ`).
* `schur` is the matrix of `Schur_t` from the product basis `|x⃗⟩` of `V^{⊗t}` to the Schur basis
  `|λ, X, T⟩`, indexed by `Σ λ, Fin (dG λ) × Fin (dA λ)`; it is unitary and intertwines
  `ρ^{⊗t}(g)` with the block-diagonal `⨁_λ ρ_λ(g) ⊗ I`.
* The structure is universally quantified in every statement of the mission: the results hold for
  every choice of Schur transform. Existence for every `t` is Theorem 3.11 (a milestone).
-/

open Matrix Kronecker

/-- The path basis index of `Path_t = V^{⊗t} ⊗ \overline{V}^{⊗t}`: pairs `(x⃗, y⃗)`, the path
basis vector `|x⃗, y⃗⟩ = |x₁,…,x_t⟩ ⊗ |y₁,…,y_t⟩` (arXiv:2606.30281v2, p.60). -/
abbrev PathIdx (N t : ℕ) := (Fin t → Fin N) × (Fin t → Fin N)

variable {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ}

/-- Schur–Weyl data for `ρ^{⊗t}`: the reachable irrep labels `Ĝ_t`, the irreps `ρ_λ` on `V^λ_G`,
the multiplicity dimensions `dim V^λ_{𝒜_t}`, and a unitary Schur transform
(arXiv:2606.30281v2, Theorem 3.11, p.34; Definition 3.22, p.40; p.62). -/
structure SchurWeylData (ρ : UnitaryRep G N) (t : ℕ) where
  /-- The label set `Ĝ_t`. -/
  ι : Type
  [instFintype : Fintype ι]
  [instDecidableEq : DecidableEq ι]
  /-- `dim V^λ_G`. -/
  dG : ι → ℕ
  /-- `dim V^λ_{𝒜_t}`. -/
  dA : ι → ℕ
  /-- Only labels with `dim V^λ_{𝒜_t} > 0` occur. -/
  dA_pos : ∀ l, 0 < dA l
  /-- The irrep `ρ_λ` on `V^λ_G = ℂ^{dG λ}`. -/
  irrep : (l : ι) → UnitaryRep G (dG l)
  /-- Each `ρ_λ` is irreducible: `dG λ > 0` and no invariant subspace other than `0`, `ℂ^{dG λ}`. -/
  irrep_irreducible : ∀ l, SymTensorNet.IsIrrep (irrep l).toHom
  /-- Distinct labels carry inequivalent (non-isomorphic) irreps. -/
  irrep_inequivalent : ∀ l l', l ≠ l' → ¬ SymTensorNet.RepEquiv (irrep l).toHom (irrep l').toHom
  /-- The Schur transform `Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t}` as a matrix. -/
  schur : Matrix (Σ l, Fin (dG l) × Fin (dA l)) (Fin t → Fin N) ℂ
  /-- `Schur_t† Schur_t = I`. -/
  schur_isometry : schurᴴ * schur = 1
  /-- `Schur_t Schur_t† = I` (so `Schur_t` is unitary). -/
  schur_coisometry : schur * schurᴴ = 1
  /-- `Schur_t ρ^{⊗t}(g) Schur_t† = ⨁_λ ρ_λ(g) ⊗ I_{V^λ_{𝒜_t}}`. -/
  schur_intertwines : ∀ g, schur * tensorPow ρ t g * schurᴴ =
    blockDiagonal' fun l => (irrep l).mat g ⊗ₖ (1 : Matrix (Fin (dA l)) (Fin (dA l)) ℂ)

attribute [instance] SchurWeylData.instFintype SchurWeylData.instDecidableEq

namespace SchurWeylData

variable {ρ : UnitaryRep G N} {t : ℕ}

/-- The Schur basis index: `|λ, X, T⟩` with `X ∈ B(V^λ_G)`, `T ∈ B(V^λ_{𝒜_t})`. -/
abbrev SchurIdx (S : SchurWeylData ρ t) := Σ l : S.ι, Fin (S.dG l) × Fin (S.dA l)

/-- The basis index of the reachable tableau space
`Tab_t = ⨁_{λ∈Ĝ_t} V^λ_G ⊗ \overline{V^λ_G}`: `|λ, X, Y⟩` (arXiv:2606.30281v2, p.62). -/
abbrev TabIdx (S : SchurWeylData ρ t) := Σ l : S.ι, Fin (S.dG l) × Fin (S.dG l)

end SchurWeylData

end PathRecording


