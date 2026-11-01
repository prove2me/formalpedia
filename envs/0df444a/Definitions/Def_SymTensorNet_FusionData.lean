-- Prove2me | Definitions.Def_SymTensorNet_FusionData
-- name    : SymTensorNet_FusionData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:26.50138+00:00
-- url     : https://prove2.me/theorems/5bb97ed9-239a-4483-a743-4909ae8711dd
-- title:
--   Fusion data (Clebsch–Gordan isometries) and conjugation data for a catalogue of irreps
-- statement:
--   Let $U^a$ ($a\in A$) be a catalogue of irreps of a group $G$.
--
--   **Fusion data** consists of:
--   1. a **trivial charge** $0$ with $\dim 0=1$ and $U^0_g=1$;
--   2. for each pair of charges $(a,b)$, a finite set of **fusion channels** $\kappa$, each with an output charge $\mathrm{out}(\kappa)$ and a $(\dim a\cdot\dim b)\times\dim\mathrm{out}(\kappa)$ matrix $\iota_\kappa$ (the Clebsch–Gordan coefficients $(Q^{abc})_{m_an_bo_c}$, $c=\mathrm{out}(\kappa)$), such that
--      - $(U^a_g\otimes U^b_g)\,\iota_\kappa=\iota_\kappa\,U^{\mathrm{out}(\kappa)}_g$ for all $g$ (intertwiner);
--      - $\iota_\kappa^\dagger\iota_\kappa=1$ and $\iota_\kappa^\dagger\iota_{\kappa'}=0$ for $\kappa\neq\kappa'$ (orthonormal);
--      - $\sum_\kappa\iota_\kappa\iota_\kappa^\dagger=1$ (complete).
--
--   Together these say that the columns of the $\iota_\kappa$ form the coupled basis $|c,o_c\rangle$ of Eq. (9), $\mathbb V^a\otimes\mathbb V^b\cong\bigoplus_c N^c_{ab}\mathbb V^c$, where $N^c_{ab}$ is the number of channels with output $c$.
--
--   **Conjugation data** consists of, for each charge $a$, a charge $\bar a$ and a unitary matrix $J^a$ with
--   $$J^a\,\overline{U^a_g}=U^{\bar a}_g\,J^a\qquad\text{for all }g,$$
--   so the complex conjugate of each catalogue irrep is unitarily equivalent to a catalogue irrep. It converts incoming legs, on which $G$ acts by the conjugate representation, into outgoing ones.
--
--   **Formalization Note** The paper assumes $G$ multiplicity free ($N^c_{ab}\le 1$) "for notational simplicity", and footnote [10] adds an index $\mu=1,\dots,N^c_{ab}$ otherwise. The channels $\kappa$ play the role of the pairs $(c,\mu)$; the multiplicity-free case is the one where distinct channels of $(a,b)$ have distinct outputs. The paper does not name $\bar a$ or $J^a$.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, p.2 ("We denote by a = 0 the charge corresponding to the trivial irrep"), Eq. (9) and the change of basis (Q^{abc}), p.2; Eq. (7), p.2; footnote [10], p.4

import Mathlib
import Definitions.Def_SymTensorNet_IrrepCatalogue

namespace SymTensorNet

open Matrix
open scoped Kronecker

universe u v

/-- **Fusion data** for a catalogue of irreps of `G`.

1. A trivial charge `0` (`unit`) with `dim 0 = 1` and `U⁰_g = 1`.
2. For every pair of charges `(a, b)` a finite type `Chan a b` of fusion channels `κ`, each with an
   output charge `out κ` and a matrix `ι_κ` with rows `Fin (dim a) × Fin (dim b)` and columns
   `Fin (dim (out κ))` (the Clebsch–Gordan coefficients `(Q^{abc})_{m_a n_b o_c}`, `c = out κ`),
   such that
   - (intertwiner) `(Uᵃ_g ⊗ Uᵇ_g) ι_κ = ι_κ U^{out κ}_g`;
   - (orthonormal) `ι_κ† ι_κ = 1`, and `ι_κ† ι_κ′ = 0` for `κ ≠ κ′` (also when the outputs differ);
   - (complete) `Σ_κ ι_κ ι_κ† = 1`.

arXiv:0907.2994v2, p.2: "We denote by a = 0 the charge corresponding to the trivial irrep, so that
𝕍⁰ ≅ ℂ and U⁰_g = 1", and Eq. (9) `𝕍ᵃ ⊗ 𝕍ᵇ ≅ ⊕_c N^c_{ab} 𝕍^c`, with `(Q^{abc})_{m_a n_b o_c}`
"the change of basis between the product basis |a, m_a⟩ ⊗ |b, n_b⟩ and the coupled basis
|c, o_c⟩"; footnote [10], p.4, for the multiplicity index.

**Formalization Note** The paper assumes `G` multiplicity free (`N^c_{ab} ≤ 1`) "for notational
simplicity" and footnote [10] adds an index `μ = 1, …, N^c_{ab}` otherwise. Here the channels `κ`
play the role of the pairs `(c, μ)`; multiplicity freeness is the special case where `out` is
injective on each `Chan a b`. -/
structure FusionData (G : Type u) [Group G] extends IrrepCatalogue.{u, v} G where
  /-- The trivial charge `0`. -/
  unit : Charge
  dim_unit : dim unit = 1
  rep_unit : ∀ g : G, (rep unit g : Matrix (Fin (dim unit)) (Fin (dim unit)) ℂ) = 1
  /-- The fusion channels of `a ⊗ b`. -/
  Chan : Charge → Charge → Type v
  [chanFintype : ∀ a b, Fintype (Chan a b)]
  [chanDecEq : ∀ a b, DecidableEq (Chan a b)]
  /-- The output charge of a channel. -/
  out : {a b : Charge} → Chan a b → Charge
  /-- The isometry `ι_κ : 𝕍^{out κ} → 𝕍ᵃ ⊗ 𝕍ᵇ` (Clebsch–Gordan coefficients). -/
  iso : {a b : Charge} → (κ : Chan a b) → Matrix (Fin (dim a) × Fin (dim b)) (Fin (dim (out κ))) ℂ
  iso_intertwine : ∀ {a b : Charge} (κ : Chan a b) (g : G),
    ((rep a g : Matrix (Fin (dim a)) (Fin (dim a)) ℂ) ⊗ₖ
        (rep b g : Matrix (Fin (dim b)) (Fin (dim b)) ℂ)) * iso κ =
      iso κ * (rep (out κ) g : Matrix (Fin (dim (out κ))) (Fin (dim (out κ))) ℂ)
  iso_isometry : ∀ {a b : Charge} (κ : Chan a b), (iso κ)ᴴ * iso κ = 1
  iso_orthogonal : ∀ {a b : Charge} (κ κ' : Chan a b), κ ≠ κ' → (iso κ)ᴴ * iso κ' = 0
  iso_complete : ∀ a b : Charge, ∑ κ : Chan a b, iso κ * (iso κ)ᴴ = 1

attribute [instance] FusionData.chanFintype FusionData.chanDecEq

/-- **Conjugation data** for a catalogue: for every charge `a` a charge `ā` and a unitary `Jᵃ`
(rows `Fin (dim ā)`, columns `Fin (dim a)`) with `Jᵃ conj(Uᵃ_g) = U^ā_g Jᵃ`, i.e. the conjugate
representation of `Uᵃ` is unitarily equivalent to the catalogue irrep `U^ā`.

arXiv:0907.2994v2, p.2, Eq. (7) (an incoming index transforms with `W†_g`, i.e. with the conjugate
representation) and Eq. (15) ("intertwining operators between the tensor products of incoming
and outgoing irreps").

**Formalization Note** The paper does not name `ā` or `J`; they convert incoming legs into
outgoing ones so that one fusion tree handles every combination of directions. When the root is
incoming and all other legs are outgoing, they do not appear. -/
structure ConjData {G : Type*} [Group G] (C : IrrepCatalogue G) where
  /-- The conjugate charge `ā`. -/
  conj : C.Charge → C.Charge
  /-- The unitary `Jᵃ : 𝕍ᵃ → 𝕍^ā` intertwining `conj(Uᵃ)` with `U^ā`. -/
  J : (a : C.Charge) → Matrix (Fin (C.dim (conj a))) (Fin (C.dim a)) ℂ
  J_unitary : ∀ a, J a * (J a)ᴴ = 1 ∧ (J a)ᴴ * J a = 1
  J_intertwine : ∀ (a : C.Charge) (g : G),
    J a * (C.rep a g : Matrix (Fin (C.dim a)) (Fin (C.dim a)) ℂ).map star =
      (C.rep (conj a) g : Matrix (Fin (C.dim (conj a))) (Fin (C.dim (conj a))) ℂ) * J a

end SymTensorNet


