-- Prove2me | Definitions.Def_ChapterA3e
-- name    : ChapterA3e
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:01:38.589912+00:00
-- url     : https://prove2.me/theorems/398a039d-8fbe-4495-8d89-f02b02610e63
-- title:
--   Chapter A3e
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3e.lean`): generated def bundle for ChapterA3e. See BookProof/ChapterA3e.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3e.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3d
import Mathlib


/-!
# Chapter A, §A.3 — the Lie algebra `𝔰𝔭𝔦𝔫⁺(3,1)` (infinitesimal Note 47 / Lemma 48)

This file continues work-package **N4** of `FORMALIZATION_ROADMAP.md`
(book §A.3, **Note 47 / Lemma 48**, book line 5445).  The book characterizes the
restricted spin group by its Lie algebra,

`Spin⁺(3,1) = { e^{θʲ iγ⁵γ⁰γʲ + bʲ γ⁰γʲ} : θ, b ∈ ℝ³ }`,

whose Lie algebra `𝔰𝔭𝔦𝔫⁺(3,1)` is spanned by the six **spinor Lorentz
generators**

* the three **boosts**    `γ⁰γʲ = -(iγ⁰)(iγʲ)`   (`j = 1,2,3`), and
* the three **rotations**  `iγ⁵γ⁰γʲ = iγ⁵·(γ⁰γʲ)` (`j = 1,2,3`).

We formalize the *infinitesimal* content of Note 47 / Lemma 48 — the differential
`Λ_* : 𝔰𝔭𝔦𝔫⁺(3,1) → 𝔬(1,3)` of the two-to-one covering `Λ : Pin(3,1) → O(1,3)`
of `ChapterA3c.lean`.  Concretely, for a Lie-algebra element `G` the *adjoint*
(commutator) action on the Majorana basis is a real `4×4` matrix `A`:

`HasAdLambda G A  :  ∀ μ, [G, iγ^μ] = G·iγ^μ - iγ^μ·G = Σ_ν A^μ_ν iγ^ν`,

and this `A` lies in the **Lorentz Lie algebra** `𝔬(1,3) = {A | A η + η Aᵀ = 0}`
(the derivative of the defining relation `Λ η Λᵀ = η` of `LorentzO`).  Everything
is over `ℝ` on the concrete `4×4` Majorana model (`mgammaR`), and every
per-generator fact is a decidable integer-matrix computation (`decide`), so the
file is fully self-contained: **no external hypothesis** (no Pauli/Weyl input) is
needed.

Deliverables:
* generators `spinBoost j`, `spinRot j` and their explicit adjoint matrices
  `adBoost j`, `adRot j`;
* `spinGen_traceless` — the six generators are traceless (so their exponentials
  have unit determinant — the group-level `det S = 1` of Lemma 48);
* `spinBoost_hasAdLambda` / `spinRot_hasAdLambda` — `[G, iγ^μ] = Σ A^μ_ν iγ^ν`;
* `adBoost_mem_lorentzLie` / `adRot_mem_lorentzLie` — each adjoint matrix is in
  `𝔬(1,3)`;
* linearity (`hasAdLambda_add`, `hasAdLambda_smul`, `lorentzLie` a subspace) and
  the headline **`spinLie_hasAdLambda_lorentzLie`**: every element of
  `𝔰𝔭𝔦𝔫⁺(3,1)` has an adjoint matrix lying in `𝔬(1,3)` — i.e. the
  infinitesimal Lorentz map `Λ_*` is well-defined and lands in `𝔬(1,3)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).

**Remaining group-level step (recorded open item).**  Exponentiating this to the
group statement `Spin⁺(3,1) ⊆ Pin(3,1)` and `Λ(S) = Υ(Σ⁻¹SΣ)` requires the
matrix-exponential determinant identity `det (exp A) = exp (tr A)` — currently a
listed *TODO* in Mathlib (`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`)
— together with the adjoint-exponential identity `exp(-G)·X·exp(G) = exp(-ad_G)(X)`.
Those analytic ingredients are the recorded obstruction; the algebraic/Lie-algebra
core (this file) is complete.
-/

open Matrix

namespace BookProof.ChapterA3

/-! ## The integer generators and adjoint matrices -/

/-- The spatial index `j ↦ j+1 : Fin 4` (so `j = 0,1,2 ↦ 1,2,3`). -/
def spinIdx (j : Fin 3) : Fin 4 := ⟨j.val + 1, by omega⟩

/-- The boost generator `γ⁰γʲ = -(iγ⁰)(iγʲ)` over `ℤ`. -/
def spinBoostZ (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℤ :=
  -(mgammaZ 0 * mgammaZ (spinIdx j))

/-- The rotation generator `iγ⁵γ⁰γʲ = iγ⁵·(γ⁰γʲ)` over `ℤ`. -/
def spinRotZ (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℤ :=
  mgamma5Z * spinBoostZ j

/-- The adjoint (commutator) matrix of the boost `γ⁰γʲ` on the Majorana basis. -/
def adBoostZ : Fin 3 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0,-2,0,0; -2,0,0,0; 0,0,0,0; 0,0,0,0]
  | 1 => !![0,0,-2,0; 0,0,0,0; -2,0,0,0; 0,0,0,0]
  | 2 => !![0,0,0,-2; 0,0,0,0; 0,0,0,0; -2,0,0,0]

/-- The adjoint (commutator) matrix of the rotation `iγ⁵γ⁰γʲ` on the Majorana
basis. -/
def adRotZ : Fin 3 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0,0,0,0; 0,0,0,0; 0,0,0,2; 0,0,-2,0]
  | 1 => !![0,0,0,0; 0,0,0,-2; 0,0,0,0; 0,2,0,0]
  | 2 => !![0,0,0,0; 0,0,2,0; 0,-2,0,0; 0,0,0,0]

/-! ## The real generators and adjoint matrices -/

/-- The boost generator `γ⁰γʲ` as a real matrix. -/
noncomputable def spinBoost (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (spinBoostZ j)

/-- The rotation generator `iγ⁵γ⁰γʲ` as a real matrix. -/
noncomputable def spinRot (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (spinRotZ j)

/-- The adjoint matrix of the boost `γ⁰γʲ` as a real matrix. -/
noncomputable def adBoost (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (adBoostZ j)

/-- The adjoint matrix of the rotation `iγ⁵γ⁰γʲ` as a real matrix. -/
noncomputable def adRot (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (adRotZ j)

/-! ## The infinitesimal predicates -/

/-- `HasAdLambda G A`: the real matrix `A` describes the *adjoint* (commutator)
action of `G` on the Majorana basis, `[G, iγ^μ] = Σ_ν A^μ_ν (iγ^ν)`.  This is the
infinitesimal analogue of `HasLambda` (`ChapterA3c.lean`). -/
def HasAdLambda (G A : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ μ, G * mgammaR μ - mgammaR μ * G = ∑ ν, A μ ν • mgammaR ν

/-- The **Lorentz Lie algebra** `𝔬(1,3) = {A | A η + η Aᵀ = 0}`, the derivative of
the defining relation `Λ η Λᵀ = η` of `LorentzO`. -/
def LorentzLie : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {A | A * minkowskiMat + minkowskiMat * Aᵀ = 0}

/-! ## Casting helpers -/







/-! ## The generators are traceless -/





/-! ## The adjoint identities and `𝔬(1,3)` membership -/









/-! ## Linearity -/

















/-! ## The Lie algebra `𝔰𝔭𝔦𝔫⁺(3,1)` and the infinitesimal Lorentz map -/

/-- Membership in the Lie algebra `𝔰𝔭𝔦𝔫⁺(3,1)`: a real combination of the six
spinor Lorentz generators (three boosts `γ⁰γʲ`, three rotations `iγ⁵γ⁰γʲ`). -/
def IsSpinLie (G : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ b r : Fin 3 → ℝ,
    G = (∑ j, b j • spinBoost j) + ∑ j, r j • spinRot j





end BookProof.ChapterA3


