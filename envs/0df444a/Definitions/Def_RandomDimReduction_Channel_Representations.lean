-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Representations
-- name    : RandomDimReduction_Channel_Representations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:23:44.594991+00:00
-- url     : https://prove2.me/theorems/3a04bc30-6161-42cd-9c4d-54089111bd8f
-- title:
--   Finite unitary irreducibles and orthogonal multiplicity decompositions
-- statement:
--   A finite unitary matrix representation is irreducible when its carrier is nonzero and its only invariant complex subspaces are zero and the whole space. Two such representations are inequivalent when no unitary intertwiner identifies them. An orthogonal multiplicity decomposition is a unitary coordinate map $T$ satisfying
--   $$ T r(g)T^\dagger=\bigoplus_\lambda I_{m_\lambda}\otimes\rho_\lambda(g). $$
--   Multiplicities may be zero. These definitions concern the representation setting only; they assume no statement about a separate intertwining operator. They provide the common coordinates needed for the rectangular conclusion of Lemma B.2.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Appendix B, setting preceding Lemma B.2, pp.22–23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Tensor

set_option autoImplicit false

noncomputable section
open Matrix
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Irreducibility of a finite unitary matrix representation: nonzero carrier,
with no proper nonzero complex invariant subspace. -/
def Irreducible {G : Type*} [Group G] {d : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  0 < d ∧ ∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin d)),
    (∀ g, ∀ x ∈ S, Matrix.toEuclideanLin (r g : Op (Fin d)) x ∈ S) → S = ⊥ ∨ S = ⊤

/-- Inequivalence of unitary irreducibles, expressed without a chosen coordinate change. -/
def Inequivalent {G : Type*} [Group G] {d e : ℕ}
    (r : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (s : G →* Matrix.unitaryGroup (Fin e) ℂ) : Prop :=
  ¬ ∃ T : Matrix (Fin e) (Fin d) ℂ,
    Tᴴ * T = 1 ∧ T * Tᴴ = 1 ∧ ∀ g, T * (r g : Op (Fin d)) = (s g : Op _) * T

abbrev RepIndex {L : Type*} (m d : L → ℕ) := (l : L) × (Fin (m l) × Fin (d l))

/-- The unitary coordinate decompositions in the setting preceding Lemma B.2. -/
structure RepDecomposition {G L : Type} [Group G] [Fintype L]
    {a : ℕ} (m d : L → ℕ)
    (r : G →* Matrix.unitaryGroup (Fin a) ℂ)
    (rho : ∀ l, G →* Matrix.unitaryGroup (Fin (d l)) ℂ) where
  T : Matrix (RepIndex m d) (Fin a) ℂ
  left_unitary : T * Tᴴ = 1
  right_unitary : Tᴴ * T = 1
  intertwines : ∀ g, T * (r g : Op (Fin a)) * Tᴴ =
    Matrix.blockDiagonal' (fun l => Matrix.kronecker (1 : Op (Fin (m l))) (rho l g : Op (Fin (d l))))

end RandomDimReduction.Channel


