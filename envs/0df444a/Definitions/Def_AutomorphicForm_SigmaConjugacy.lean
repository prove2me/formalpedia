-- Prove2me | Definitions.Def_AutomorphicForm_SigmaConjugacy
-- name    : AutomorphicForm_SigmaConjugacy
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/755ab312-c90d-59f2-9673-0103021d9c6b
-- title:
--   Sigma-twisted conjugacy in GL(2) over a field
-- statement:
--   Throughout, $L$ is a field and $\sigma \colon L \to L$ a ring endomorphism. For $g, \delta \in \mathrm{GL}_2(L)$, [`AutomorphicForm.sigmaConj`](../def/AutomorphicForm_SigmaConjugacy.html#L11) is the element
--   $$\mathrm{sigmaConj}\,\sigma\,g\,\delta = g\,\delta\,\bigl(\sigma(g)\bigr)^{-1},$$
--   where $\sigma(g)$ denotes the image of $g$ under the map on general linear groups induced by $\sigma$ (Mathlib's `Matrix.GeneralLinearGroup.map`, i.e. $\sigma$ applied entrywise). Note that $\sigma$ is applied only to the twisting element $g$, never to $\delta$. The predicate [`AutomorphicForm.IsSigmaConj σ δ δ'`](../def/AutomorphicForm_SigmaConjugacy.html#L15) asserts the existence of some $g \in \mathrm{GL}_2(L)$ with $\delta' = g\,\delta\,\sigma(g)^{-1}$, and [`AutomorphicForm.sigmaConjClassOf σ δ`](../def/AutomorphicForm_SigmaConjugacy.html#L18) is the set of all $\delta'$ satisfying this, i.e. the $\sigma$-twisted conjugacy class of $\delta$, realised as a subset of $\mathrm{GL}_2(L)$ rather than as a quotient type.
--
--   The accompanying lemmas are the basic API. [`AutomorphicForm.sigmaConj_one_left`](../def/AutomorphicForm_SigmaConjugacy.html#L22) records that twisting by $g = 1$ leaves $\delta$ unchanged; [`AutomorphicForm.IsSigmaConj.refl`](../def/AutomorphicForm_SigmaConjugacy.html#L26) deduces that every $\delta$ is $\sigma$-conjugate to itself, and [`AutomorphicForm.mem_sigmaConjClassOf_self`](../def/AutomorphicForm_SigmaConjugacy.html#L30) restates this as membership of $\delta$ in its own class. [`AutomorphicForm.mem_sigmaConjClassOf_iff`](../def/AutomorphicForm_SigmaConjugacy.html#L34) unfolds membership in `sigmaConjClassOf σ δ` to the existential statement defining `IsSigmaConj`. Finally, [`AutomorphicForm.sigmaConj_id`](../def/AutomorphicForm_SigmaConjugacy.html#L39) identifies the construction at $\sigma = \mathrm{id}_L$ with ordinary conjugation, $\mathrm{sigmaConj}\,(\mathrm{id}_L)\,g\,\delta = g\,\delta\,g^{-1}$. Symmetry and transitivity of `IsSigmaConj` are left unproved, so the relation is available only as a reflexive binary predicate together with its class-of-an-element form.
--
--   **Relation to Mathlib.** Mathlib supplies the functorial map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(L)$ induced by a ring homomorphism (`Matrix.GeneralLinearGroup.map`), but has no notion of twisted conjugacy; the twisted conjugation operation, the relation and the class are the project's own.
--
--   **Where it is used.** Twisted conjugacy classes are the equivalence along which the geometric side of a twisted trace formula is organised, the twisted orbital integrals being indexed by $\sigma$-conjugacy classes just as ordinary orbital integrals are indexed by conjugacy classes; this is the setting for base-change comparisons for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SigmaConjugacy.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

variable {L : Type*} [Field L]

def sigmaConj (σ : L →+* L) (g δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    Matrix.GeneralLinearGroup (Fin 2) L :=
  g * δ * (Matrix.GeneralLinearGroup.map σ g)⁻¹

def IsSigmaConj (σ : L →+* L) (δ δ' : Matrix.GeneralLinearGroup (Fin 2) L) : Prop :=
  ∃ g, δ' = sigmaConj σ g δ

def sigmaConjClassOf (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    Set (Matrix.GeneralLinearGroup (Fin 2) L) :=
  {δ' | IsSigmaConj σ δ δ'}

theorem sigmaConj_one_left (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    sigmaConj σ 1 δ = δ := by
  simp [sigmaConj]

theorem IsSigmaConj.refl (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    IsSigmaConj σ δ δ :=
  ⟨1, (sigmaConj_one_left σ δ).symm⟩

theorem mem_sigmaConjClassOf_self (σ : L →+* L)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) : δ ∈ sigmaConjClassOf σ δ :=
  IsSigmaConj.refl σ δ

theorem mem_sigmaConjClassOf_iff (σ : L →+* L)
    (δ δ' : Matrix.GeneralLinearGroup (Fin 2) L) :
    δ' ∈ sigmaConjClassOf σ δ ↔ ∃ g, δ' = sigmaConj σ g δ :=
  Iff.rfl

theorem sigmaConj_id (g δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    sigmaConj (RingHom.id L) g δ = g * δ * g⁻¹ := by
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id L) g = g := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  rw [sigmaConj, hmap]

end AutomorphicForm


