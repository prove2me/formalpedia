-- Prove2me | Definitions.Def_LogConcaveLattice_Lift_Lattice
-- name    : LogConcaveLattice_Lift_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:35.716203+00:00
-- url     : https://prove2.me/theorems/cb15025a-f19c-4d5d-a48d-4ae9f6936436
-- title:
--   §§1, 2.3 — lattices, determinants in the span, dual lattices, weak stability, lattice subspaces, projections
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$. A **lattice** is a discrete additive subgroup $\Gamma\subseteq\mathbb R^n$, represented as a $\mathbb Z$-submodule. A **lattice basis** of $\Gamma$ is a family $b_1,\dots,b_k$ of $\mathbb R$-linearly independent vectors with $\Gamma=\operatorname{span}_{\mathbb Z}\{b_1,\dots,b_k\}$; $k$ is the rank.
--
--   1. **Determinant in the span.** For a lattice $\Gamma$ with basis $b_1,\dots,b_k$,
--   $$\det\Gamma=\sqrt{\det\big(\langle b_i,b_j\rangle\big)_{i,j=1}^k},$$
--   the volume of the fundamental parallelepiped measured inside $\operatorname{span}_{\mathbb R}\Gamma$; it does not depend on the basis, equals $|\det(b_1,\dots,b_n)|$ in full rank, and equals $1$ for $\Gamma=\{0\}$ (empty basis).
--   2. **Dual lattice.** $\Gamma^*=\{x\in\operatorname{span}_{\mathbb R}\Gamma:\ \langle x,\gamma\rangle\in\mathbb Z\text{ for every }\gamma\in\Gamma\}$; for a full-rank $\Gamma$ this is $\{x\in\mathbb R^n:\langle x,\gamma\rangle\in\mathbb Z\ \forall\gamma\in\Gamma\}$.
--   3. **Weak stability.** $\Lambda$ is weakly stable if $\det\Gamma\ge1$ for every sublattice (additive subgroup) $\Gamma\subseteq\Lambda$, of every rank.
--   4. **Dilation.** $c\cdot\Lambda=\{c\,x:x\in\Lambda\}$.
--   5. **Lattice subspace.** For a linear subspace $E$, $\Lambda\cap E$ is a sublattice of $\Lambda$, and $E$ is a lattice subspace of $\Lambda$ if $\operatorname{span}_{\mathbb R}(\Lambda\cap E)=E$.
--   6. **Projection.** $\Pi_E\Lambda$ is the image of $\Lambda$ under the orthogonal projection $\Pi_E$ onto $E$, an additive subgroup of $E$ that need not be discrete.
--
--   These are the lattice-geometric objects of Theorem 1.1 and of Lemmas 2.2, 2.3 and 3.4; the determinant in the span is what makes weak stability a condition on sublattices of every rank.
--
--   **Formalization Note** The ambient space is `EuclideanSpace ℝ (Fin n)`. The determinant is defined through a chosen lattice basis and the Gram determinant; a subgroup without a lattice basis (a non-discrete one) gets the value $0$, a case never used. The full-rank determinant used elsewhere in the mission is Mathlib's `ZLattice.covolume`, which agrees with this one in full rank.
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, §1 p. 1 (lattice, basis, determinant, dual), p. 2 (weakly stable), §2.3 p. 7 (sublattice, determinant of a rank-k sublattice, lattice subspace, Π_E Λ, dual of a sublattice)

import Mathlib

open scoped RealInnerProductSpace

namespace LogConcaveLattice.Lift

/-- The ambient space `ℝⁿ` with its Euclidean inner product (§2.1, p. 5). -/
abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- `b` is a lattice basis of `Γ` (§2.3, p. 7): an `ℝ`-linearly independent finite family whose
integer span is `Γ`. -/
def IsLatticeBasis (Γ : Submodule ℤ (V n)) {k : ℕ} (b : Fin k → V n) : Prop :=
  LinearIndependent ℝ b ∧ Submodule.span ℤ (Set.range b) = Γ

open Classical in
/-- **Determinant of a lattice of any rank** (pp. 1, 7: "for a lower-rank lattice, the
determinant is computed in its linear span"): `det Γ = √det(Gram(b₁,…,b_k))` for a lattice basis
`b` of `Γ`; it does not depend on the basis. For `Γ = {0}` the basis is empty and `det Γ = 1`.
A subgroup with no lattice basis (not discrete) gets the value `0`; it is never used. -/
noncomputable def latticeDet (Γ : Submodule ℤ (V n)) : ℝ :=
  if h : ∃ k : ℕ, ∃ b : Fin k → V n, IsLatticeBasis Γ b then
    Real.sqrt (Matrix.det (Matrix.gram ℝ h.choose_spec.choose))
  else 0

/-- **Dual lattice** (p. 1 for full rank, p. 7 for a sublattice): `Γ* = {γ* ∈ span_ℝ Γ :
⟨γ*, γ⟩ ∈ ℤ for every γ ∈ Γ}`. For a full-rank `Γ` the span is all of `ℝⁿ`. -/
def dual (Γ : Submodule ℤ (V n)) : Submodule ℤ (V n) where
  carrier := {x | x ∈ Submodule.span ℝ (Γ : Set (V n)) ∧ ∀ γ ∈ Γ, ∃ m : ℤ, ⟪x, γ⟫ = m}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨Submodule.add_mem _ hx hy, fun γ hγ => ?_⟩
    obtain ⟨a, ha⟩ := hx' γ hγ
    obtain ⟨b, hb⟩ := hy' γ hγ
    exact ⟨a + b, by rw [inner_add_left, ha, hb]; push_cast; ring⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun γ _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨?_, fun γ hγ => ?_⟩
    · rw [← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ hx
    · obtain ⟨a, ha⟩ := hx' γ hγ
      refine ⟨c * a, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, ha]
      push_cast; ring

/-- **Weak stability** (p. 2): `det Γ ≥ 1` for all sublattices `Γ ⊆ Λ` (all ranks; `Γ = {0}` has
determinant `1`). -/
def WeaklyStable (Λ : Submodule ℤ (V n)) : Prop :=
  ∀ Γ : Submodule ℤ (V n), Γ ≤ Λ → 1 ≤ latticeDet Γ

/-- The dilated lattice `c · Λ = {c x : x ∈ Λ}`. -/
def scaleLattice (c : ℝ) (Λ : Submodule ℤ (V n)) : Submodule ℤ (V n) :=
  Λ.map ((c • LinearMap.id : V n →ₗ[ℝ] V n).restrictScalars ℤ)

/-- `Λ ∩ E` for a linear subspace `E`, as a sublattice of `Λ` (p. 7). -/
def interSubspace (Λ : Submodule ℤ (V n)) (E : Submodule ℝ (V n)) : Submodule ℤ (V n) :=
  Λ ⊓ E.restrictScalars ℤ

/-- **Lattice subspace** (p. 7): `E` is a lattice subspace of `Λ` if `span_ℝ (Λ ∩ E) = E`. -/
def IsLatticeSubspace (Λ : Submodule ℤ (V n)) (E : Submodule ℝ (V n)) : Prop :=
  Submodule.span ℝ ((interSubspace Λ E : Submodule ℤ (V n)) : Set (V n)) = E

/-- The projected group `Π_E Λ` (p. 7), the image of `Λ` under the orthogonal projection
`Π_E` onto `E`; an additive subgroup of `E`, possibly not discrete. -/
noncomputable def projLattice (E : Submodule ℝ (V n)) (Λ : Submodule ℤ (V n)) :
    Submodule ℤ (V n) :=
  Λ.map ((E.starProjection : V n →L[ℝ] V n).toLinearMap.restrictScalars ℤ)

end LogConcaveLattice.Lift


