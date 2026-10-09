-- Prove2me | Definitions.Def_OAIErdos3B123
-- name    : OAIErdos3B123
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T07:04:09.673802+00:00
-- url     : https://prove2.me/theorems/9aceff7a-02ab-4cf4-8995-42d1d92ac0d7
-- title:
--   OpenAI Erdős-3 split, definitions bundle 124 of 132
-- statement:
--   Definitions bundle 124 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B122`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 124 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_frequency_quotient`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_frequency_quotient_budget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B042

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledFrequencyExternalTransfer
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_frequency_quotient
    {L J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
    (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    (vP : Fin d → L) (hspan : Submodule.span ℚ (Set.range vP) = P)
    (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hr : (r : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) :
    let K := frequencyCodeKernel P eta code
    let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
    let I := D.filtration.topSubspaceIdeal K hK
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    let q := p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1
    ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
      Q.filtration = D.filtration.quotientLie I hI ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
      Q.GeometryComplexityLE ((q + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (q + 3) ^ 5 := by
  intro K hK I hI q
  obtain ⟨n, hn, bk, hbk⟩ := exists_frequency_code_kernel_basis_logHeight D.basis P vP hspan
    eta code hp hD.1 hr hvP heta
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have : 0 ≤ ((2 * p + 6) ^ 2 + 2) ^ 63 := by positivity
    dsimp [q]
    exact (le_add_of_nonneg_right this).trans (le_add_of_nonneg_right zero_le_one)
  have hbq : ((2 * p + 6) ^ 2 + 2) ^ 63 ≤ q := by dsimp [q]; linarith
  exact D.exists_controlled_top_subspace_quotient hs K hK bk bk.span_eq hq
    (hD.mono D hpq) (fun i j => (hbk i j).trans hbq)

theorem exists_controlled_frequency_quotient_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
      (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
      (vP : Fin d → L), Submodule.span ℚ (Set.range vP) = P →
      ∀ (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (r : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ p) →
      (∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) →
      let K := frequencyCodeKernel P eta code
      let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
      let I := D.filtration.topSubspaceIdeal K hK
      let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by
        rw [D.filtration.terminal]; exact bot_le
      ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        Q.filtration = D.filtration.quotientLie I hI ∧
        Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
        Q.GeometryComplexityLE ((p + 2) ^ C) ∧
        ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 2) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let q := X + ((2 * X + 6) ^ 2 + 2) ^ 63 + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((q + 3) ^ 11 + (q + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro L J _ _ s d r D hs P hP vP hspan eta code p hp hD hr hvP heta K hK I hI
  obtain ⟨n, hn, Q, hQF, hQL, hQ, he⟩ :=
    D.exists_controlled_frequency_quotient hs P hP vP hspan eta code hp hD hr hvP heta
  have hb : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 +
      (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 ≤ (p + 2) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hb11 : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 ≤ (p + 2) ^ C := by
    have : 0 ≤ (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 := by positivity
    exact (le_add_of_nonneg_right this).trans hb
  have hb5 : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 ≤ (p + 2) ^ C := by
    have : 0 ≤ (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 := by positivity
    exact (le_add_of_nonneg_left this).trans hb
  exact ⟨n, hn, Q, hQF, hQL, hQ.mono Q hb11, fun i j => (he i j).trans hb5⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal BigOperators Classical

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal BigOperators Classical

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


