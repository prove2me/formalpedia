-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:28.74178+00:00
-- url     : https://prove2.me/theorems/f0716c83-1f73-4927-98a0-ede2310575c5
-- title:
--   LHwline Lemmas
-- statement:
--   Definitions and structural lemmas for LHwline Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
section LHwline
variable {K : Type*} [Field K] {r n : ℕ}
def lhwline_rowOp (a b : Fin r) (t : K) (x : Fin r × Fin n → K) : Fin r × Fin n → K :=
  fun v => if v.1 = b then x v + t * x (a, v.2) else x v
def lhwline_colOp (l j : Fin n) (c : K) (x : Fin r × Fin n → K) : Fin r × Fin n → K :=
  fun v => if v.2 = j then x v + c * x (v.1, l) else x v
def lhwline_RInv (φ : (Fin r × Fin n → K) → K) : Prop :=
  ∀ (x : Fin r × Fin n → K) (a b : Fin r) (t : K), a < b → φ (lhwline_rowOp a b t x) = φ x
def lhwline_CInv (φ : (Fin r × Fin n → K) → K) : Prop :=
  ∀ (x : Fin r × Fin n → K) (l j : Fin n) (c : K), l < j → φ (lhwline_colOp l j c x) = φ x
end LHwline
section LHwlineElim
variable {K : Type*} [Field K] {r n : ℕ}
def lhwline_mrow (p : Fin r) (S : Finset (Fin r)) (t : Fin r → K) (x : Fin r × Fin n → K) :
    Fin r × Fin n → K :=
  fun v => if v.1 ∈ S then x v + t v.1 * x (p, v.2) else x v
def lhwline_mcol (q : Fin n) (S : Finset (Fin n)) (c : Fin n → K) (x : Fin r × Fin n → K) :
    Fin r × Fin n → K :=
  fun v => if v.2 ∈ S then x v + c v.2 * x (v.1, q) else x v
def highestWeightLineUpdate (p : Fin r) (q : Fin n) (x : Fin r × Fin n → K) : Fin r × Fin n → K :=
  let y := lhwline_mrow p (Finset.univ.filter fun b => p < b) (fun b => -(x (b, q) / x (p, q))) x
  lhwline_mcol q (Finset.univ.filter fun j => q < j) (fun j => -(y (p, j) / y (p, q))) y
def lhwline_elim : ℕ → (Fin r × Fin n → K) → (Fin r × Fin n → K)
  | 0, x => x
  | k + 1, x =>
    if h : k < r ∧ k < n then highestWeightLineUpdate ⟨k, h.1⟩ ⟨k, h.2⟩ (lhwline_elim k x)
    else lhwline_elim k x
def lhwline_cleared (k : ℕ) (x : Fin r × Fin n → K) : Prop :=
  ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → (a.val < k ∨ j.val < k) → x (a, j) = 0
end LHwlineElim
section LHwlineClear
variable {K : Type} [Field K] {r n : ℕ}
end LHwlineClear
section LHwlineVanish
variable {K : Type} [Field K] {r n : ℕ}
def lhwline_mnu (hn : n ≤ r) (ν : Fin n → ℕ) : Fin r × Fin n →₀ ℕ :=
  ∑ j : Fin n, Finsupp.single (Fin.castLE hn j, j) (ν j)
end LHwlineVanish
end Formalism.GradedWeylDivisibility


