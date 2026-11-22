-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:19.594853+00:00
-- url     : https://prove2.me/theorems/0b306a1e-d95a-499a-a022-858ea512584b
-- title:
--   Prod Factorial Support Sub Single
-- statement:
--   Definitions and structural lemmas for Prod Factorial Support Sub Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
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
namespace Formalism.REAL
section general
variable {σ : Type*}
lemma fischerInner_eq_sum_of_subset (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockF f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset h
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.mp hm]
lemma fischerInner_add_left (f1 f2 g : MvPolynomial σ ℂ) :
    fockF (f1 + f2) g = fockF f1 g + fockF f2 g := by
  classical
  rw [fischerInner_eq_sum_of_subset _ _ (f1.support ∪ f2.support) MvPolynomial.support_add,
    fischerInner_eq_sum_of_subset f1 g (f1.support ∪ f2.support) Finset.subset_union_left,
    fischerInner_eq_sum_of_subset f2 g (f1.support ∪ f2.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_add]; ring
lemma fischerInner_add_right (f g1 g2 : MvPolynomial σ ℂ) :
    fockF f (g1 + g2) = fockF f g1 + fockF f g2 := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_add, star_add]; ring
def fischerInnerLeftHom (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →+ ℂ :=
  AddMonoidHom.mk' (fun f => fockF f g) (fun a b => fischerInner_add_left a b g)
def fischerInnerRightHom (f : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →+ ℂ :=
  AddMonoidHom.mk' (fun g => fockF f g) (fun a b => fischerInner_add_right f a b)
end general
variable {M n' : ℕ}
end Formalism.REAL


