-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.exists_perm_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:02.877052+00:00
-- url     : https://prove2.me/submissions/f3b78f27-6b8c-422a-a22f-64215903c1f3

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Theorems.Thm_AaronsonAmbainis_DetBij_Qmat_prod_eq
import Theorems.Thm_AaronsonAmbainis_DetBij_coeff_units_smul_ne_zero

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) (m : ι →₀ ℕ)
    (hm : m ∈ (Qmat g A).det.support) :
    ∃ σ : Equiv.Perm (Ones g), (∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)) ∧
      m = ∑ x : Ones g, agExp (σ x).1 x.1 := by
  rw [MvPolynomial.mem_support_iff, Matrix.det_apply, MvPolynomial.coeff_sum] at hm
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hσ' := coeff_units_smul_ne_zero m _ _ hσ
  rw [Qmat_prod_eq] at hσ'
  refine ⟨σ, ?_⟩
  by_cases h : ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)
  · refine ⟨h, ?_⟩
    rw [if_pos h, MvPolynomial.coeff_monomial] at hσ'
    by_contra hne
    rw [if_neg (fun h' => hne h'.symm)] at hσ'
    exact hσ' rfl
  · rw [if_neg h, MvPolynomial.coeff_zero] at hσ'
    exact absurd rfl hσ'
end AaronsonAmbainis.DetBij
