-- Prove2me | solution 1 for APSCounting893.Main.image_dimension_in_ch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:47:45.63133+00:00
-- url     : https://prove2.me/submissions/27f44252-220c-41d3-89a0-0755dbacdfe5

import Theorems.Thm_APSCounting893_Main_bounded_modular_dimension_certificates
import Theorems.Thm_APSCounting893_Main_modular_dimension_certificate_search_in_ch
set_option autoImplicit false
namespace APSCounting893.Main
end APSCounting893.Main

theorem solution :
    ∃ (A : APSCounting893.Main.Language) (f : APSCounting893.Main.Word → APSCounting893.Main.Word),
      APSCounting893.Main.InCountingHierarchy A ∧ APSCounting893.Main.FunctionInPWithOracle A f ∧
      ∀ (n : ℕ) (C : APSCounting893.Main.ArithmeticCircuit n), APSCounting893.Main.ValidCircuit .rational C →
        ∃ r : ℕ,
          RSCapacity.algDim (APSCounting893.Main.imageClosure (APSCounting893.Main.rationalComplexPolynomials C))=
            ((r : ℕ∞) : WithBot ℕ∞) ∧ f C.encode=APSCounting893.Main.encodeNat r := by
  obtain ⟨A,f,hA,hf,hsearch⟩:=APSCounting893.Main.modular_dimension_certificate_search_in_ch
  refine ⟨A,f,hA,hf,?_⟩
  intro n C hvalid
  obtain ⟨r,hfr,hr⟩:=hsearch n C hvalid
  obtain ⟨s,hs,hcert⟩:=APSCounting893.Main.bounded_modular_dimension_certificates C hvalid
  have hrs : r=s := Nat.le_antisymm
    ((hcert r).mpr ((hr r).mp le_rfl)) ((hr s).mpr ((hcert s).mp le_rfl))
  subst s
  exact ⟨r,hs,hfr⟩
