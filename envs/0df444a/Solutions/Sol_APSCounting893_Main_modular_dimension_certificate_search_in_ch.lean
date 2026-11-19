-- Prove2me | solution 1 for APSCounting893.Main.modular_dimension_certificate_search_in_ch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:41:19.420558+00:00
-- url     : https://prove2.me/submissions/bfaff873-db4d-4d9e-8b94-24141754f3fe

import Theorems.Thm_APSCounting893_Main_modular_jacobian_threshold_language_in_ch
import Theorems.Thm_APSCounting893_Main_bounded_threshold_search_with_oracle
import Theorems.Thm_APSCounting893_Main_bounded_modular_dimension_certificates
set_option autoImplicit false
open APSCounting893.Main
theorem solution :
    ∃ (A : APSCounting893.Main.Language) (f : APSCounting893.Main.Word → APSCounting893.Main.Word),
      APSCounting893.Main.InCountingHierarchy A ∧ APSCounting893.Main.FunctionInPWithOracle A f ∧
      ∀ (n : ℕ) (C : APSCounting893.Main.ArithmeticCircuit n), APSCounting893.Main.ValidCircuit .rational C →
        ∃ r : ℕ,f C.encode=APSCounting893.Main.encodeNat r ∧
          ∀ k : ℕ,k≤r ↔ APSCounting893.Main.ModularJacobianCertificate C k  := by
  obtain ⟨A,hA,hthreshold⟩:=modular_jacobian_threshold_language_in_ch
  obtain ⟨f,hf,hsearch⟩:=bounded_threshold_search_with_oracle A
  refine ⟨A,f,hA,hf,?_⟩
  intro n C hvalid
  obtain ⟨r,hr,hrank⟩:=bounded_modular_dimension_certificates C hvalid
  have hrm : r≤C.outputs.length := by
    obtain ⟨o,v,ho,hv,hw⟩:=(hrank r).mp (le_refl r)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective o ho
  have hml : C.outputs.length≤C.encode.length := by
    have hh : C.outputs.length≤(C.outputs.flatMap encodeNat).length := by
      induction C.outputs with
      | nil => rfl
      | cons j js ih =>
        have hp : 0<(encodeNat j).length := by simp [encodeNat]
        simp only [List.length_cons,List.flatMap_cons,List.length_append]
        omega
    simp only [ArithmeticCircuit.encode,encodeList,List.length_append]
    omega
  refine ⟨r,?_,hrank⟩
  apply hsearch C.encode r (hrm.trans hml)
  intro k hk
  exact (hthreshold n C hvalid k).trans (hrank k).symm
