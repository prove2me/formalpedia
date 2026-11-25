-- Prove2me | Definitions.Def_DetDLP_W3_DriverReadback
-- name    : DetDLP_W3_DriverReadback
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:17:46.212055+00:00
-- url     : https://prove2.me/theorems/84a06cab-dfc1-45d9-94c8-01df8c26d7e1
-- title:
--   Scan certificate from a canonical driver exponent
-- statement:
--   For a generator of order M, every canonical exponent returned by a machine is the first exponent selected by the finite range scan. Thus a uniform implementation with a fast small-input branch can furnish the scan certificate directly from its exponent correctness proof.

import Definitions.Def_DetDLP_W3_Driver

set_option autoImplicit false
namespace DetDLP

/-- A machine whose output is any canonical exponent also satisfies the small scan spec;
there is no need to join a separate small machine when the computational proof is uniform. -/
theorem w3_scanOutput_of_exponent {V : Type} [AddCommGroup V] [DecidableEq V]
    {M u : ℕ} {P Q : V} (hg : addOrderOf P = M) (hu : u < M) (he : u • P = Q)
    {accepts : ℕ → Prop} (hr : accepts u) : w3_scanOutput M P Q accepts := by
  have hx (v : ℕ) (hv : v < M) (hvQ : v • P = Q) : v = u := by
    have h := (nsmul_eq_nsmul_iff_modEq).mp (hvQ.trans he.symm)
    change v % addOrderOf P = u % addOrderOf P at h
    simpa [hg,Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt hu] using h
  refine ⟨u,?_,hr⟩
  cases hh : (List.range M).find? (fun v => decide (v • P = Q)) with
  | none =>
    have h := List.find?_eq_none.mp hh u (List.mem_range.mpr hu)
    simp [he] at h
  | some v =>
    have h := List.find?_some hh
    rw [hx v (List.mem_range.mp (List.mem_of_find?_eq_some hh)) (of_decide_eq_true h)]

end DetDLP


