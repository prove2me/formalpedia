-- Prove2me | Definitions.Def_SamplingAC0_tensorPow
-- name    : SamplingAC0_tensorPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:40.800692+00:00
-- url     : https://prove2.me/theorems/381c79e6-1a30-4777-8f8b-294f7268b5c8
-- title:
--   Independent copies $D^{\otimes k}$
-- statement:
--   For a distribution $D$ on a finite set $B$ and $k\ge0$, $D^{\otimes k}$ is the distribution of $k$ independent samples of $D$: the distribution on $B^k$ with
--
--   $$D^{\otimes k}(x_1,\dots,x_k)=\prod_{i=1}^k D(x_i).$$
--
--   It is the target of the direct-product theorem (Theorem 1).
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Notation, p.2

import Mathlib
set_option autoImplicit false

namespace SamplingAC0

open scoped BigOperators

/-- **Independent copies `D^{⊗k}`.** Riazanov–Viola, *Sampling Tools and the Power of AC0*,
STOC 2027 submission (manuscript sha256 99c33d30…), Notation, p.2: "For a distribution D we write
D^{⊗k} for k independent samples of D."

`tensorPow D k` is the distribution on `k`-tuples with mass `∏ᵢ D(xᵢ)`. -/
noncomputable def tensorPow {β : Type} [Fintype β] (D : PMF β) (k : ℕ) : PMF (Fin k → β) :=
  PMF.ofFintype (fun x => ∏ i, D (x i)) (by
    classical
    have h1 : ∑ a, D a = 1 := (tsum_fintype (fun a => D a)).symm.trans D.tsum_coe
    have h2 := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset β))
      (fun _ a => D a)
    simp only [h1, Finset.prod_const_one, Fintype.piFinset_univ] at h2
    exact h2.symm)

end SamplingAC0


