-- Prove2me | Definitions.Def_PPSLattice_LWEHard
-- name    : PPSLattice_LWEHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:36:52.239367+00:00
-- url     : https://prove2.me/theorems/3b115efe-28f9-42fd-8271-e64f6d4dbc23
-- title:
--   The LWE assumption for a family $(n,q(n),\chi(n))$
-- statement:
--   The **LWE assumption** for $(n,q(n),\chi(n))$: for every number of samples $m(n)$ computable in polynomial time (in unary, so polynomial) and every uniform PPT distinguisher $D$, which receives $1^n$ and the pair $(\mathbf A,\mathbf b)$,
--   $$\Bigl|\Pr\bigl[D(1^n,\mathbf A,\mathbf s^\top\mathbf A+\mathbf e^\top)=1\bigr]-\Pr\bigl[D(1^n,\mathbf A,\mathbf c^\top)=1\bigr]\Bigr|$$
--   is negligible in $n$.
--
--   **Formalization Note** The ensemble is indexed by the dimension $n$, the security parameter of the assumption; "$m\in\mathbb N$" is read as every polynomial number of samples. Distinguishers are uniform reactive machines (`RestrictedDec.Adversary`), activated once; the first bit of the move is the output. `Negligible` is `NoisyOWMPC.Negligible`, whose sign clause holds for absolute values.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17; §3, p.15

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_PPSLattice_lweSample
import Definitions.Def_PPSLattice_encMat
import Definitions.Def_PPSLattice_PolyTimeOn
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The probability that the distinguisher `D` outputs `1` on LWE samples of dimension `n`
(`real = true`) or on uniform samples (`real = false`): `D` is activated once, on security
parameter `n` (so it reads `1^n`), with input `(A, b)` written as `tup [code of A, code of b]`;
its output bit is the first bit of its move. -/
noncomputable def lweDistProb (q χ m : ℕ → ℕ) (D : RestrictedDec.Adversary) (n : ℕ)
    (real : Bool) : ℝ :=
  (((lweSample (q n) n (m n) (χ n) real).bind fun ab =>
      (D.activate n [] (BeyondDS.tup [encMat (q n) ab.1, encVec (q n) ab.2])).map
        fun r => r.2.headD false) true).toReal

/-- The **LWE assumption** for the family `(n, q(n), χ(n))`: for every number of samples `m(n)`
computable in polynomial time (in unary, hence polynomial) and every uniform PPT distinguisher `D`,
the distinguishing advantage `|Pr[D(A, s^⊤A + e^⊤) = 1] − Pr[D(A, c^⊤) = 1]|` is negligible in `n`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17; computational indistinguishability ≈c, §3, p.15.

**Formalization Note.** The ensemble is indexed by the dimension `n`, which plays the role of the
security parameter of the assumption; "m ∈ N" is read as every polynomial number of samples.
Distinguishers are the uniform reactive machines of `RestrictedDec.Adversary` (polynomial-time step
function, polynomially many coins). `Negligible` is `NoisyOWMPC.Negligible`, whose sign clause holds
for absolute values. -/
def LWEHard (q χ : ℕ → ℕ) : Prop :=
  ∀ m : ℕ → ℕ, PolyTimeOn (fun n : ℕ => encNat n) (fun n => encNat (m n)) →
    ∀ D : RestrictedDec.Adversary, D.Valid →
      NoisyOWMPC.Negligible fun n => |lweDistProb q χ m D n true - lweDistProb q χ m D n false|

end PPSLattice


