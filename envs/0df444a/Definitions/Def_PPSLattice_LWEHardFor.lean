-- Prove2me | Definitions.Def_PPSLattice_LWEHardFor
-- name    : PPSLattice_LWEHardFor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:37:09.574903+00:00
-- url     : https://prove2.me/theorems/5a3cab13-d9ff-44c6-bdf5-8aeaa9f3a4d7
-- title:
--   The LWE assumption for the parameters of Construction 4.6
-- statement:
--   For parameters $P$: for every polynomial-time computable number of samples $m'(\lambda,N)$ and every uniform PPT distinguisher $D$ that first chooses $N\ge1$ and then receives $(\mathbf A,\mathbf b)$ with dimension $n(\lambda,N)$, modulus $q(\lambda,N)$ and width $\chi(\lambda,N)$, the advantage $|\Pr[D=1\mid\mathbf b^\top=\mathbf s^\top\mathbf A+\mathbf e^\top]-\Pr[D=1\mid\mathbf b\text{ uniform}]|$ is negligible in $\lambda$.
--
--   **Formalization Note** The reductions of Lemmas 4.19 and 4.28 learn $N$ from the PPS adversary before using their LWE challenge, so the assumption is stated with $N$ chosen first.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17; Theorems 4.13, 4.26; Lemmas 4.19, 4.28

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_PPSLattice_Params
import Definitions.Def_PPSLattice_lweSample
import Definitions.Def_PPSLattice_encMat
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_PolyTimeOn
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The probability that `D` outputs `1` in the LWE experiment for the parameters `P` with `m′(λ, N)`
samples: `D`'s first move `tup [N]` (binary) chooses `N ≥ 1` (otherwise the output is `0`); then `D` receives
`(A, b)` drawn by `lweSample` with dimension `n(λ, N)`, modulus `q(λ, N)`, width `χ(λ, N)`, and its next move's
first bit is the output. -/
noncomputable def lweForProb (P : Params) (m' : ℕ → ℕ → ℕ) (D : RestrictedDec.Adversary)
    (lam : ℕ) (real : Bool) : ℝ :=
  (((D.activate lam [] (BeyondDS.tup [])).bind fun r0 =>
      let N := decBin ((BeyondDS.untup r0.2).getD 0 [])
      if 1 ≤ N then
        (lweSample (P.q lam N) (P.n lam N) (m' lam N) (P.chi lam N) real).bind fun ab =>
          (D.activate lam r0.1
              (BeyondDS.tup [encMat (P.q lam N) ab.1, encVec (P.q lam N) ab.2])).map
            fun r => r.2.headD false
      else PMF.pure false) true).toReal

/-- The **LWE assumption for the parameters of Construction 4.6**, as Theorems 4.13 and 4.26 use it: for
every polynomial-time computable sample count `m′(λ, N)` and every uniform PPT distinguisher `D` that first
chooses `N`, the advantage `|Pr[D = 1 | b = s^⊤A + e^⊤] − Pr[D = 1 | b uniform]|` is negligible in `λ`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17; Theorems 4.13, p.24 and 4.26, p.30 ("LWE assumption holds (Assumption 3.4)");
Lemma 4.19, p.28 ("B receives (N, i*) from A and an LWE challenge (M, w^⊤) where M ∈ Z_q^{n×(⌈log N⌉·m)}");
Lemma 4.28, p.30 ("⌈log N⌉ · m + λ samples").

**Formalization Note.** The parameters depend on `N`, which the adversary of the PPS game chooses, so the
reductions of Lemmas 4.19 and 4.28 choose `N` before receiving the LWE challenge; the assumption is stated
in that form, indexed by `λ`. -/
def LWEHardFor (P : Params) : Prop :=
  ∀ m' : ℕ → ℕ → ℕ,
    PolyTimeOn (fun a : ℕ × ℕ => BeyondDS.tup [encNat a.1, encBin a.2])
      (fun a => encNat (m' a.1 a.2)) →
    ∀ D : RestrictedDec.Adversary, D.Valid →
      NoisyOWMPC.Negligible fun lam => |lweForProb P m' D lam true - lweForProb P m' D lam false|

end PPSLattice


