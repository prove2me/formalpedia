-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_orthSuccProb
-- name    : AvgCaseTI_Supplement_orthSuccProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:31:57.139962+00:00
-- url     : https://prove2.me/theorems/9f5fb261-f09b-43f3-80a2-a8e77f2979c7
-- title:
--   Success probability $\Pr_{A,\omega}$ of a randomized orthogonal-isomorphism machine
-- statement:
--   Let $M$ be a Turing machine, $k$ a degree, $\mathbb F_q$ a presented finite field, $n\ge1$, and $B(\cdot)$ any map from $n\times n\times n$ arrays to $n\times n\times n$ arrays. A run of $M$ on the instance $(\mathbb F_q,n,A,B(A))$ with coin string $\omega\in\{0,1\}^{(L+2)^k}$ **returns a correct answer** if within $(L+2)^k$ steps it outputs a correct answer (the complete list of orthogonal isomorphisms, not “Fail”).
--
--   The success probability is
--   $$
--   \Pr_{A,\omega}[\text{correct}]=\frac1{q^{n^3}}\sum_{A}\frac{\#\{\omega:\text{the run on }(A,B(A))\text{ with coins }\omega\text{ returns a correct answer}\}}{2^{(L_A+2)^k}},
--   $$
--   the probability over a uniform first array $A$ and an independent uniform coin string $\omega$, where $L_A$ is the code length of $(\mathbb F_q,n,A,B(A))$. The second array $B(A)$ depends on $A$ only, not on the coins.
--
--   **Formalization Note** The coin length depends on the instance, so the joint probability is written as the average over $A$ of the fraction of good coin strings. The module also proves that a presented field is finite.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 5.6, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_AvgCaseTI_Halts
import Definitions.Def_AvgCaseTI_Supplement_OrthCorrectOut

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

/-- A presented field is finite (a finite-dimensional vector space over `ZMod p`). -/
theorem finite_F (P : FieldPres) : Finite P.F := by
  have hf : P.f ≠ 0 := P.hmonic.ne_zero
  have : Module.Finite (ZMod P.p) P.F := (AdjoinRoot.powerBasis hf).finite
  exact Module.finite_of_finite (ZMod P.p)

/-- A run of `M` on instance `x` with coin string `r` **returns a correct answer** of orthogonal tensor
isomorphism: within `(L+2)^k` steps it outputs a correct answer (`OrthCorrectOut`), not "Fail". -/
def RunCorrect (M : Turing.TM2ComputableAux Bool Bool) (k : ℕ) (x : AlgIsoInstance)
    (r : Fin (timeBound k x) → Bool) : Prop :=
  ∃ out : List Bool, HMBinPacking.OutputsWithin M (encodeInstance x ++ List.ofFn r) out (timeBound k x) ∧
    OrthCorrectOut x.P x.A x.B out

/-- **`Pr_{A,ω}[A_s(A, B(A); ω) returns a correct answer]`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 5.6, p.34 (PDF p.36): "For A uniform and any choice B = B(A) independent of the
internal randomness ω, Pr_{A,ω}[A_s(A, B; ω) returns a correct answer]".

`orthSuccProb M k P n Bf` is the probability, for `A` uniform among the `q^{n³}` arrays over `P.F` and
`ω` a uniform coin string of the length `(L+2)^k` of the instance `(P, n, A, Bf A)`, that the run of `M`
on `(P, n, A, Bf A)` with coins `ω` returns a correct answer:
`(1/q^{n³}) Σ_A |{ω : correct}| / 2^{(L+2)^k}`.

**Formalization Note.** The second tensor `Bf A` is any function of `A` alone, fixed before the coins. The
coin length depends on the instance through its code length, so the joint probability is the
average over `A` of the per-instance fraction of coin strings. -/
noncomputable def orthSuccProb (M : Turing.TM2ComputableAux Bool Bool) (k : ℕ) (P : FieldPres) (n : ℕ)
    (Bf : Tensor3 P.F n → Tensor3 P.F n) : ℝ :=
  haveI : Finite P.F := finite_F P
  haveI : Fintype (Tensor3 P.F n) := Fintype.ofFinite _
  (∑ A : Tensor3 P.F n,
      (Nat.card {r : Fin (timeBound k ⟨P, n, A, Bf A⟩) → Bool // RunCorrect M k ⟨P, n, A, Bf A⟩ r} : ℝ) /
        (2 : ℝ) ^ timeBound k ⟨P, n, A, Bf A⟩) /
    (Nat.card (Tensor3 P.F n) : ℝ)

end AvgCaseTI.Supplement


