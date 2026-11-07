-- Prove2me | Definitions.Def_CompNonlocal_IsKA
-- name    : CompNonlocal_IsKA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:17.475197+00:00
-- url     : https://prove2.me/theorems/233bd364-6f57-4ee1-9d16-f87730019e5c
-- title:
--   Sender-first two-message QCCC key agreement
-- statement:
--   A sender-first two-message protocol is a **key agreement** if its parties are uniform QPT, the keys $K_R,K_S\in\{0,1\}^\kappa$ satisfy $\Pr[K_S\ne K_R]\le\mathsf{negl}(\kappa)$, and for every polynomial-size distinguisher $\mathcal A$,
--   $$\big|\Pr[\mathcal A_\kappa(T,K_S)=1]-\Pr[\mathcal A_\kappa(T,K_1)=1]\big|\le\mathsf{negl}(\kappa),$$
--   with $T$ the complete transcript and $K_1$ uniform and independent.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 4, pp.20–21

import Mathlib
import Definitions.Def_CompNonlocal_TwoMsg
import Definitions.Def_CompNonlocal_Uniform
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_CompNonlocal_fit

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- Sender-first two-message QCCC key agreement. Głuch, Morimae, *From Computational Nonlocality
to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…),
Definition 4, pp.20–21: the parties are QPT, output classical keys `K_S, K_R ∈ {0,1}^κ`, and

1. "Correctness: In an honest execution, Pr[K_S ≠ K_R] ≤ negl(κ)";
2. "Security: For every polynomial-size quantum distinguisher family A with classical advice,
   define, for b ∈ {0, 1}, p_b := Pr[A_κ(T, K_b) = 1 | (T, K_S, K_R) ← ⟨KA.Sen, KA.Rec⟩(1^κ),
   K_0 := K_S, K_1 ← {0,1}^κ]. We require |p_0 − p_1| ≤ negl(κ)", with `T` "the complete public
   transcript".

**Formalization Note** The keys are `K_R = fit κ out_R` and `K_S = fit κ out_S`; the transcript is
`T = msg_S ++ msg_R`; the distinguisher reads `T ++ K` and outputs its first bit. The negligible
bound is chosen after the distinguisher. -/
def IsKA (P : TwoMsg) : Prop :=
  Uniform P.Sen1 ∧ Uniform P.Rec ∧ Uniform P.Sen2 ∧
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ,
      P.expect κ (fun _ _ oR oS => if fit κ oR = fit κ oS then 0 else 1) ≤ μ κ) ∧
    (∀ D : Family, PolySize D → ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ,
      |P.expect κ (fun mS mR _ oS =>
          ((D κ).effectOn 0 (mS ++ mR ++ fit κ oS) (fun t => t.headD false)).trace.re) -
        P.expect κ (fun mS mR _ _ =>
          (1 / 2 ^ κ : ℝ) * ∑ k : Bits κ,
            ((D κ).effectOn 0 (mS ++ mR ++ List.ofFn k) (fun t => t.headD false)).trace.re)| ≤ μ κ)

end CompNonlocal


