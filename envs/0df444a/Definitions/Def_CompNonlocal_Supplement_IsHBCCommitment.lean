-- Prove2me | Definitions.Def_CompNonlocal_Supplement_IsHBCCommitment
-- name    : CompNonlocal_Supplement_IsHBCCommitment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:03:34.191651+00:00
-- url     : https://prove2.me/theorems/fe7548a5-7a51-46a9-9f2a-dfc6e9f8621b
-- title:
--   Statistically sum-binding QCCC commitments with computational HBC hiding (Definition 6)
-- statement:
--   A QCCC commitment scheme is **statistically sum-binding with computational honest-but-curious (HBC) hiding** if:
--
--   1. the committer, receiver, $\mathrm{Open}$ and $\mathrm{Ver}$ are uniform quantum polynomial-time, and the number of rounds is polynomially bounded and polynomial-time computable;
--   2. **Correctness:** for each $b\in\{0,1\}$, the honest opening of an honest commitment to $b$ is accepted with probability at least $1-\mathrm{negl}(\kappa)$;
--   3. **Computational HBC hiding:** let $\omega^b_{\mathrm{view}}$ be the receiver's full view (the transcript $T$ and its register $R$) after an honest commit phase for $b$. For every polynomial-size quantum distinguisher $A$ with classical advice,
--   $$\big|\Pr[A_\kappa(\omega^0_{\mathrm{view}})=1]-\Pr[A_\kappa(\omega^1_{\mathrm{view}})=1]\big|\le\mathrm{negl}(\kappa);$$
--   4. **Statistical sum binding:** there is one negligible function $\epsilon_{\mathrm{bind}}$ such that for every unbounded quantum committer $A^*$ interacting with the honest receiver, and every two unbounded openers $O^*_0,O^*_1$ acting on the same post-commit state, the probabilities $p_b=\Pr[\mathrm{Ver}(1^\kappa,T,R,b,d)=1\mid d\leftarrow O^*_b(1^\kappa,T,C)]$ satisfy
--   $$p_0+p_1\le1+\epsilon_{\mathrm{bind}}(\kappa).$$
--
--   This is the conclusion of Theorem 8.
--
--   **Formalization Note** Messages are classical, so given the transcript the registers $C$ and $R$ are in a product state and every probability is a finite sum over transcripts. An unbounded opener is, for each transcript, a POVM on the committer's memory with outcomes in $\{0,1\}^L$ for any $L$. The binding bound $\epsilon_{\mathrm{bind}}$ is chosen before the strategies.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Definition 6, pp.22–23

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_Commitment
import Definitions.Def_CompNonlocal_Supplement_CheatCommitter
import Definitions.Def_CompNonlocal_Uniform
import Definitions.Def_CompNonlocal_PolySize
import Definitions.Def_CompNonlocal_Negligible

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity
open scoped ComplexOrder

/-- Statistically sum-binding QCCC commitments with computational honest-but-curious hiding.
Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 6, pp.22–23:

1. the committer, the receiver, Open and Ver are QPT (uniform), and the commit phase has a
   polynomially bounded, polynomial-time computable number of rounds;
2. "Correctness: For each b ∈ {0, 1}, Pr[Ver(1^κ, T, R, b, d) = 1 | (T, C, R) ← Com(1^κ, b),
   d ← Open(1^κ, b, T, C)] ≥ 1 − negl(κ)";
3. "Computational HBC hiding: Let ω^b_view be the state of the receiver's full view at the end of
   an honest commit phase for bit b, before opening. For every polynomial-size quantum
   distinguisher A with classical advice, |Pr[A_κ(ω^0_view) = 1] − Pr[A_κ(ω^1_view) = 1]| ≤ negl(κ)";
4. "Statistical sum binding: Fix any computationally unbounded quantum committer A∗ interacting
   with the honest receiver during the commit phase, and let ω_TCR be the resulting joint state. For
   any two computationally unbounded opening algorithms O∗_0, O∗_1, define
   p_b := Pr[Ver(1^κ, T, R, b, d) = 1 | d ← O∗_b(1^κ, T, C)], b ∈ {0, 1}, where each experiment starts
   with the same post-commit state ω_TCR. There is a negligible function ϵ_bind, independent of these
   strategies, such that p_0 + p_1 ≤ 1 + ϵ_bind(κ)."

**Formalization Note** Messages are classical, so conditioned on the transcript `T` the joint state
of `(C, R)` is the product of the two unnormalized registers (`comMem`/`mem` and `recMem`), and every
probability below is a sum over the finitely many transcripts of the product of a committer-side
and a receiver-side trace. The receiver's view is `(T, R)`; the distinguisher reads `T` classically
and `R` on its quantum input and outputs its first bit. An unbounded opener `O∗_b` is, for each
transcript, a POVM on the committer's memory with outcomes `d ∈ {0,1}^L` (any `L`; Ver reads a finite
prefix of `d`, so this covers every opening string); any post-commit processing of the memory is
absorbed into it. In 4 one negligible `ϵ_bind` is chosen before `κ`, the committer and both openers;
in 2 one bound serves both bits; in 3 the bound is chosen after the distinguisher. -/
def IsHBCCommitment (P : Commitment) : Prop :=
  Uniform P.Com ∧ Uniform P.Rec ∧ Uniform P.Open ∧ Uniform P.Ver ∧
    (∃ p : Polynomial ℕ, ∀ κ, P.R κ ≤ p.eval κ) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ κ, g (unary κ) = unary (P.R κ)) ∧
    -- correctness
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ (κ : ℕ) (b : Bool),
      1 - μ κ ≤ ∑ t : P.Trans κ, ∑ d : Bits (P.Open κ).outC.length,
        (P.openEff κ b (Commitment.tl t) (List.ofFn d) * P.comMem κ b (Commitment.tl t)).trace.re *
          (P.verEff κ b (Commitment.tl t) (List.ofFn d) * P.recMem κ (Commitment.tl t)).trace.re) ∧
    -- computational honest-but-curious hiding
    (∀ A : Family, PolySize A → ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ : ℕ,
      |(∑ t : P.Trans κ, (P.comMem κ false (Commitment.tl t)).trace.re *
          ((A κ).effectOn (P.Rec κ).outQ.length (Commitment.tl t).flatten (fun o => o.headD false) *
            P.recMem κ (Commitment.tl t)).trace.re) -
        (∑ t : P.Trans κ, (P.comMem κ true (Commitment.tl t)).trace.re *
          ((A κ).effectOn (P.Rec κ).outQ.length (Commitment.tl t).flatten (fun o => o.headD false) *
            P.recMem κ (Commitment.tl t)).trace.re)| ≤ μ κ) ∧
    -- statistical sum binding
    (∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ (κ D nK : ℕ) (A : CheatCommitter D nK),
      A.IsValid (P.Com κ).outC.length →
      ∀ (L : ℕ) (O : Bool → List Str → Bits L → Matrix (Fin D) (Fin D) ℂ),
        (∀ b T d, (O b T d).PosSemidef) → (∀ b T, ∑ d : Bits L, O b T d = 1) →
        (∑ b : Bool, ∑ t : P.Trans κ, ∑ d : Bits L,
          (O b (Commitment.tl t) d * A.mem (Commitment.tl t) (P.R κ)).trace.re *
            (P.verEff κ b (Commitment.tl t) (List.ofFn d) * P.recMem κ (Commitment.tl t)).trace.re)
          ≤ 1 + ε κ)

end CompNonlocal.Supplement


