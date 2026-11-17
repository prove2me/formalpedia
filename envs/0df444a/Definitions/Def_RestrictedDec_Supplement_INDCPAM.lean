-- Prove2me | Definitions.Def_RestrictedDec_Supplement_INDCPAM
-- name    : RestrictedDec_Supplement_INDCPAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:23:25.560194+00:00
-- url     : https://prove2.me/theorems/37c7164a-ddb7-4ecc-a327-5a708080f532
-- title:
--   IND-CPA security over $M$ (Definition 2)
-- statement:
--   In the experiment $\mathrm{Exp}^{\mathrm{cpa},b}_E(A,\lambda)$, keys are generated, $A$ receives $pk$, chooses valid equal-length $(m_0,m_1)$ and receives $c^*\leftarrow\mathrm{Enc}_{pk}(m_b)$; the output is its final bit. The advantage is
--   $$\mathrm{Adv}^{\mathrm{cpa}}_E(A,\lambda)=\big|\Pr[\mathrm{Exp}^{\mathrm{cpa},1}_E(A,\lambda)=1]-\Pr[\mathrm{Exp}^{\mathrm{cpa},0}_E(A,\lambda)=1]\big|,$$
--   and $E$ is **IND-CPA secure** over $M$ if this advantage is negligible for every uniform PPT adversary. There is no correctness clause.
--
--   This is the security assumption on the residual scheme $R$ and the label scheme $L$ of the compilers.
--
--   **Formalization Note** For $M_\lambda=\{0,1\}^{n(\lambda)}$ this is the published `RestrictedDec.INDCPA` (proved in the sanity file).
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 2, App. A.1, p.29

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Supplement_runGameM
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- The experiment `Exp^{cpa,b}_E(A, λ)` over the message space `M` (Definition 2): keys
`(pk, sk) ← KeyGen(1^λ)`, the adversary gets `pk`, chooses valid equal-length `(m₀, m₁)`, receives
`c* ← Enc_pk(m_b)`, and the output is its final bit `b′`. There is no oracle.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 2, App. A.1, p.29.

**Formalization Note.** The interaction is `runGameM` with an oracle that never answers, so a
"query" move is a no-op; an invalid challenge or exhausted fuel gives `b′ = 0` for both `b`. -/
noncomputable def cpaExpM (M : ℕ → Str → Prop) (E : PKE) (A : Adversary) (lam : ℕ) (b : Bool) :
    PMF Bool :=
  (E.keyLaw lam).bind fun k =>
    runGameM A E M lam k.1 (fun _ _ _ => none) b (A.p.eval lam + 1) none [] k.1

/-- `Adv^cpa_E(A, λ) = |Pr[Exp^{cpa,1}_E(A, λ) = 1] − Pr[Exp^{cpa,0}_E(A, λ) = 1]|` (Definition 2,
p.29). -/
noncomputable def advCPAM (M : ℕ → Str → Prop) (E : PKE) (A : Adversary) (lam : ℕ) : ℝ :=
  |((cpaExpM M E A lam true) true).toReal - ((cpaExpM M E A lam false) true).toReal|

/-- **IND-CPA** security over `M`: every uniform PPT adversary has negligible distinguishing
advantage (Definition 2, p.29: "The scheme is IND-CPA secure if this advantage is negligible for
every PPT adversary"). No correctness clause, as printed. For `M λ m := m.length = n λ` this is the
published `RestrictedDec.INDCPA`. -/
def INDCPAM (M : ℕ → Str → Prop) (E : PKE) : Prop :=
  ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (advCPAM M E A)

end Supplement

end RestrictedDec


