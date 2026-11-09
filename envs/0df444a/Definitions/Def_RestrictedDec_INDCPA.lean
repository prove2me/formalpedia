-- Prove2me | Definitions.Def_RestrictedDec_INDCPA
-- name    : RestrictedDec_INDCPA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:38.268145+00:00
-- url     : https://prove2.me/theorems/c792b5f1-c20f-4823-85b9-c30a0bd933ea
-- title:
--   IND-CPA security (Definition 2)
-- statement:
--   For $b\in\{0,1\}$ the experiment $\mathrm{Exp}^{\mathrm{cpa},b}_E(A,\lambda)$ samples $(pk,sk)\leftarrow\mathrm{KeyGen}(1^\lambda)$, gives $pk$ to $A$, on valid equal-length messages $(m_0,m_1)$ returns $c^*\leftarrow\mathrm{Enc}_{pk}(m_b)$, and outputs $A$'s final bit $b'$. The distinguishing advantage is
--
--   $$\mathrm{Adv}^{\mathrm{cpa}}_E(A,\lambda)=\Bigl|\Pr[\mathrm{Exp}^{\mathrm{cpa},1}_E(A,\lambda)=1]-\Pr[\mathrm{Exp}^{\mathrm{cpa},0}_E(A,\lambda)=1]\Bigr|,$$
--
--   and $E$ is **IND-CPA secure** if this advantage is negligible for every uniform PPT adversary. There is no correctness clause, as in the definition.
--
--   **Formalization Note** There is no oracle: a query move gets no answer. An invalid challenge or exhausted activations give $b'=0$ in both experiments.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 2, App. A.1, p.29

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_runGame
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

/-- The experiment `Exp^{cpa,b}_E(A, λ)` (Definition 2): keys `(pk, sk) ← KeyGen(1^λ)`, the
adversary gets `pk`, chooses valid equal-length `(m₀, m₁)`, receives `c* ← Enc_pk(m_b)`, and the
output is its final bit `b′`. There is no oracle.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 2, App. A.1, p.29.

**Formalization Note.** The interaction is `runGame` with an oracle that never answers, so a
"query" move is a no-op; an invalid challenge or exhausted fuel gives `b′ = 0` for both `b`. -/
noncomputable def cpaExp (n : ℕ → ℕ) (E : PKE) (A : Adversary) (lam : ℕ) (b : Bool) : PMF Bool :=
  (E.keyLaw lam).bind fun k =>
    runGame A E n lam k.1 (fun _ _ _ => none) b (A.p.eval lam + 1) none [] k.1

/-- `Adv^cpa_E(A, λ) = |Pr[Exp^{cpa,1}_E(A, λ) = 1] − Pr[Exp^{cpa,0}_E(A, λ) = 1]|`. -/
noncomputable def advCPA (n : ℕ → ℕ) (E : PKE) (A : Adversary) (lam : ℕ) : ℝ :=
  |((cpaExp n E A lam true) true).toReal - ((cpaExp n E A lam false) true).toReal|

/-- **IND-CPA** security over `{0,1}^{n(λ)}`: every uniform PPT adversary has negligible
distinguishing advantage (Definition 2, p.29: "The scheme is IND-CPA secure if this advantage is
negligible for every PPT adversary"). No correctness clause, as printed. -/
def INDCPA (n : ℕ → ℕ) (E : PKE) : Prop :=
  ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (advCPA n E A)

end RestrictedDec


