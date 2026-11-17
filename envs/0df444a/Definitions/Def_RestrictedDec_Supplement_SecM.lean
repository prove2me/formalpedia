-- Prove2me | Definitions.Def_RestrictedDec_Supplement_SecM
-- name    : RestrictedDec_Supplement_SecM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:22:57.565584+00:00
-- url     : https://prove2.me/theorems/ed6fac05-6ec7-4a68-9d4e-bd32c9eb8d1d
-- title:
--   $\mathrm{Exp}^{\mathrm{IND},t}$, advantage, Gap and $\mathrm{Sec}^t(\mathcal F)$ over $M$
-- statement:
--   For a timing $t\in\{\mathrm{na},\mathrm{ad}\}$, a scheme $P$, a family $\mathcal F$ and an adversary $A$:
--
--   1. the **world $b$** of $\mathrm{Exp}^{\mathrm{IND},t}_{P,\mathcal F}(A,\lambda)$ generates keys and runs $A$ against the functional decryption oracle $F(\mathrm{Dec}_{sk}(c))$ with the restrictions of Definition 1, with challenge bit $b$;
--   2. the experiment draws $b$ uniformly and outputs $1$ iff $b'=b$; the **advantage** is $\mathrm{Adv}^t_{P,\mathcal F}(A,\lambda)=|\Pr[\mathrm{Exp}=1]-\tfrac12|$;
--   3. the **gap** is $\mathrm{Gap}(A)=|\Pr[A\Rightarrow1\mid b=1]-\Pr[A\Rightarrow1\mid b=0]|$ (App. B.4);
--   4. $P\in\mathrm{Sec}^t(\mathcal F)$ iff $P$ has ordinary negligible-error correctness and every uniform PPT adversary has negligible advantage;
--   5. IND-CCA1 and IND-CCA2 over $M$ are $\mathrm{Sec}^{na}(\mathcal F_{\mathrm{id}})$ and $\mathrm{Sec}^{ad}(\mathcal F_{\mathrm{id}})$.
--
--   **Formalization Note** The oracle is the published `RestrictedDec.indOracle`. The adversary may be started in a given state $s_0$; the standard experiment uses the empty state, and a nonempty $s_0$ is used only for the conditional bound of Theorem 11.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13; §2.2, p.14; App. B.4, p.40

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_famId
import Definitions.Def_RestrictedDec_expIND
import Definitions.Def_RestrictedDec_Supplement_CorrectM
import Definitions.Def_RestrictedDec_Supplement_runGameM
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- The **fixed-bit world** of the experiment `Exp^{IND,t}_{P,𝓕}(A, λ)` over the message space
`M`, with the adversary started in the state `s₀`: `(pk, sk) ← KeyGen(1^λ)`, the challenge bit is
`b`, the adversary interacts with the functional decryption oracle `indOracle t` (first input `pk`,
at most `p(λ) + 1` activations), and the result is its guess `b′`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13; App. B.4,
p.40 ("Gap(A) = |Pr[A ⇒ 1 | b = 1] − Pr[A ⇒ 1 | b = 0]|").

**Formalization Note.** `indOracle` and `Timing` are the published `RestrictedDec` ones. The
standard experiment starts the adversary in the empty state `s₀ = []`; a nonempty `s₀` is used
only to state Theorem 11's bound conditional on given sampler coins. -/
noncomputable def expWorldM (t : Timing) (M : ℕ → Str → Prop) (P : PKE) (F : Family)
    (A : Adversary) (lam : ℕ) (s0 : Str) (b : Bool) : PMF Bool :=
  (P.keyLaw lam).bind fun k =>
    runGameM A P M lam k.1 (indOracle t P F lam k.2) b (A.p.eval lam + 1) none s0 k.1

/-- The **experiment** `Exp^{IND,t}_{P,𝓕}(A, λ)` over `M`, adversary started in state `s₀`:
`b ← {0,1}` uniform, then the world `b`; the output is `1` iff `b′ = b` (Definition 1, p.13). -/
noncomputable def expINDM (t : Timing) (M : ℕ → Str → Prop) (P : PKE) (F : Family)
    (A : Adversary) (lam : ℕ) (s0 : Str) : PMF Bool :=
  (PMF.uniformOfFintype Bool).bind fun b =>
    (expWorldM t M P F A lam s0 b).map fun b' => decide (b' = b)

/-- The **advantage** `Adv^t_{P,𝓕}(A, λ) = |Pr[Exp^{IND,t}_{P,𝓕}(A, λ) = 1] − 1/2|` over `M`
(Definition 1, p.13), adversary started in the empty state. -/
noncomputable def advM (t : Timing) (M : ℕ → Str → Prop) (P : PKE) (F : Family) (A : Adversary)
    (lam : ℕ) : ℝ :=
  |((expINDM t M P F A lam []) true).toReal - 1 / 2|

/-- The **distinguishing gap** `Gap_{P,𝓕}(A, λ) = |Pr[A ⇒ 1 | b = 1] − Pr[A ⇒ 1 | b = 0]|` in
`Exp^{IND,t}_{P,𝓕}` over `M` (App. B.4, p.40: "This is twice the usual success advantage"). -/
noncomputable def gapM (t : Timing) (M : ℕ → Str → Prop) (P : PKE) (F : Family) (A : Adversary)
    (lam : ℕ) : ℝ :=
  |((expWorldM t M P F A lam [] true) true).toReal -
    ((expWorldM t M P F A lam [] false) true).toReal|

/-- The **security class** `Sec^t(𝓕)` (`IND^t_𝓕` security) over the message space `M`: the scheme
has ordinary negligible-error correctness (Definition 3) and every uniform PPT adversary has
negligible advantage in `Exp^{IND,t}_{P,𝓕}`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13 ("A scheme
satisfies INDna F or INDad F if it has ordinary negligible-error correctness (Definition 3) and every
probabilistic polynomial-time (PPT) adversary has negligible advantage in the corresponding game.
… Write Secna(F) and Secad(F) for the schemes secure in these games.").

**Formalization Note.** The published `RestrictedDec.Sec` over `M` instead of `{0,1}^{n(λ)}`.
Efficiency of the scheme is the separate predicate `IsSchemeM`. -/
def SecM (t : Timing) (M : ℕ → Str → Prop) (F : Family) (P : PKE) : Prop :=
  CorrectM M P ∧ ∀ A : Adversary, A.Valid → NoisyOWMPC.Negligible (advM t M P F A)

/-- **IND-CCA1** security over `M`: `Sec^na(𝓕_id)` (§2.2, p.14: "If the identity function idM⊥ is
permitted, the pre-challenge and adaptive games recover IND-CCA1 and IND-CCA2"). -/
def INDCCA1M (M : ℕ → Str → Prop) (P : PKE) : Prop := SecM .na M famId P

/-- **IND-CCA2** security over `M`: `Sec^ad(𝓕_id)` (§2.2, p.14). -/
def INDCCA2M (M : ℕ → Str → Prop) (P : PKE) : Prop := SecM .ad M famId P

end Supplement

end RestrictedDec


