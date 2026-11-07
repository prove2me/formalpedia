-- Prove2me | Definitions.Def_CompNonlocal_IsASP
-- name    : CompNonlocal_IsASP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:48:14.186205+00:00
-- url     : https://prove2.me/theorems/1bbb8065-c846-4442-a60f-9b7750afb6ac
-- title:
--   $(\alpha,\beta)$-QCCC asymmetric state preparation
-- statement:
--   An ASP protocol is an **$(\alpha,\beta)$-ASP** if:
--
--   1. the sender, receiver and decoder are uniform QPT;
--   2. the receiver retains exactly its designated qubit and measures every other register into $\mathrm{msg}_R$ (so $\zeta_t$ is pure);
--   3. $0\le\alpha(\kappa)<\beta(\kappa)\le4$ and $\beta(\kappa)-\alpha(\kappa)\ge1/p(\kappa)$ for a polynomial $p$;
--   4. the decoder's output lies in the unit ball $B^3$;
--   5. completeness: eventually $\mathbb E\|\hat r_S-r(T)\|_2^2\le\alpha(\kappa)$ (Eq. (23));
--   6. honest-but-curious soundness: for every polynomial-size family $\{\mathcal A_\kappa\}$, eventually $\mathbb E\|\hat r_{\mathcal A}-r(T)\|_2^2\ge\beta(\kappa)$ (Eq. (24)).
--
--   **Formalization Note** Definition 14's polynomial-time computability of $\alpha,\beta$ is not required (Reading 8).
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 14, p.33

import Mathlib
import Definitions.Def_CompNonlocal_ASP_honestError
import Definitions.Def_CompNonlocal_ASP_advError
import Definitions.Def_CompNonlocal_Uniform

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- `(α, β)`-QCCC asymmetric state preparation. Głuch, Morimae, *From Computational Nonlocality to
Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…),
Definition 14, p.33:

1. the sender, receiver and decoder are uniform QPT;
2. the receiver "retains a designated qubit register Q … Before sending the message, it measures
   every remaining private quantum register and ancillas in the computational basis and includes
   all measurement outcomes in msg_R";
3. "0 ≤ α(κ) < β(κ) ≤ 4, β(κ) − α(κ) ≥ 1/p(κ) for a polynomial p";
4. the decoder "outputs a vector r̂_S ∈ B³";
5. completeness (23): eventually the sender's error is at most `α(κ)`;
6. honest-but-curious soundness (24): "For every polynomial-size quantum circuit family {A_κ} with
   classical advice", eventually its error is at least `β(κ)` ("with the onset in soundness allowed
   to depend on the adversary").

**Formalization Note** Definition 14 also asks α, β to be polynomial-time computable; that clause is
dropped (Reading 8): for Theorem 7, Corollary 3 and Lemma 17 this weakens their hypothesis, and the
constants of Theorem 6 are computable. "1/p(κ)" is `1/(p(κ) + 1)` for `p : Polynomial ℕ`. Condition 2
makes the prepared state pure; the product structure of Definition 14 holds by construction. -/
def IsASP (P : ASP) (α β : ℕ → ℝ) : Prop :=
  Uniform P.Sen ∧ Uniform P.Rec ∧ Uniform P.Dec ∧
    (∀ κ, (P.Rec κ).outQ = [P.qw κ] ∧ ∀ i, i ∈ (P.Rec κ).outC ∨ i = P.qw κ) ∧
    (∀ κ, 0 ≤ α κ ∧ α κ < β κ ∧ β κ ≤ 4) ∧
    (∃ p : Polynomial ℕ, ∀ κ, 1 ≤ (β κ - α κ) * ((p.eval κ : ℕ) + 1 : ℝ)) ∧
    (∀ κ (z : Bits (P.Dec κ).width), ‖decVec ((P.Dec κ).clOut z)‖ ≤ 1) ∧
    (∀ᶠ κ in Filter.atTop, P.honestError κ ≤ α κ) ∧
    (∀ Adv : Family, PolySize Adv → ∀ᶠ κ in Filter.atTop, β κ ≤ P.advError κ (Adv κ))

end CompNonlocal


