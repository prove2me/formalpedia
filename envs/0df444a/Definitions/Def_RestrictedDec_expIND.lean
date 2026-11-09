-- Prove2me | Definitions.Def_RestrictedDec_expIND
-- name    : RestrictedDec_expIND
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:43.003882+00:00
-- url     : https://prove2.me/theorems/f26a8900-20b3-4126-ac9b-bbd643e7489b
-- title:
--   Experiment $\mathrm{Exp}^{\mathrm{IND},t}_{\Pi,\mathcal F}$ and its advantage (Definition 1)
-- statement:
--   Fix a timing $t\in\{na,ad\}$, a scheme $\Pi$ over $\{0,1\}^{n(\lambda)}$ and a family $\mathcal F$. The experiment $\mathrm{Exp}^{\mathrm{IND},t}_{\Pi,\mathcal F}(A,\lambda)$:
--
--   1. generates $(pk,sk)\leftarrow\mathrm{KeyGen}(1^\lambda)$ and gives $pk$ to $A$;
--   2. answers each query $(F,c)$ with an admissible $F$ by $F(\mathrm{Dec}_{sk}(c))$;
--   3. on valid messages $m_0,m_1$ chooses $b\leftarrow\{0,1\}$ uniformly and gives $c^*\leftarrow\mathrm{Enc}_{pk}(m_b)$ to $A$;
--   4. if $t=na$, answers no further queries; if $t=ad$, answers $(F,c)$ with $c\neq c^*$ by $F(\mathrm{Dec}_{sk}(c))$, and answers $(F,c^*)$ by the common public value $F(m_0)$ when $F(m_0)=F(m_1)$, without decrypting $c^*$, refusing it otherwise;
--   5. outputs $1$ iff $A$'s guess $b'$ equals $b$.
--
--   The advantage is
--
--   $$\mathrm{Adv}^t_{\Pi,\mathcal F}(A,\lambda)=\Bigl|\Pr\bigl[\mathrm{Exp}^{\mathrm{IND},t}_{\Pi,\mathcal F}(A,\lambda)=1\bigr]-\tfrac12\Bigr|.$$
--
--   **Formalization Note** The bit $b$ is drawn right after key generation (equivalent, since nothing before the challenge depends on it). Inadmissible queries are refused; "$c\neq c^*$" is inequality of ciphertext strings; the restriction on $c^*$ applies to each query separately.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13

import Mathlib
import Definitions.Def_RestrictedDec_Family
import Definitions.Def_RestrictedDec_runGame
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

/-- The query timing `t ∈ {na, ad}`: pre-challenge (`na`) or adaptive (`ad`) access.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, p.13 ("We call access
pre-challenge (denoted na) when queries stop at the challenge, and adaptive (denoted ad) when they
may continue"). -/
inductive Timing
  | na
  | ad
  deriving DecidableEq

/-- The **functional decryption oracle** `O^𝓕_sk(F, c) = F(Dec_sk(c))` of the experiment
`Exp^{IND,t}_{P,𝓕}`, with the restrictions of Definition 1:
1. before the challenge, an admissible query `(F, c)` is answered with `F(Dec_sk(c))`;
2. after the challenge, `t = na` gives no answer; for `t = ad` an admissible query `(F, c)` with
   `c ≠ c*` is answered with `F(Dec_sk(c))`, and `(F, c*)` is answered with the common public value
   `F(m₀)` when `F(m₀) = F(m₁)`, without decrypting `c*`, and refused otherwise;
3. an inadmissible description is refused.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, p.13 (Oracle Responses;
Definition 1, steps 2 and 4).

**Formalization Note.** `none` is the refusal; `c ≠ c*` is inequality of ciphertext strings. -/
def indOracle (t : Timing) (P : PKE) (F : Family) (lam : ℕ) (sk : Str) :
    Option (Str × Str × Str) → Str → Str → Option Str
  | none, d, c => if F.admissible lam d then some (F.eval lam d (P.dec lam sk c)) else none
  | some (m0, m1, cs), d, c =>
    match t with
    | .na => none
    | .ad =>
      if F.admissible lam d then
        if c ≠ cs then some (F.eval lam d (P.dec lam sk c))
        else if F.eval lam d (some m0) = F.eval lam d (some m1) then some (F.eval lam d (some m0))
        else none
      else none

/-- The **experiment** `Exp^{IND,t}_{P,𝓕}(A, λ)` (Definition 1): `(pk, sk) ← KeyGen(1^λ)`,
`b ← {0,1}` uniform, the adversary interacts with the oracle `indOracle t` (first input `pk`, at
most `p(λ) + 1` activations), and the output is `1` iff its guess `b′` equals `b`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13. -/
noncomputable def expIND (t : Timing) (n : ℕ → ℕ) (P : PKE) (F : Family) (A : Adversary)
    (lam : ℕ) : PMF Bool :=
  (P.keyLaw lam).bind fun k =>
    (PMF.uniformOfFintype Bool).bind fun b =>
      (runGame A P n lam k.1 (indOracle t P F lam k.2) b (A.p.eval lam + 1) none [] k.1).map
        fun b' => decide (b' = b)

/-- The **advantage** `Adv^t_{P,𝓕}(A, λ) = |Pr[Exp^{IND,t}_{P,𝓕}(A, λ) = 1] − 1/2|`
(Definition 1, p.13). -/
noncomputable def adv (t : Timing) (n : ℕ → ℕ) (P : PKE) (F : Family) (A : Adversary)
    (lam : ℕ) : ℝ :=
  |((expIND t n P F A lam) true).toReal - 1 / 2|

end RestrictedDec


