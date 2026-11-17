-- Prove2me | Definitions.Def_RestrictedDec_Supplement_QueryBounded
-- name    : RestrictedDec_Supplement_QueryBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:34:14.091374+00:00
-- url     : https://prove2.me/theorems/e07ea7b4-1f96-44e8-a904-788e4539b57e
-- title:
--   Adversaries making at most $Q(\lambda)$ functional-decryption queries
-- statement:
--   An adversary $A$ **makes at most $Q(\lambda)$ queries** in $\mathrm{Exp}^{\mathrm{IND},t}_{P,\mathcal F}$ over $M$ if, for every $\lambda$ and both challenge bits, every run of the experiment (over keys, challenge encryption and the adversary's coins) contains at most $Q(\lambda)$ functional-decryption query moves.
--
--   $Q$ is the query bound in the term $6Q\epsilon_{SS}$ of (B.5).
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.4, p.40

import Mathlib
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_RestrictedDec_expIND
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

open Classical in
/-- The **number of functional-decryption queries** made in a run of the game `runGameM` (same
arguments, same transitions): each query move counts `1`; the run ends as in `runGameM`. -/
noncomputable def queriesM (A : Adversary) (E : PKE) (M : ℕ → Str → Prop) (lam : ℕ) (pk : Str)
    (oracle : Option (Str × Str × Str) → Str → Str → Option Str) (b : Bool) :
    ℕ → Option (Str × Str × Str) → Str → Str → PMF ℕ
  | 0, _, _, _ => PMF.pure 0
  | fuel + 1, ph, s, input =>
    (A.activate lam s input).bind fun r =>
      match decMove r.2, ph with
      | .query d c, _ =>
          (queriesM A E M lam pk oracle b fuel ph r.1 (encOpt (oracle ph d c))).map (· + 1)
      | .challenge m0 m1, none =>
          if M lam m0 ∧ M lam m1 ∧ m0.length = m1.length then
            (E.encLaw lam pk (if b then m1 else m0)).bind fun cs =>
              queriesM A E M lam pk oracle b fuel (some (m0, m1, cs)) r.1 cs
          else PMF.pure 0
      | .challenge _ _, some _ => PMF.pure 0
      | .guess _, _ => PMF.pure 0

/-- The adversary **makes at most `Q(λ)` functional-decryption queries** in
`Exp^{IND,t}_{P,𝓕}(A, λ)` over `M`: for every `λ` and both challenge bits, every possible number of
queries of a run is at most `Q(λ)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. B.4, p.40 ("Let Q bound the
number of functional-decryption queries"; Theorem 10: "every PPT adversary making at most Q
queries"). -/
def QueryBounded (t : Timing) (M : ℕ → Str → Prop) (P : PKE) (F : Family) (A : Adversary)
    (Q : ℕ → ℕ) : Prop :=
  ∀ (lam : ℕ) (b : Bool), ∀ n ∈ ((P.keyLaw lam).bind fun k =>
    queriesM A P M lam k.1 (indOracle t P F lam k.2) b (A.p.eval lam + 1) none [] k.1).support,
    n ≤ Q lam

end Supplement

end RestrictedDec


