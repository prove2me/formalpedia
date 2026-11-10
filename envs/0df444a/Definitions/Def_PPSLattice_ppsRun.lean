-- Prove2me | Definitions.Def_PPSLattice_ppsRun
-- name    : PPSLattice_ppsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:36:02.043434+00:00
-- url     : https://prove2.me/theorems/5905e979-fcfa-42ec-957b-24b4e36d7564
-- title:
--   Interaction of an adversary with the PPS challenger
-- statement:
--   After $(\mathrm{crs},\mathrm{ct}_{i^*})$ has been sent, the adversary interacts for at most a given number of activations; the result is its guess $b'$.
--
--   1. A query $(i,\mu)$ with $i\in[N]$, $i\ne i^*$, $\mu\in\{0,1\}^\lambda$ is answered with $\mathrm{ct}_i\leftarrow\mathrm{skEnc}(\mathrm{msk},i,\mu)$; other queries get a fixed empty answer.
--   2. A set $S\subseteq[N]$ with $i^*\in S$ (mode indistinguishability) or $i^*\notin S$ (payload hiding) is answered with $\mathrm{sk}_S\leftarrow\mathrm{KGen}(\mathrm{msk},S)$; the next move is the guess.
--   3. An inadmissible set, a guess before $S$, a non-guess after $S$, or running out of activations ends the run with a uniformly random guess.
--
--   **Formalization Note** Scoring an inadmissible branch as a uniform guess contributes exactly $\tfrac12$; this is equivalent to restricting to admissible adversaries, because an adversary can test its own admissibility and replace such a branch by an admissible set and a random guess.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Mode Indistinguishability and Payload Hiding, p.18

import Mathlib
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_PPSLattice_PPS
import Definitions.Def_PPSLattice_decPMove
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace PPSLattice

/-- The **interaction of an adversary with the PPS challenger** after `(crs, ct_{i*})` has been sent,
for at most `fuel` activations; the result is the adversary's guess `b′`. With `payload = false`
(mode indistinguishability) the admissible sets contain `i*`; with `payload = true` (payload hiding)
they do not.
1. A query `(i, µ)` with `i ∈ [N]`, `i ≠ i*`, `µ ∈ {0,1}^λ` is answered with `ct_i ← skEnc(msk, i, µ)`;
   any other query is answered with the empty string.
2. A set `S` with `S ⊆ [N]` on the admissible side of `i*` is answered with `sk_S ← KGen(msk, S)`;
   the next move must be the guess `b′`, which ends the run.
3. An inadmissible set, a guess before `S`, a move other than a guess after `S`, or running out of
   activations ends the run with a **uniformly random** guess, independent of everything else.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Mode Indistinguishability and Payload Hiding, p.18 ("S ← A^{O(·,·)}(crs,
ct_{i*,b}), sk_S ← KGen(msk, S)", "b ← A(sk_S)", "the oracle O takes as input (i, µ_i) ∈ [N] × M_λ,
i ≠ i* and responds with ct_i ← skEnc(msk, i, µ)", "A stateful PPT machine A is said to be
admissible if S ⊆ [N] and i* ∈ S" (resp. "i* ∉ S")).

**Formalization Note.** An inadmissible branch scores a uniform guess, so it contributes exactly
`½` to the success probability; this is equivalent to restricting to admissible adversaries,
because an adversary can test its own admissibility and replace any inadmissible branch by an
admissible set followed by a random guess. Out-of-domain oracle queries get a fixed answer that
does not depend on `b`. -/
noncomputable def ppsRun (E : PPS) (A : RestrictedDec.Adversary) (lam N : ℕ) (crs msk : Str)
    (istar : ℕ) (payload : Bool) : ℕ → Str → Str → PMF Bool
  | 0, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, s, input =>
    (A.activate lam s input).bind fun r =>
      match decPMove r.2 with
      | .query i mu =>
        if i ∈ Finset.Icc 1 N ∧ i ≠ istar ∧ mu.length = lam then
          (E.skEnc lam N crs msk i mu).bind fun ct =>
            ppsRun E A lam N crs msk istar payload fuel r.1 ct
        else ppsRun E A lam N crs msk istar payload fuel r.1 []
      | .setS S =>
        if S ⊆ Finset.Icc 1 N ∧ ((payload = true ∧ istar ∉ S) ∨ (payload = false ∧ istar ∈ S))
        then
          (E.kgen lam N crs msk S).bind fun sk =>
            match fuel with
            | 0 => PMF.uniformOfFintype Bool
            | _ + 1 =>
              (A.activate lam r.1 sk).bind fun r' =>
                match decPMove r'.2 with
                | .guess b' => PMF.pure b'
                | _ => PMF.uniformOfFintype Bool
        else PMF.uniformOfFintype Bool
      | .guess _ => PMF.uniformOfFintype Bool

end PPSLattice


