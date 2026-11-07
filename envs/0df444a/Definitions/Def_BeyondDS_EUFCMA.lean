-- Prove2me | Definitions.Def_BeyondDS_EUFCMA
-- name    : BeyondDS_EUFCMA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:12:51.649201+00:00
-- url     : https://prove2.me/theorems/551627fb-afb3-4887-9ea1-747ded80389d
-- title:
--   Negligible functions, non-uniform PPT reactive machines and EUF-CMA security
-- statement:
--   **Negligible.** $\nu:\mathbb N\to\mathbb R$ is negligible if it is nonnegative and for every $a$ eventually $\nu(\kappa)\le\kappa^{-a}$: "a nonnegative function that is eventually smaller than $\kappa^{-a}$ for every constant $a>0$".
--
--   **Reactive machine family.** A non-uniform probabilistic polynomial-time reactive machine is a polynomial-time map $f$, advice strings $a(\kappa)$ of length at most $q(\kappa)$, and a polynomial $q$. Each activation reads $\kappa$, the advice, its state, its input and $q(\kappa)$ fresh uniform coins, and keeps state and output of at most $q(\kappa)$ bits. Such a family acts as an adversary of the model at security parameter $\kappa$, reading the coded observations and writing a coded decision.
--
--   **Efficient scheme family.** $\kappa\mapsto\Sigma_\kappa$ has coins, keys and signature bound polynomial in $\kappa$, and $\mathrm{gen},\mathrm{sign},\mathrm{verify}$ computed in polynomial time by one machine each, with $\kappa$ in unary.
--
--   **EUF-CMA.** In the game, keys are generated honestly; the forger receives the public key, adaptively asks for signatures on messages of its choice, and outputs $(m,s)$; it wins if $(m,s)$ is accepted and $m$ was never queried. The family is EUF-CMA secure if every non-uniform PPT forger wins with negligible probability.
--
--   **Formalization Note** "Ordinary unforgeable signatures" (Theorem 1) is read as EUF-CMA against non-uniform PPT forgers; p.22: "no strong-unforgeability assumption is needed". The advice bound matters: with unbounded advice every language is decidable. Running out of activations loses the game.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §1.1, p.3 (PDF p.4); §4.2, pp.12–13 (PDF pp.13–14); §7.1, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_BeyondDS_IsEfficientProtocol

set_option autoImplicit false

open QAlgorithms.Complexity
open Polynomial

namespace BeyondDS

/-- `negl(κ)` of §1.1, p.3: "a nonnegative function that is eventually smaller than κ−a for every
constant a > 0". Natural `a` suffices, since a real `a` lies below a natural one. -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  (∀ κ, 0 ≤ ν κ) ∧ ∀ a : ℕ, ∃ κ₀, ∀ κ ≥ κ₀, ν κ ≤ ((κ : ℝ) ^ a)⁻¹

/-- A non-uniform probabilistic polynomial-time reactive machine family (§4.2, p.12: "the adversary may
use a polynomial-length advice string depending on the security parameter"). `f` is one polynomial-time
map; on each activation it reads the security parameter, the advice, its state, its input and fresh
coins. `q` bounds the advice, the coins and the state and output kept from each activation.

**Formalization Note.** The advice bound matters: with unbounded advice every language is decidable. The
truncation in `activate` is what closes polynomial time under many activations. -/
structure ReactiveFamily where
  f : Str → Str
  advice : ℕ → Str
  q : ℕ[X]

/-- The conditions on a reactive family. -/
def ReactiveFamily.Valid (R : ReactiveFamily) : Prop :=
  PolyTimeComputable R.f ∧ ∀ κ, (R.advice κ).length ≤ R.q.eval κ

/-- One activation: from state and input to new state and output, with fresh uniform coins. -/
noncomputable def ReactiveFamily.activate (R : ReactiveFamily) (κ : ℕ) (s input : Str) :
    PMF (Str × Str) :=
  (PMF.uniformOfFintype (Fin (R.q.eval κ) → Bool)).map fun c =>
    let out := untup (R.f (tup [encNat κ, R.advice κ, s, input, List.ofFn c]))
    ((out.getD 0 []).take (R.q.eval κ), (out.getD 1 []).take (R.q.eval κ))

/-- The code of an observation of the adversary, for bit-string messages and states. -/
def encObs {n : ℕ} : Obs n Str Str → Str
  | Obs.keys pk => tup [[false, false, false], tup ((List.finRange n).map pk)]
  | Obs.sent i j m => tup [[false, false, true], encNat i.val, encNat j.val, m]
  | Obs.revealed i s r k => tup [[false, true, false], encNat i.val, s, encResp r, k]
  | Obs.elected r l => tup [[false, true, true], encNat r, encNat l.val]
  | Obs.boundary r => tup [[true, false, false], encNat r]

/-- A unary field as an identity, if it is one. -/
def decId (n : ℕ) (w : Str) : Option (Fin n) :=
  if h : decNat w < n then some ⟨decNat w, h⟩ else none

/-- The parser of a move of the adversary: `tup [corrupt, inject, next]`, where `corrupt` is a `tup` of
unary identities, `inject` a `tup` of triples `tup [from, to, message]`, and `next` a one-element `tup`
for a named player or empty for "end round". Every move has a code. -/
def decDecision (n : ℕ) (w : Str) : Decision n Str :=
  let fs := untup w
  { corrupt := ((untup (fs.getD 0 [])).filterMap (decId n)).toFinset
    inject := (untup (fs.getD 1 [])).filterMap fun m =>
      let g := untup m
      match decId n (g.getD 0 []), decId n (g.getD 1 []) with
      | some a, some b => some (a, b, g.getD 2 [])
      | _, _ => none
    next := ((untup (fs.getD 2 [])).head?).bind (decId n) }

/-- A reactive family as an adversary of the model at security parameter `κ`. Its state is its
machine state. -/
noncomputable def ReactiveFamily.toAdversary (R : ReactiveFamily) (κ n : ℕ) : Adversary n Str Str where
  σ := Str
  init := PMF.pure []
  step := fun s obs =>
    (R.activate κ s (tup (obs.map encObs))).map fun r => (r.1, decDecision n r.2)

/-- A family of signature schemes, one per `κ`, is efficient: lengths polynomial in `κ`, and `gen`,
`sign`, `verify` computed in polynomial time, one machine for all `κ`, with `κ` in unary (p.15: "a
public polynomial length bound"). -/
def SigFamilyEfficient (Sg : ℕ → Sig) : Prop :=
  (∃ q : ℕ[X], ∀ κ, (Sg κ).coinLen ≤ q.eval κ ∧ (Sg κ).sigLen ≤ q.eval κ ∧
    ∀ c, ((Sg κ).gen c).1.length ≤ q.eval κ ∧ ((Sg κ).gen c).2.length ≤ q.eval κ) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ κ c,
    f (tup [encNat κ, List.ofFn c]) = tup [((Sg κ).gen c).1, ((Sg κ).gen c).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ κ sk m c,
    f (tup [encNat κ, sk, m, List.ofFn c]) = (Sg κ).sign sk m c) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ κ pk m s,
    f (tup [encNat κ, pk, m, s]) = encBool ((Sg κ).verify pk m s))

/-- The EUF-CMA game after key generation: the forger, in state `s` with input `input`, either asks for
a signature on the second output field (first output field `[]`) or answers `(m, s*)`, in the second and
third output fields (first output field nonempty). It has `fuel` activations left and `queried` holds its
queries so far. It wins if `(m, s*)` is accepted and `m` was never queried; running out of activations
loses. -/
noncomputable def forgeLoop (R : ReactiveFamily) (κ : ℕ) (S : Sig) (pk sk : Str) :
    ℕ → Str → Str → List Str → PMF Bool
  | 0, _, _, _ => PMF.pure false
  | fuel + 1, s, input, queried =>
    (R.activate κ s input).bind fun r =>
      let out := untup r.2
      if out.getD 0 [] = [] then
        S.coinLaw.bind fun c =>
          forgeLoop R κ S pk sk fuel r.1 (S.sign sk (out.getD 1 []) c) (out.getD 1 [] :: queried)
      else
        PMF.pure (S.accepts pk (out.getD 1 []) (out.getD 2 []) && decide (out.getD 1 [] ∉ queried))

/-- The probability that the forger wins the EUF-CMA game at `κ`: keys by `gen`, at most `q κ` queries,
the public key as its first input. -/
noncomputable def forgeWin (R : ReactiveFamily) (Sg : ℕ → Sig) (κ : ℕ) : ENNReal :=
  ((Sg κ).coinLaw.bind fun c =>
    forgeLoop R κ (Sg κ) ((Sg κ).gen c).1 ((Sg κ).gen c).2 (R.q.eval κ + 1) []
      ((Sg κ).gen c).1 []) true

/-- "Ordinary unforgeable signatures" (Theorem 1, p.3; p.22: "no strong-unforgeability assumption is
needed"), read as existential unforgeability under chosen-message attacks against non-uniform
probabilistic polynomial-time forgers (`paper.md` decisions 7–8): every such forger wins with negligible
probability. -/
def EUFCMA (Sg : ℕ → Sig) : Prop :=
  ∀ R : ReactiveFamily, R.Valid → ∃ ν, Negligible ν ∧ ∀ κ, forgeWin R Sg κ ≤ ENNReal.ofReal (ν κ)

end BeyondDS


