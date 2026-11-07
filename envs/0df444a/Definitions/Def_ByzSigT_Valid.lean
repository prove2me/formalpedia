-- Prove2me | Definitions.Def_ByzSigT_Valid
-- name    : ByzSigT_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:54:16.363666+00:00
-- url     : https://prove2.me/theorems/c2e374e5-ae1d-4a08-a0f6-50be0d6f039d
-- title:
--   Validity of messages, certificates and justifications; corrupt sets; conflicting certificates
-- statement:
--   This definition transcribes the recursive validity rules of §4.2. The validity of a term depends only on the validity of its proper subterms.
--
--   1. A **certificate** $\sigma$ of a given kind, layer and value is a tuple of exactly $n-f$ valid messages of that kind from distinct parties outside its corrupt set $D_\sigma$. In layer $k+1$ it must also satisfy $|D_\sigma|>(3f-n)/2$.
--   2. The **corrupt set** $D_X$ is the set of parties proved corrupt by $X$: by a corruption proof among valid messages occurring in $X$, or by having messages in both of two conflicting certificates occurring in $X$.
--   3. **Conflicting certificates** of a layer are two $V$ certificates, or two $V2$ certificates, for different values of the same view, or a $V2_a$ certificate of view $v$ and a $V_b$ certificate, $b\ne a$, of a later view whose vote1 messages all contain locks from views before $v$.
--   4. A **valid message** carries a valid input justification of its sender, except decided messages, together with the evidence printed on p.16: a lock from an earlier view for suggest and propose, a valid propose from the leader for vote1, a $V_a$ or $V2_a$ certificate for vote2 and vote3, a $V3_a$ or $\mathrm{SigT}^{(i)}$ certificate for a value-SigT, a $\mathrm{SigT}^{(i)}$ certificate and the sender's value-SigT for allgood, conflicting certificates and the sender's token for equiv.
--   5. A **valid input justification** for $a$ in layer $\ell\ge 2$ holds the party's own allgood/equiv message of layer $\ell-1$, its blame, and $n-f$ valid messages from parties outside its corrupt set, with one of three types: clean ($n-f$ allgood messages for $a$), adopt (an allgood message for $a$ and an equiv message, one of them the party's own), or tally ($n-f$ equiv messages and the outcome of lines 54–65).
--
--   These rules are the content of the protocol's safety argument: every statement about certificates in the mission reads them.
--
--   **Formalization Note** Validity is written as a one-step rule iterated from "false"; the iteration stabilizes at the nesting depth of the term. The blame is stored as evidence inside the justification, so "outside its blame" is "outside $D_J$". The layer-$(k+1)$ condition is $3f<n+2|D_\sigma|$ in $\mathbb Z$.
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), §4.2, pp.15–16 (PDF 16–17)

import Mathlib
import Definitions.Def_ByzSigT_Msg

open Classical

namespace ByzSigT

/-!
# Validity of messages, certificates and justifications; corrupt sets; conflicting certificates

Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…), §4.2, pp.15–16 (PDF 16–17), verbatim:

> Certificates. A certificate σ consists of n − f valid messages from distinct parties outside its
> corrupt set D_σ, the set identified by all corruption proofs in σ. A V_a, V2_a, or V3_a
> certificate of view v consists of vote1, vote2, or vote3 messages, respectively, for a of view v;
> a SigT^(i) or allgood certificate for a consists of value-SigT^(i) or allgood messages for a. In
> layer k + 1, a certificate is valid only if, in addition, |D_σ| > (3f − n)/2. The validity of a
> certificate thus depends only on its contents. Conflicting certificates are two V certificates,
> or two V2 certificates, for different values of the same view, or a V2_a certificate of view v
> and a V_b certificate for b ≠ a of a later view whose vote1 messages contain locks from views
> before v, all of the same layer. All instructions to form a certificate require that the
> resulting certificate be valid.

> Corruption proofs. A party is proved corrupt by its messages in both of two conflicting
> certificates, or by two of its messages from one layer that are: vote1 messages, or vote2
> messages, for different values in the same view; vote3 or value-SigT messages for different
> values; an allgood message for a and a vote3 or value-SigT message for b ≠ a; or an allgood and
> an equiv message.

> Justifications. Validity is defined recursively, and parties ignore invalid messages. In layer 1,
> ⊥ is an input justification for either value. For i > 1, an input justification of party p for a
> in layer i contains p’s own allgood/equiv message from layer i − 1, its blame, which contains
> every party the justification proves corrupt, and one of the following from layer i − 1:
> 1. clean: n − f allgood messages for a from parties outside its blame.
> 2. adopt: an allgood message for a and an equiv message, one of which is p’s own, and n − f
>    allgood/equiv messages from parties outside its blame.
> 3. tally: n − f equiv messages from parties outside its blame, and the evidence and choices with
>    which lines 54–65 give a, where u_p on line 59 is the value justified by p’s input
>    justification for layer i − 1 in p’s own allgood/equiv message (either value if it is ⊥).

plus the carried justifications of p.16: every message of layer `i` except decided carries its
sender's input justification for layer `i`; propose for `a` of view `v` carries a lock for `a` from
a view `v' < v` (an input justification for `a` if `v' = −1`, a `V_a` certificate of view `v'`
otherwise); vote1 for `a` of view `v` a valid propose for `a` of view `v` from `leader(v)`; suggest
of view `v` a lock from a view before `v`; vote2 and vote3 for `a` of view `v` a `V_a` and a `V2_a`
certificate of view `v`; value-SigT^{(i)} for `a` a `V3_a` certificate or a SigT^{(i)} certificate
for `a`; allgood for `a` a SigT^{(i)} certificate for `a` and its sender's value-SigT^{(i)} for `a`;
equiv conflicting certificates of layer `i` and its sender's SigT^{(i)}.

**Formalization Note.**
* The validity of a term depends only on the validity of its proper subterms. It is written as a
  one-step rule `rule f V` that consults a validity oracle `V` only on judgments about proper
  subterms, iterated from `False` (`okAt f m`); `Valid f` is the eventual value, which the iteration
  reaches after as many steps as the nesting depth of the term. Judgments: a message (classical or
  token), a certificate of a kind, layer and value, an input justification of a party for a value
  in a layer.
* `corruptSet f X` (`D_X`) is the set of parties proved corrupt by `X`: by a pair of valid messages
  (`ProofPair`) occurring as proper subterms of `X`, or by having messages in both of two
  conflicting certificates occurring as proper subterms of `X`. The blame of a justification, stored
  as evidence inside it, is its corrupt set: "outside its blame" is "outside `D_J`".
* Certificates have exactly `n − f` messages (`ℕ` subtraction; `n > 2f` in every use), all valid,
  with distinct signers outside `D_σ`. The layer-`(k+1)` rule `|D_σ| > (3f − n)/2` is
  `3f < n + 2|D_σ|` in `ℤ`.
* A justification "from layer `j`" is an input justification for layer `j + 1`. In a tally
  justification, `V` (line 54) is the set of values of the valid value-SigT^{(j)} messages occurring
  in it; it "uses line 56" when `j = k ≥ 2` and it contains a valid allgood certificate of layer
  `k − 1`, and then it is for that certificate's value; for `V = {0, 1}` its extra component lists,
  for each value, the chosen value-SigT and the `V3` certificate in that value-SigT's evidence
  (line 63), and the value is `tallyWinner` (lines 64–65).
* "vote3 or value-SigT messages for different values" is read as any two such messages (also one of
  each kind); a correct party never sends a vote3 for one value and a value-SigT for the other
  (lines 21, 32).
-/

variable {n k : ℕ}

/-- The judgments whose validity is defined. -/
inductive Judg (n k : ℕ) : Type where
  /-- A message (a classically signed message or a token). -/
  | msg (t : Term n k) : Judg n k
  /-- `σ` is a certificate of kind `κ` for `a` of layer `ℓ`. -/
  | cert (κ : CertKind) (ℓ : ℕ) (a : Bool) (σ : Term n k) : Judg n k
  /-- `J` is an input justification of party `p` for `a` in layer `ℓ`. -/
  | just (p : Fin n) (ℓ : ℕ) (a : Bool) (J : Term n k) : Judg n k

/-- Conflicting certificates of layer `ℓ`, in one order (relative to an oracle `V`): two V
certificates or two V2 certificates for different values of the same view, or a `V2_a`
certificate of view `v` and a `V_b` certificate, `b ≠ a`, of a later view all of whose vote1
messages carry locks from views before `v`. -/
def ConflictingOrdV (V : Judg n k → Prop) (ℓ : ℕ) (σ σ' : Term n k) : Prop :=
  (∃ (v : ℕ) (a b : Bool), a ≠ b ∧ V (.cert (.V v) ℓ a σ) ∧ V (.cert (.V v) ℓ b σ')) ∨
  (∃ (v : ℕ) (a b : Bool), a ≠ b ∧ V (.cert (.V2 v) ℓ a σ) ∧ V (.cert (.V2 v) ℓ b σ')) ∨
  (∃ (v w : ℕ) (a b : Bool) (ms' : List (Term n k)), a ≠ b ∧ v < w ∧
    V (.cert (.V2 v) ℓ a σ) ∧ V (.cert (.V w) ℓ b σ') ∧ σ' = .list ms' ∧
    ∀ s ∈ ms', Vote1LockBefore s v)

/-- Conflicting certificates of layer `ℓ` (either order), relative to an oracle `V`. -/
def ConflictingV (V : Judg n k → Prop) (ℓ : ℕ) (σ σ' : Term n k) : Prop :=
  ConflictingOrdV V ℓ σ σ' ∨ ConflictingOrdV V ℓ σ' σ

/-- The corrupt set `D_X` relative to an oracle `V`. -/
noncomputable def corruptSetV (V : Judg n k → Prop) (X : Term n k) : Finset (Fin n) :=
  Finset.univ.filter fun q =>
    (∃ s s' : Term n k, Term.ProperSubterm s X ∧ Term.ProperSubterm s' X ∧ V (.msg s) ∧
      V (.msg s') ∧ ProofPair q s s') ∨
    (∃ (ℓ : ℕ) (σ σ' : Term n k), Term.ProperSubterm σ X ∧ Term.ProperSubterm σ' X ∧
      ConflictingV V ℓ σ σ' ∧ q ∈ certSigners σ ∧ q ∈ certSigners σ')

/-- `ℓ` is a layer: `1 ≤ ℓ ≤ k + 1`. -/
def LayerOK (k ℓ : ℕ) : Prop := 1 ≤ ℓ ∧ ℓ ≤ k + 1

/-- `J` is a valid input justification of `q` for some value in layer `ℓ` (relative to `V`). -/
def CarriesJ (V : Judg n k → Prop) (q : Fin n) (ℓ : ℕ) (J : Term n k) : Prop :=
  ∃ a : Bool, V (.just q ℓ a J)

/-- The evidence `ev` of a lock for `a` with code `c` (view `c − 1`) in layer `ℓ` is valid: an
input justification for `a` (of some party) if `c = 0`, a `V_a` certificate of view `c − 1`
otherwise. -/
def LockOK (V : Judg n k → Prop) (ℓ : ℕ) (a : Bool) (c : ℕ) (ev : Term n k) : Prop :=
  (c = 0 ∧ ∃ owner : Fin n, V (.just owner ℓ a ev)) ∨
  (∃ w : ℕ, c = w + 1 ∧ V (.cert (.V w) ℓ a ev))

/-- The one-step validity rule for messages (relative to the oracle `V`). -/
def msgRule (V : Judg n k → Prop) (t : Term n k) : Prop :=
  -- suggest of view v: a lock from a view before v
  (∃ (q : Fin n) (ℓ : ℕ) (L : Term n k) (v : ℕ) (J : Term n k),
    t = (Msg.suggest ℓ L v J).signed q ∧ LayerOK k ℓ ∧ CarriesJ V q ℓ J ∧
    ∃ (a : Bool) (c : ℕ) (ev : Term n k), L = lockTerm a c ev ∧ (c : ℤ) - 1 < v ∧
      LockOK V ℓ a c ev) ∨
  -- propose for a of view v: a lock for a from a view before v
  (∃ (q : Fin n) (ℓ : ℕ) (a : Bool) (L : Term n k) (v : ℕ) (J : Term n k),
    t = (Msg.propose ℓ a L v J).signed q ∧ LayerOK k ℓ ∧ CarriesJ V q ℓ J ∧
    ∃ (c : ℕ) (ev : Term n k), L = lockTerm a c ev ∧ (c : ℤ) - 1 < v ∧ LockOK V ℓ a c ev) ∨
  -- vote1 for a of view v: a valid propose for a of view v from leader(v)
  (∃ (q : Fin n) (ℓ : ℕ) (a : Bool) (v : ℕ) (P J : Term n k),
    t = (Msg.vote1 ℓ a v P J).signed q ∧ LayerOK k ℓ ∧ CarriesJ V q ℓ J ∧
    ∃ (q' : Fin n) (L J' : Term n k), IsLeader q' v ∧ P = (Msg.propose ℓ a L v J').signed q' ∧
      V (.msg P)) ∨
  -- vote2 for a of view v: a V_a certificate of view v
  (∃ (q : Fin n) (ℓ : ℕ) (σ : Term n k) (a : Bool) (v : ℕ) (J : Term n k),
    t = (Msg.vote2 ℓ σ a v J).signed q ∧ LayerOK k ℓ ∧ CarriesJ V q ℓ J ∧
    V (.cert (.V v) ℓ a σ)) ∨
  -- vote3 for a of view v: a V2_a certificate of view v (layers ≤ k only)
  (∃ (q : Fin n) (ℓ : ℕ) (σ : Term n k) (a : Bool) (v : ℕ) (J : Term n k),
    t = (Msg.vote3 ℓ σ a v J).signed q ∧ 1 ≤ ℓ ∧ ℓ ≤ k ∧ CarriesJ V q ℓ J ∧
    V (.cert (.V2 v) ℓ a σ)) ∨
  -- decided: carries no justification
  (∃ (q : Fin n) (a : Bool), t = (Msg.decided a).signed q) ∨
  -- viewchange
  (∃ (q : Fin n) (ℓ v : ℕ) (J : Term n k),
    t = (Msg.viewchange ℓ v J).signed q ∧ LayerOK k ℓ ∧ CarriesJ V q ℓ J) ∨
  -- equiv: conflicting certificates of layer ℓ and its sender's SigT^(ℓ)
  (∃ (q : Fin n) (ℓ : ℕ) (s σa σb J : Term n k),
    t = (Msg.equiv ℓ s σa σb J).signed q ∧ 1 ≤ ℓ ∧ ℓ ≤ k ∧ CarriesJ V q ℓ J ∧
    ConflictingV V ℓ σa σb ∧ (∃ (i : Fin k) (b : Term n k), IsTokIdx ℓ i ∧ s = .tok q i b) ∧
    V (.msg s)) ∨
  -- allgood for a: a SigT^(ℓ) certificate for a and its sender's value-SigT^(ℓ) for a
  (∃ (q : Fin n) (ℓ : ℕ) (a : Bool) (s σ J : Term n k),
    t = (Msg.allgood ℓ a s σ J).signed q ∧ 1 ≤ ℓ ∧ ℓ ≤ k ∧ CarriesJ V q ℓ J ∧
    V (.cert .sigT ℓ a σ) ∧ IsValueSigTOf q ℓ a s ∧ V (.msg s)) ∨
  -- value-SigT^(i+1) for a: a V3_a certificate or a SigT^(i+1) certificate for a
  (∃ (q : Fin n) (i : Fin k) (a : Bool) (σ J : Term n k),
    t = valueSigT q i a σ J ∧ CarriesJ V q (i.val + 1) J ∧
    ((∃ v : ℕ, V (.cert (.V3 v) (i.val + 1) a σ)) ∨ V (.cert .sigT (i.val + 1) a σ))) ∨
  -- the equiv token of line 38
  (∃ (q : Fin n) (i : Fin k) (σa σb J : Term n k),
    t = .tok q i (equivBody σa σb J) ∧ CarriesJ V q (i.val + 1) J ∧
    ConflictingV V (i.val + 1) σa σb)

/-- The one-step validity rule for certificates. -/
def certRule (f : ℕ) (V : Judg n k → Prop) (κ : CertKind) (ℓ : ℕ) (a : Bool) (σ : Term n k) :
    Prop :=
  ∃ ms : List (Term n k), σ = .list ms ∧ ms.length = n - f ∧ (ms.filterMap Term.signer).Nodup ∧
    (∀ s ∈ ms, CertMsg κ ℓ a s ∧ V (.msg s)) ∧
    (∀ s ∈ ms, ∀ q, s.signer = some q → q ∉ corruptSetV V σ) ∧
    (ℓ = k + 1 → (3 * f : ℤ) < n + 2 * ((corruptSetV V σ).card : ℤ))

/-- The value justified by an input justification `J` is `a` (either value for `⊥`). -/
def JustValueIs (J : Term n k) (a : Bool) : Prop :=
  J = botJust ∨ ∃ (j : ℕ) (ty : JType) (own bl : Term n k) (ms : List (Term n k)) (ex : Term n k),
    J = justTerm j a ty own bl ms ex

/-- The value `a` is the one justified by the input justification carried by `own` (line 59). -/
def OwnInputIs (own : Term n k) (a : Bool) : Prop :=
  ∃ (q : Fin n) (j : ℕ) (Jo : Term n k), JustValueIs Jo a ∧
    ((∃ (b : Bool) (s σ : Term n k), own = (Msg.allgood j b s σ Jo).signed q) ∨
     (∃ s σa σb : Term n k, own = (Msg.equiv j s σa σb Jo).signed q))

/-- Line 63's choice for value `c`: a valid value-SigT^{(j)} `vs` for `c` and a valid layer-`j`
`V3_c` certificate `τ` in its evidence. -/
def ChoiceV (V : Judg n k → Prop) (j : ℕ) (c : Bool) (vs τ : Term n k) : Prop :=
  V (.msg vs) ∧ (∃ q : Fin n, IsValueSigTOf q j c vs) ∧ Term.Subterm τ vs ∧
    ∃ v : ℕ, V (.cert (.V3 v) j c τ)

/-- The tally rule (lines 54–65) for a justification `J` for `a` from layer `j` whose `n − f`
messages are `ms` and whose extra component is `extra`. -/
def TallyRuleV (V : Judg n k → Prop) (j : ℕ) (a : Bool) (own : Term n k)
    (ms : List (Term n k)) (extra J : Term n k) : Prop :=
  let Vs : Set Bool := {c | ∃ s : Term n k, Term.ProperSubterm s J ∧ V (.msg s) ∧
    ∃ q : Fin n, IsValueSigTOf q j c s}
  let L56 : Prop := j = k ∧ 2 ≤ k ∧ ∃ (σ : Term n k) (c : Bool), Term.ProperSubterm σ J ∧
    V (.cert .allgood (k - 1) c σ)
  (L56 ∧ ∃ σ : Term n k, Term.ProperSubterm σ J ∧ V (.cert .allgood (k - 1) a σ)) ∨
  (¬ L56 ∧ Vs = ∅ ∧ OwnInputIs own a) ∨
  (¬ L56 ∧ Vs = {a}) ∨
  (¬ L56 ∧ Vs = Set.univ ∧ ∃ vs₀ τ₀ vs₁ τ₁ : Term n k,
    extra = .list [.nat 3, vs₀, τ₀, vs₁, τ₁] ∧ ChoiceV V j false vs₀ τ₀ ∧ ChoiceV V j true vs₁ τ₁ ∧
    a = tallyWinner (certSigners τ₀) (certSigners τ₁) (certSigners (.list ms)))

/-- The one-step validity rule for input justifications of `p` for `a` in layer `ℓ`. -/
def justRule (f : ℕ) (V : Judg n k → Prop) (p : Fin n) (ℓ : ℕ) (a : Bool) (J : Term n k) :
    Prop :=
  (ℓ = 1 ∧ J = botJust) ∨
  (2 ≤ ℓ ∧ ℓ ≤ k + 1 ∧
    ∃ (ty : JType) (own bl : Term n k) (ms : List (Term n k)) (extra : Term n k),
      J = justTerm (ℓ - 1) a ty own bl ms extra ∧
      V (.msg own) ∧ ((∃ b : Bool, IsAllgoodOf p (ℓ - 1) b own) ∨ IsEquivOf p (ℓ - 1) own) ∧
      ms.length = n - f ∧ (ms.filterMap Term.signer).Nodup ∧ (∀ s ∈ ms, V (.msg s)) ∧
      (∀ s ∈ ms, ∀ q, s.signer = some q → q ∉ corruptSetV V J) ∧
      ((ty = .clean ∧ ∀ s ∈ ms, ∃ q : Fin n, IsAllgoodOf q (ℓ - 1) a s) ∨
       (ty = .adopt ∧ (∀ s ∈ ms, ∃ q : Fin n, (∃ b : Bool, IsAllgoodOf q (ℓ - 1) b s) ∨
          IsEquivOf q (ℓ - 1) s) ∧
        ∃ ag eq : Term n k, extra = .list [ag, eq] ∧ (∃ q : Fin n, IsAllgoodOf q (ℓ - 1) a ag) ∧
          (∃ q : Fin n, IsEquivOf q (ℓ - 1) eq) ∧ V (.msg ag) ∧ V (.msg eq) ∧
          (ag = own ∨ eq = own)) ∨
       (ty = .tally ∧ (∀ s ∈ ms, ∃ q : Fin n, IsEquivOf q (ℓ - 1) s) ∧
        TallyRuleV V (ℓ - 1) a own ms extra J)))

/-- The one-step validity rule. -/
def rule (f : ℕ) (V : Judg n k → Prop) : Judg n k → Prop
  | .msg t => msgRule V t
  | .cert κ ℓ a σ => certRule f V κ ℓ a σ
  | .just p ℓ a J => justRule f V p ℓ a J

/-- The `m`-th iterate of the validity rule, starting from `False`. -/
def okAt (f : ℕ) : ℕ → Judg n k → Prop
  | 0, _ => False
  | m + 1, j => rule f (okAt f m) j

/-- Validity: the eventual value of `okAt f m` (reached once `m` exceeds the nesting depth). -/
def Valid (f : ℕ) (j : Judg n k) : Prop := ∃ M : ℕ, ∀ m ≥ M, okAt f m j

/-- A valid message (classical or token). -/
def ValidMsg (f : ℕ) (t : Term n k) : Prop := Valid f (.msg t)

/-- A valid certificate of kind `κ` for `a` of layer `ℓ`. -/
def ValidCert (f : ℕ) (κ : CertKind) (ℓ : ℕ) (a : Bool) (σ : Term n k) : Prop :=
  Valid f (.cert κ ℓ a σ)

/-- A valid input justification of `p` for `a` in layer `ℓ` (a valid justification for `a` from
layer `ℓ − 1`). -/
def ValidJust (f : ℕ) (p : Fin n) (ℓ : ℕ) (a : Bool) (J : Term n k) : Prop :=
  Valid f (.just p ℓ a J)

/-- The corrupt set `D_X`: the parties proved corrupt by `X`. -/
noncomputable def corruptSet (f : ℕ) (X : Term n k) : Finset (Fin n) := corruptSetV (Valid f) X

/-- Conflicting (valid) certificates of layer `ℓ`. -/
def Conflicting (f : ℕ) (ℓ : ℕ) (σ σ' : Term n k) : Prop := ConflictingV (Valid f) ℓ σ σ'

end ByzSigT


