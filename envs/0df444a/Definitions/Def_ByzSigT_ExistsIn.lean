-- Prove2me | Definitions.Def_ByzSigT_ExistsIn
-- name    : ByzSigT_ExistsIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:05.943195+00:00
-- url     : https://prove2.me/theorems/ebb564b3-fca2-498e-8aab-275d1add0b79
-- title:
--   Existence of messages and the vocabulary of the analysis
-- statement:
--   A message $m$ **exists** in an execution $E$ when some correct party receives a term containing $m$ during $E$ before terminating. A certificate exists when each of its messages exists.
--
--   This definition also collects the notions the milestones use: a party multicasts a message; a party outputs $(\mathrm{type},a,J)$ from a layer, with its blame and used tokens at that moment; a party enters a layer; a party receives a certificate; a justification from layer $j$, which is an input justification for layer $j+1$; its type; the set $\mathrm{equivSenders}$ and the $V3$ certificates selected on line 63; the use of line 56; and the sequence
--
--   $$T_1=0,\qquad T_{i+1}=n-2f+2T_i .$$
--
--   These are the terms of the analysis in §4.2, in the paper's own sense.
--
--   **Formalization Note** $T_i$ takes values in $\mathbb Z$. "Contains" is the subterm relation.
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), §4.2, Nomenclature, p.15 (PDF 16); analysis preamble, p.18 (PDF 19)

import Mathlib
import Definitions.Def_ByzSigT_kSigT
import Definitions.Def_ByzSigT_Secure

open Classical

namespace ByzSigT

/-!
# Vocabulary of the analysis of the k-SigT protocol

Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…), §4.2, p.15 (PDF 16), "Nomenclature", verbatim:

> For a protocol Π, a message m, and an execution E of Π, which is entirely determined by the
> adversary and their choices of corrupt parties, their behavior, GST, and network delays, we say
> that m exists in execution E if there exists a correct party that receives m during E before
> terminating.

and the analysis preamble, p.18 (PDF 19): "Define T_1 = 0 and T_{i+1} = n − 2f + 2T_i, so that
T_i = (2^{i−1} − 1)(n − 2f) … For a certificate or justification X, its corrupt set D_X is the set of
parties proved corrupt by X. A justification from layer j is an input justification for layer
j + 1."

All notions are about an execution `E` of `kSigT n f k Δ` with corrupt set `F` and inputs `u`.

**Formalization Note.**
* "Receives `m`" includes receiving a term in which `m` occurs. A certificate (a tuple of messages
  assembled by its holder) exists when each of its messages exists; `Present E X` says that `X`
  exists or is a tuple of messages that each exist.
* "Contains" is the subterm relation. "A justification for `a` from layer `j`" is a valid input
  justification for `a` in layer `j + 1` of some party (`IsJustFrom`); its type is read off its
  encoding.
* `equivSenders J` are the signers of the `n − f` messages of `J`; `SelectedV3 J c τ` says that
  `τ` is the `V3_c` certificate selected in `J` on line 63; `UsesLine56 J` that `J` is a tally
  justification from layer `k ≥ 2` containing a valid allgood certificate of layer `k − 1`.
* Outputs, layer entry and the token use at an output are read from the protocol state
  (`kState`): the output log `outputs`, the current `layer`, and the `used` set recorded with each
  output. The blame at an output is the corrupt set of the recorded blame tuple.
* `T n f i` is `T_i` in `ℤ` (`T 0` is not used).
-/

variable {n k : ℕ}

/-- The state of party `p` just before position `j` of `E` (running `kSigT n f k Δ`). -/
noncomputable def kState (f : ℕ) (Δ : ℝ) (u : Fin n → Bool) (E : Execution n k) (p : Fin n)
    (j : ℕ) : KState n k :=
  E.stateAt (kSigT n f k Δ) u p j

/-- `m` exists in `E`: some correct party receives a term containing `m` before terminating. -/
def ExistsIn (f : ℕ) (Δ : ℝ) (F : Finset (Fin n)) (u : Fin n → Bool) (E : Execution n k)
    (m : Term n k) : Prop :=
  ∃ p ∉ F, ∃ (j : ℕ) (src : Fin n) (s : Term n k), E.ev j = .deliver src p s ∧
    Term.Subterm m s ∧ (kState f Δ u E p j).terminated = false

/-- `X` exists in `E`, or is a tuple of messages that each exist in `E`. -/
def Present (f : ℕ) (Δ : ℝ) (F : Finset (Fin n)) (u : Fin n → Bool) (E : Execution n k)
    (X : Term n k) : Prop :=
  ExistsIn f Δ F u E X ∨ ∃ ms : List (Term n k), X = .list ms ∧ ∀ m ∈ ms, ExistsIn f Δ F u E m

/-- A valid certificate of kind `κ` for `a` of layer `ℓ` exists in `E`. -/
def CertExists (f : ℕ) (Δ : ℝ) (F : Finset (Fin n)) (u : Fin n → Bool) (E : Execution n k)
    (κ : CertKind) (ℓ : ℕ) (a : Bool) : Prop :=
  ∃ ms : List (Term n k), ValidCert f κ ℓ a (.list ms) ∧ ∀ m ∈ ms, ExistsIn f Δ F u E m

/-- Party `p` multicasts `m` (sends it to every party in one step). -/
def Multicasts (f : ℕ) (Δ : ℝ) (u : Fin n → Bool) (E : Execution n k) (p : Fin n)
    (m : Term n k) : Prop :=
  ∃ j, ∀ q : Fin n, Action.send q m ∈ E.actionsAt (kSigT n f k Δ) u p j

/-- `r` is an output record of party `p` in `E`. -/
def OutputRec (f : ℕ) (Δ : ℝ) (u : Fin n → Bool) (E : Execution n k) (p : Fin n)
    (r : OutRec n k) : Prop :=
  ∃ j, r ∈ (kState f Δ u E p j).outputs

/-- Party `p` outputs `(ty, a, J)` from layer `ℓ`. -/
def Outputs (f : ℕ) (Δ : ℝ) (u : Fin n → Bool) (E : Execution n k) (p : Fin n) (ℓ : ℕ)
    (ty : JType) (a : Bool) (J : Term n k) : Prop :=
  ∃ r, OutputRec f Δ u E p r ∧ r.layer = ℓ ∧ r.type = ty ∧ r.value = a ∧ r.just = J

/-- Party `p` enters layer `ℓ`. -/
def EntersLayer (f : ℕ) (Δ : ℝ) (u : Fin n → Bool) (E : Execution n k) (p : Fin n) (ℓ : ℕ) :
    Prop :=
  ∃ j, (kState f Δ u E p j).layer = ℓ

/-- Party `p` multicasts an allgood or equiv message (signed by itself) of layer `ℓ`. -/
def MulticastsAgEq (f : ℕ) (Δ : ℝ) (u : Fin n → Bool) (E : Execution n k) (p : Fin n) (ℓ : ℕ) :
    Prop :=
  ∃ m : Term n k, ((∃ a, IsAllgoodOf p ℓ a m) ∨ IsEquivOf p ℓ m) ∧ Multicasts f Δ u E p m

/-- Party `p` receives a term containing `m`. -/
def Receives (E : Execution n k) (p : Fin n) (m : Term n k) : Prop :=
  ∃ (j : ℕ) (src : Fin n) (s : Term n k), E.ev j = .deliver src p s ∧ Term.Subterm m s

/-- Party `p` receives (all messages of) a valid certificate of kind `κ` for `a` of layer `ℓ`. -/
def ReceivesCert (f : ℕ) (E : Execution n k) (p : Fin n) (κ : CertKind) (ℓ : ℕ) (a : Bool) :
    Prop :=
  ∃ ms : List (Term n k), ValidCert f κ ℓ a (.list ms) ∧ ∀ m ∈ ms, Receives E p m

/-- `T_i`: `T_1 = 0`, `T_{i+1} = n − 2f + 2 T_i`. -/
def T (n f : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | i + 2 => (n : ℤ) - 2 * f + 2 * T n f (i + 1)

/-- `J` is a valid justification for `a` from layer `j` (an input justification for `a` in layer
`j + 1` of some party). -/
def IsJustFrom (f : ℕ) (J : Term n k) (j : ℕ) (a : Bool) : Prop :=
  ∃ q : Fin n, ValidJust f q (j + 1) a J

/-- `J` has type `ty`. -/
def JustTypeIs (J : Term n k) (ty : JType) : Prop :=
  ∃ (j : ℕ) (a : Bool) (own bl : Term n k) (ms : List (Term n k)) (ex : Term n k),
    J = justTerm j a ty own bl ms ex

/-- `equivSenders` of `J`: the signers of its `n − f` messages. -/
def equivSenders (J : Term n k) : Finset (Fin n) :=
  match J with
  | .list [_, _, _, _, _, _, msl, _] => certSigners msl
  | _ => ∅

/-- `τ` is the `V3_c` certificate selected in `J` (line 63). -/
def SelectedV3 (J : Term n k) (c : Bool) (τ : Term n k) : Prop :=
  ∃ (j : ℕ) (a : Bool) (ty : JType) (own bl : Term n k) (ms : List (Term n k))
    (vs₀ τ₀ vs₁ τ₁ : Term n k),
    J = justTerm j a ty own bl ms (.list [.nat 3, vs₀, τ₀, vs₁, τ₁]) ∧ τ = (if c then τ₁ else τ₀)

/-- `J` is a tally justification from layer `k` that uses line 56. -/
def UsesLine56 (f : ℕ) (J : Term n k) : Prop :=
  JustTypeIs J .tally ∧ 2 ≤ k ∧
    (∃ (a : Bool) (own bl : Term n k) (ms : List (Term n k)) (ex : Term n k),
      J = justTerm k a .tally own bl ms ex) ∧
    ∃ (σ : Term n k) (c : Bool), Term.ProperSubterm σ J ∧ ValidCert f .allgood (k - 1) c σ

/-- `X` contains a valid allgood certificate for `b` from layer `j`. -/
def ContainsAllgood (f : ℕ) (X : Term n k) (j : ℕ) (b : Bool) : Prop :=
  ∃ σ : Term n k, Term.Subterm σ X ∧ ValidCert f .allgood j b σ

end ByzSigT


