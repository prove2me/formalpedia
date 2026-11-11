-- Prove2me | Definitions.Def_FreshSig_Layered_Execution
-- name    : FreshSig_Layered_Execution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:41:49.827441+00:00
-- url     : https://prove2.me/theorems/c42cd5e2-d7cf-4116-86cc-0eca78008250
-- title:
--   Synchronous executions, the record $K(h)$, first issue, corruption, and the nonce and commitment routines (Definitions A.5, A.9)
-- statement:
--   An **execution** is a sequence of synchronous rounds $r=0,1,2,\dots$, each a finite, ordered list of **events**: generating a fresh atom; a call $\mathrm{Sign}_i(x)$, returning $\langle x\rangle_i$; a call of another protected interface; any other computation, input, transmission or reception of a term; the corruption of a party; a party invoking the nonce routine or obtaining its output; a party invoking the commitment routine with label $g$, depth $\ell$ and input $v$, or obtaining its output $(V,\rho,\pi)$; a party outputting the lists $(R,A)$ of refresh; and a party accepting $\hat\sigma$ as a signature of origin $i$ on $m$ at depth $q$ in the epoch with label $g$. Positions $(r,k)$ are ordered lexicographically.
--
--   The **record** $K(h)$ of the prefix $h$ before a position is the set of all terms generated, computed or supplied by the events of $h$, by anyone, preparation phase included; it only grows. A term **occurs by** $h$ iff it lies in $\mathrm{Sub}(K(h))$. The **first issue** of a term is the first event that creates it; for $\langle x\rangle_i$ this is the first call $\mathrm{Sign}_i(x)$.
--
--   The **symbolic rules** (Admissible): every term an event uses lies in $\mathrm{DY}(K(h))$ for the prefix $h$ before it, and a generated atom lies outside $\mathrm{Sub}(K(h))$. Only signing calls create signatures; anyone may make them, at any time.
--
--   A party $i$ is **correct up to** a position $p$ in the execution phase (round $\tau_0$ or later) if no event corrupts it in the execution phase up to $p$; corruption in the preparation phase does not count.
--
--   **Definition A.5 (nonce routine)**, label $g$, duration $t_N$: a correct party that invokes it and stays correct for $t_N$ rounds obtains an output within $t_N$ rounds; every output $\nu_i$ at a correct party is a nonce relative to $K(h_i)$, $h_i$ the prefix before the invocation (freshness at every correct party, §2.4); one output per invocation.
--
--   **Definition A.9 (commitment routine)**, label $g$, duration $t_C$: a correct party that invokes it with depth $\ell$ and input $v_i$ and stays correct for $t_C$ rounds obtains an output within $t_C$ rounds; every output $(V_i,\rho_i,\pi_i)$ of a correct party satisfies $\rho_i=\mathrm{root}_\ell(V_i)$; *input validity*: every entry is $\bot$ or of the required type (a leaf if $\ell=0$, a root of depth $\ell-1$ otherwise) and $v_{i,k}\in\{v_k,\bot\}$ for every party $k$ correct at that output that invoked with input $v_k$; *self-inclusion* $v_{i,i}=v_i$; *opening correctness* $\mathrm{OpenVerify}(\rho_i,k,v_{i,k},\pi_{i,k})=1$ for every $k$; one output per invocation. No delivery is guaranteed (channels may drop messages).
--
--   **Formalization Note** `Execution := ℕ → List Event`; `evAt tr (r, k)` is the $k$-th event of round $r$; `record tr p` is the record of the prefix strictly before `p`, and the prefix $h_0$ before the common start is `record tr (τ₀, 0)`. `FirstIssue`, `Admissible`, `CorrectAt`, `CorrectThrough`, `NonceRoutine`, `CommitRoutine` follow the text; party indices are $0,\dots,n-1$.
-- source:
--   Lenzen, Loss, Shi, Fresh Signatures without Fresh Keys, STOC 2027 submission (manuscript sha256 ac05cb97…), p. 55, Appendix A.1 (executions, record, occurrence, first issue); pp. 58–59, Appendix A.3; p. 60, Definition A.5; pp. 62–63, Definition A.9; p. 13, §3.1; p. 12, §2.4

import Mathlib
import Definitions.Def_FreshSig_Layered_Term

/-!
# Synchronous executions, the record `K(h)`, first issue, corruption, and the helper routines

Lenzen, Loss, Shi, *Fresh Signatures without Fresh Keys*, STOC 2027 submission,
Appendix A.1 (executions, record, occurrence, first issue; pp. 54–55), A.3 (network,
corruption, precorruption; pp. 58–59), A.5 (Definitions A.5 and A.9; pp. 60–63) and §3.1 (p. 13).

An execution is a sequence of synchronous rounds `r = 0, 1, 2, …`, each a finite list of events
in the order in which they happen. Rounds before the common start `τ₀` are the preparation
phase (and whatever else precedes the epoch): nothing restricts them beyond the symbolic rules.
-/

namespace FreshSig.Layered

/-- Local forwarding record `aℓ = (Vℓ, πℓ)` (p. 56): the collected vector and its proofs, with
`none` for a missing entry or proof (`⊥`). -/
abbrev FwdRecord : Type := List (Option Term) × List (Option Term)

/-- Events of an execution.
* `gen a` — fresh-atom generation, returning `atom a`;
* `signCall i x` — a call `Signᵢ(x)` (by anyone with access), returning `⟨x⟩ᵢ`;
* `extCall k i x` — a call of another protected interface `k` of party `i`, returning `ext k i x`;
* `handle t` — any other local computation, input, advice, transmission or reception of `t`;
* `corrupt i` — the adversary corrupts party `i`;
* `nonceInv i g`, `nonceOut i g ν` — party `i` invokes the nonce routine / obtains its output
  `ν` (`none` = `⊥`) in the epoch with label `g`;
* `commitInv i g ℓ v`, `commitOut i g ℓ V ρ π` — party `i` invokes the commitment routine with
  label `g`, depth `ℓ` and input `v` / obtains its output `(V, ρ, π)`;
* `refreshOut i g R A` — party `i` outputs the lists `(R, A)` of the refresh with label `g`;
* `accept j g i m σ q` — party `j` accepts `σ` as a signature of origin `i` on `m` at depth `q`
  in the epoch with label `g` (its verification returned `1`). -/
inductive Event : Type where
  | gen (a : ℕ)
  | signCall (i : ℕ) (x : Term)
  | extCall (k i : ℕ) (x : Term)
  | handle (t : Term)
  | corrupt (i : ℕ)
  | nonceInv (i : ℕ) (g : Term)
  | nonceOut (i : ℕ) (g : Term) (ν : Option Term)
  | commitInv (i : ℕ) (g : Term) (ℓ : ℕ) (v : Term)
  | commitOut (i : ℕ) (g : Term) (ℓ : ℕ) (V : List (Option Term)) (ρ : Term)
      (π : List (Option Term))
  | refreshOut (i : ℕ) (g : Term) (R : List Term) (A : List FwdRecord)
  | accept (j : ℕ) (g : Term) (i : ℕ) (m σ : Term) (q : ℕ)

namespace Event

/-- The terms an event creates: only fresh-atom generation, signing calls and calls of other
protected interfaces create terms. -/
def created : Event → List Term
  | gen a => [Term.atom a]
  | signCall i x => [Term.sig i x]
  | extCall k i x => [Term.ext k i x]
  | _ => []

/-- The terms an event takes from what is already available (computed, received, input, or
passed to an interface). -/
def used : Event → List Term
  | gen _ => []
  | signCall _ x => [x]
  | extCall _ _ x => [x]
  | handle t => [t]
  | corrupt _ => []
  | nonceInv _ g => [g]
  | nonceOut _ g ν => g :: ν.toList
  | commitInv _ g _ v => [g, v]
  | commitOut _ g _ V ρ π => g :: ρ :: (V.filterMap id ++ π.filterMap id)
  | refreshOut _ g R A => g :: (R ++ A.flatMap (fun a => a.1.filterMap id ++ a.2.filterMap id))
  | accept _ g _ m σ _ => [g, m, σ]

/-- All terms generated, computed or supplied by the event. -/
def terms (e : Event) : List Term := e.used ++ e.created

end Event

/-- An execution: the list of events of every synchronous round, in order. -/
abbrev Execution : Type := ℕ → List Event

/-- A position `(r, k)`: the `k`-th event of round `r`. -/
abbrev Pos : Type := ℕ × ℕ

/-- Strict execution order on positions (lexicographic). -/
def PosLT (p q : Pos) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- Execution order on positions, non-strict. -/
def PosLE (p q : Pos) : Prop := PosLT p q ∨ p = q

/-- The event at a position, if any. -/
def evAt (tr : Execution) (p : Pos) : Option Event := (tr p.1)[p.2]?

/-- The finite execution prefix ending immediately before position `p`. -/
def prefixEvents (tr : Execution) (p : Pos) : List Event :=
  (List.range p.1).flatMap tr ++ (tr p.1).take p.2

/-- The cumulative record `K(h)` of the prefix `h` ending immediately before `p` (p. 55): all terms
generated, computed or supplied in it by any party or the adversary, the preparation phase
included. Nothing is ever removed. The record of the prefix before round `τ` is
`record tr (τ, 0)`. -/
def record (tr : Execution) (p : Pos) : Set Term :=
  {t | ∃ e ∈ prefixEvents tr p, t ∈ e.terms}

/-- `o` occurs by the prefix before `p` iff `o ∈ Sub(K(h))` (p. 55). -/
def OccursBefore (tr : Execution) (p : Pos) (o : Term) : Prop := o ∈ Sub (record tr p)

/-- The first issue of `σ` (p. 55): the event at `p` creates `σ` and no earlier event does. For an
ideal signature `⟨x⟩ᵢ` this is the first call `Signᵢ(x)`. -/
def FirstIssue (tr : Execution) (σ : Term) (p : Pos) : Prop :=
  (∃ e, evAt tr p = some e ∧ σ ∈ e.created) ∧
    ∀ p' : Pos, PosLT p' p → ∀ e, evAt tr p' = some e → σ ∉ e.created

/-- The symbolic execution rules (Appendix A.1): every term an event uses is in the public
closure `DY` of the record before it, and fresh-atom generation returns an atom outside all
previously occurring structural subterms. Only `Signᵢ` creates `⟨x⟩ᵢ`. Signing interfaces may be
called by anyone at any time, before and after the start. -/
def Admissible (n : ℕ) (tr : Execution) : Prop :=
  ∀ (p : Pos) (e : Event), evAt tr p = some e →
    (∀ t ∈ e.used, DY n (record tr p) t) ∧
    ∀ a : ℕ, e = Event.gen a → Term.atom a ∉ Sub (record tr p)

/-- Party `i` is correct up to the event at `p` (p. 58): `p` lies in the execution phase (round
`τ₀` or later) and `i` has not been corrupted in the execution phase up to and including `p`.
Corruptions during the preparation phase do not count. -/
def CorrectAt (tr : Execution) (τ₀ : ℕ) (i : ℕ) (p : Pos) : Prop :=
  PosLE (τ₀, 0) p ∧
    ∀ p' : Pos, PosLE (τ₀, 0) p' → PosLE p' p → evAt tr p' ≠ some (Event.corrupt i)

/-- Party `i` is not corrupted in rounds `τ₀, …, r`. -/
def CorrectThrough (tr : Execution) (τ₀ : ℕ) (i : ℕ) (r : ℕ) : Prop :=
  ∀ p' : Pos, τ₀ ≤ p'.1 → p'.1 ≤ r → evAt tr p' ≠ some (Event.corrupt i)

/-- Definition A.5 (nonce routine) in the epoch with label `g` and duration `tN`, with freshness
required at every correct party (§2.4). `hᵢ` is the prefix immediately preceding the invocation.
An invocation has a single output. -/
structure NonceRoutine (n : ℕ) (g : Term) (τ₀ tN : ℕ) (tr : Execution) : Prop where
  /-- Termination within `tN` rounds. -/
  termination : ∀ i < n, ∀ p : Pos, CorrectAt tr τ₀ i p → evAt tr p = some (Event.nonceInv i g) →
    CorrectThrough tr τ₀ i (p.1 + tN) →
    ∃ (p' : Pos) (ν : Term), PosLT p p' ∧ p'.1 ≤ p.1 + tN ∧
      evAt tr p' = some (Event.nonceOut i g (some ν))
  /-- Freshness: the output is a nonce relative to `K(hᵢ)`. -/
  freshness : ∀ i < n, ∀ (p p' : Pos) (ν : Option Term), CorrectAt tr τ₀ i p →
    evAt tr p = some (Event.nonceInv i g) → PosLT p p' → CorrectAt tr τ₀ i p' →
    evAt tr p' = some (Event.nonceOut i g ν) → ∃ t, ν = some t ∧ IsNonce n (record tr p) t
  /-- One output. -/
  single_output : ∀ i < n, ∀ (p p' : Pos) (ν ν' : Option Term), CorrectAt tr τ₀ i p →
    CorrectAt tr τ₀ i p' → evAt tr p = some (Event.nonceOut i g ν) →
    evAt tr p' = some (Event.nonceOut i g ν') → p = p'

/-- The guarantees of Definition A.9 for the output `(V, ρ, π)` at `p'` of a correct party `i`
that invoked the commitment routine with label `g`, depth `ℓ` and input `v`:
format `ρ = root(V)` with `n` proofs; input validity (every entry `⊥` or of the required type,
and `V[k] ∈ {v_k, ⊥}` for every party `k` correct at `p'` that invoked with input `v_k`);
self-inclusion `V[i] = v`; opening correctness `OpenVerify(ρ, k, V[k], π[k]) = 1` for every `k`. -/
def CommitOutputOK (n : ℕ) (tr : Execution) (τ₀ : ℕ) (g : Term) (i ℓ : ℕ) (v : Term)
    (V : List (Option Term)) (ρ : Term) (π : List (Option Term)) (p' : Pos) : Prop :=
  ρ = Term.root ℓ V ∧ π.length = n ∧ TypedVec n ℓ V ∧
  (∀ k < n, ∀ (pk : Pos) (vk : Term), CorrectAt tr τ₀ k pk →
      evAt tr pk = some (Event.commitInv k g ℓ vk) → CorrectAt tr τ₀ k p' →
      V[k]? = some (some vk) ∨ V[k]? = some none) ∧
  V[i]? = some (some v) ∧
  ∀ k < n, OpenVerify ρ k (V.getD k none) (π.getD k none)

/-- Definition A.9 (distributed commitment routine) in the epoch with label `g` and duration
`tC`. No delivery is guaranteed (channels may drop messages, §3.1). An invocation has a single
output. -/
structure CommitRoutine (n : ℕ) (g : Term) (τ₀ tC : ℕ) (tr : Execution) : Prop where
  /-- Termination within `tC` rounds. -/
  termination : ∀ i < n, ∀ (p : Pos) (ℓ : ℕ) (v : Term), CorrectAt tr τ₀ i p →
    evAt tr p = some (Event.commitInv i g ℓ v) → CorrectThrough tr τ₀ i (p.1 + tC) →
    ∃ (p' : Pos) (V : List (Option Term)) (ρ : Term) (π : List (Option Term)),
      PosLT p p' ∧ p'.1 ≤ p.1 + tC ∧ evAt tr p' = some (Event.commitOut i g ℓ V ρ π)
  /-- Format, input validity, self-inclusion and opening correctness. -/
  guarantees : ∀ i < n, ∀ (p p' : Pos) (ℓ : ℕ) (v : Term) (V : List (Option Term)) (ρ : Term)
    (π : List (Option Term)), CorrectAt tr τ₀ i p → evAt tr p = some (Event.commitInv i g ℓ v) →
    PosLT p p' → CorrectAt tr τ₀ i p' → evAt tr p' = some (Event.commitOut i g ℓ V ρ π) →
    CommitOutputOK n tr τ₀ g i ℓ v V ρ π p'
  /-- One output per depth. -/
  single_output : ∀ i < n, ∀ (p p' : Pos) (ℓ : ℕ) (V V' : List (Option Term)) (ρ ρ' : Term)
    (π π' : List (Option Term)), CorrectAt tr τ₀ i p → CorrectAt tr τ₀ i p' →
    evAt tr p = some (Event.commitOut i g ℓ V ρ π) →
    evAt tr p' = some (Event.commitOut i g ℓ V' ρ' π') → p = p'

end FreshSig.Layered


