-- Prove2me | Definitions.Def_FreshSig_Layered_Term
-- name    : FreshSig_Layered_Term
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:41:16.340381+00:00
-- url     : https://prove2.me/theorems/7d9d96cb-d53d-4adc-886f-befe46b40844
-- title:
--   Symbolic terms, structural subterms $\mathrm{Sub}$, the public closure $\mathrm{DY}$, nonces and symbolic vector commitments (Appendix A.1, A.5)
-- statement:
--   All cryptography is symbolic (Dolev–Yao). A **term** is a public constant, a party identity $i$, a fresh atom, a tuple $(t_1,\dots,t_k)$, an ideal signature $\langle m\rangle_i$ of party $i$ on $m$, a leaf $\mathrm{leaf}(t)$, a commitment root $\mathrm{root}_\ell(V)$ of depth $\ell$ of a vector $V=(v_1,\dots,v_n)$ whose entries are terms or $\bot$, or an opening proof for a coordinate of such a root; we write $\mathrm{leaf}(g,\nu)=\mathrm{leaf}((g,\nu))$. Constructors of different kinds never coincide.
--
--   A term $a$ is a **structural subterm** of $b$ ("$a$ occurs in $b$") if $a=b$ or $a$ occurs in a component of the tuple, signature, leaf, root or proof $b$; in particular the message of a signature and every non-$\bot$ entry of a committed vector occur in it. $\mathrm{Sub}(S)$ is the set of structural subterms of members of $S$.
--
--   Roots are **typed by depth**: a root of depth $0$ commits to $n$ entries that are leaves or $\bot$, a root of depth $\ell>0$ to $n$ entries that are roots of depth $\ell-1$ or $\bot$.
--
--   The **public closure** $\mathrm{DY}(K)$ of a set $K$ of terms is the least set containing $K$ and all public constants and identities, closed under: forming tuples; projecting a component of a tuple; reading the identity and the message of a signature; wrapping a term in a leaf; computing a well-typed root and its opening proofs from a vector of available entries. No rule creates an atom or a signature, opens a leaf, or extracts an entry from a root or proof. A term $\nu$ is a **nonce** relative to $K$ iff
--   $$\nu\notin \mathrm{Sub}(\mathrm{DY}(K)).$$
--   $\mathrm{OpenVerify}(\rho,j,v,\pi)$ accepts exactly when $\rho$ is a root whose coordinate $j$ is $v$ ($v$ may be $\bot$) and $\pi$ is the proof of that coordinate; a root therefore opens to at most one value per coordinate. $\mathrm{Verify}(i,m,\sigma)=1$ iff $\sigma=\langle m\rangle_i$.
--
--   These are the objects of the symbolic model in which the paper's freshness arguments are carried out: a root contains its entries although nobody can extract them again (the causal idealisation of Example A.11).
--
--   **Formalization Note** `Term` is an inductive type with constructors `cst`, `pid`, `atom`, `tup`, `sig`, `ext`, `leaf`, `root ℓ V`, `prf ℓ V j`, with `V : List (Option Term)` (`none` = $\bot$). `ext k i x` is the output of an additional protected interface (such as the counter-bound signer of Example A.7); no public rule creates or opens it. `Occurs`, `Sub`, `IsRoot n ℓ`, `TypedVec`, `DY n K` (an inductive predicate whose rules are exactly the public rules above), `IsNonce`, `OpenVerify` and `SigVerify` follow the text. Party identities are public constants. Roots carry their depth and vector (the explicit-vector realisation of Example A.10), not an invocation tag.
-- source:
--   Lenzen, Loss, Shi, Fresh Signatures without Fresh Keys, STOC 2027 submission (manuscript sha256 ac05cb97…), pp. 54–55, Appendix A.1; p. 62, Appendix A.5 (symbolic vector commitments, Examples A.10, A.11); p. 12, §2.4

import Mathlib

/-!
# Symbolic terms, structural subterms, the public closure DY and nonces

Lenzen, Loss, Shi, *Fresh Signatures without Fresh Keys*, STOC 2027 submission,
Appendix A.1 (pp. 54–55), symbolic vector commitments of Appendix A.5 (p. 62) and §2.4 (p. 12).

Parties are indexed `0, …, n - 1` (the paper's `P₁, …, Pₙ`); coordinate `j` of a committed
vector belongs to party `j`. The entries of a committed vector are `Option Term`, with `none`
for the paper's `⊥`.
-/

namespace FreshSig.Layered

/-- Symbolic terms (Appendix A.1). Constructors of different types have disjoint ranges.
* `cst c` — a public constant (the reserved tags such as `LF` are public constants);
* `pid i` — the public identity of party `i`;
* `atom a` — a fresh atom;
* `tup ts` — a tuple;
* `sig i m` — the ideal signature `⟨m⟩ᵢ` of party `i` on `m`;
* `ext k i x` — the output of another protected interface `k` of party `i` on `x`
  (for instance the counter-bound signer of Example A.7); no public rule creates or opens it;
* `leaf t` — a leaf `leaf(t)`;
* `root ℓ V` — the commitment root of depth `ℓ` of the vector `V` (`none` = `⊥`);
* `prf ℓ V j` — the opening proof of coordinate `j` of `root ℓ V`. -/
inductive Term : Type where
  | cst : String → Term
  | pid : ℕ → Term
  | atom : ℕ → Term
  | tup : List Term → Term
  | sig : ℕ → Term → Term
  | ext : ℕ → ℕ → Term → Term
  | leaf : Term → Term
  | root : ℕ → List (Option Term) → Term
  | prf : ℕ → List (Option Term) → ℕ → Term

/-- The reserved public tag `LF` of the layered scheme's signed statements (p. 55, p. 15). -/
def LF : Term := Term.cst "LF"

/-- `leaf(g, ν) := leaf((g, ν))` (p. 62). -/
def leafOf (g ν : Term) : Term := Term.leaf (Term.tup [g, ν])

/-- Structural subterms (p. 54): `Occurs a b` says that `a` is a structural subterm of `b`
("`a` occurs in `b`"). A term occurs in itself and, recursively, in any tuple, signature, leaf,
root or proof that contains it; in particular the message of a signature and every non-`⊥`
entry of a committed vector occur in it. -/
inductive Occurs : Term → Term → Prop where
  | refl (t : Term) : Occurs t t
  | tup {a t : Term} {ts : List Term} : t ∈ ts → Occurs a t → Occurs a (Term.tup ts)
  | sigId (i : ℕ) (m : Term) : Occurs (Term.pid i) (Term.sig i m)
  | sig {a : Term} (i : ℕ) {m : Term} : Occurs a m → Occurs a (Term.sig i m)
  | extId (k i : ℕ) (x : Term) : Occurs (Term.pid i) (Term.ext k i x)
  | ext {a : Term} (k i : ℕ) {x : Term} : Occurs a x → Occurs a (Term.ext k i x)
  | leaf {a t : Term} : Occurs a t → Occurs a (Term.leaf t)
  | root {a t : Term} {ℓ : ℕ} {V : List (Option Term)} :
      some t ∈ V → Occurs a t → Occurs a (Term.root ℓ V)
  | prf {a t : Term} {ℓ : ℕ} {V : List (Option Term)} {j : ℕ} :
      some t ∈ V → Occurs a t → Occurs a (Term.prf ℓ V j)

/-- `Sub(S)`: all structural subterms of terms of `S`. -/
def Sub (S : Set Term) : Set Term := {a | ∃ b ∈ S, Occurs a b}

/-- Typing of committed entries: an entry of a depth-`ℓ` vector is `⊥`, a leaf if `ℓ = 0`, or a
root of depth `ℓ - 1` if `ℓ > 0` (p. 62). `IsRoot n ℓ t`: `t` is a root of depth `ℓ` of a vector of
`n` entries, each correctly typed. -/
inductive IsRoot (n : ℕ) : ℕ → Term → Prop where
  | zero (V : List (Option Term)) (hlen : V.length = n)
      (hV : ∀ t : Term, some t ∈ V → ∃ u, t = Term.leaf u) : IsRoot n 0 (Term.root 0 V)
  | succ (ℓ : ℕ) (V : List (Option Term)) (hlen : V.length = n)
      (hV : ∀ t : Term, some t ∈ V → IsRoot n ℓ t) : IsRoot n (ℓ + 1) (Term.root (ℓ + 1) V)

/-- A well-typed vector of depth `ℓ`: `n` entries, each `⊥` or of the type required at depth
`ℓ` (a leaf if `ℓ = 0`, a root of depth `ℓ - 1` otherwise). -/
def TypedVec (n ℓ : ℕ) (V : List (Option Term)) : Prop :=
  V.length = n ∧ ∀ t : Term, some t ∈ V →
    (ℓ = 0 → ∃ u, t = Term.leaf u) ∧ (0 < ℓ → IsRoot n (ℓ - 1) t)

/-- The public closure `DY(K)` (p. 54): the least set containing `K` and all public constants
(constants and party identities) closed under the public construction and inspection rules:
forming and projecting tuples, reading the identity and the message of a signature, wrapping an
available term in a leaf, and computing a commitment root and its opening proofs from an
available well-typed vector. There is no rule that creates a fresh atom, a signature or another
protected-interface output, that opens a leaf, or that extracts an entry from a root or a proof. -/
inductive DY (n : ℕ) (K : Set Term) : Term → Prop where
  | base {t : Term} : t ∈ K → DY n K t
  | cst (c : String) : DY n K (Term.cst c)
  | pid (i : ℕ) : DY n K (Term.pid i)
  | tup {ts : List Term} : (∀ t ∈ ts, DY n K t) → DY n K (Term.tup ts)
  | proj {ts : List Term} {t : Term} : DY n K (Term.tup ts) → t ∈ ts → DY n K t
  | sigId {i : ℕ} {m : Term} : DY n K (Term.sig i m) → DY n K (Term.pid i)
  | sigMsg {i : ℕ} {m : Term} : DY n K (Term.sig i m) → DY n K m
  | leaf {t : Term} : DY n K t → DY n K (Term.leaf t)
  | root {ℓ : ℕ} {V : List (Option Term)} : TypedVec n ℓ V →
      (∀ t : Term, some t ∈ V → DY n K t) → DY n K (Term.root ℓ V)
  | prf {ℓ : ℕ} {V : List (Option Term)} {j : ℕ} : TypedVec n ℓ V → j < V.length →
      (∀ t : Term, some t ∈ V → DY n K t) → DY n K (Term.prf ℓ V j)

/-- Symbolic nonces (p. 55): `ν` is a nonce relative to `K` iff `ν ∉ Sub(DY(K))`. -/
def IsNonce (n : ℕ) (K : Set Term) (ν : Term) : Prop := ν ∉ Sub {t | DY n K t}

/-- `OpenVerify(ρ, j, v, π)` (p. 62): accepts precisely valid proofs that coordinate `j` of the
root `ρ` is `v` (`v = none` is the entry `⊥`). A missing proof (`π = none`) is rejected. -/
def OpenVerify (ρ : Term) (j : ℕ) (v : Option Term) (π : Option Term) : Prop :=
  ∃ (ℓ : ℕ) (V : List (Option Term)), ρ = Term.root ℓ V ∧ V[j]? = some v ∧
    π = some (Term.prf ℓ V j)

/-- `Commit(V)` (p. 62): the root `root(V)` of depth `ℓ` and the proofs of its `n` coordinates. -/
def commit (ℓ : ℕ) (V : List (Option Term)) : Term × List (Option Term) :=
  (Term.root ℓ V, (List.range V.length).map (fun j => some (Term.prf ℓ V j)))

/-- The ideal test `Verify(i, m, σ)` (p. 55): accepts exactly `σ = ⟨m⟩ᵢ`. -/
def SigVerify (i : ℕ) (m σ : Term) : Prop := σ = Term.sig i m

end FreshSig.Layered


