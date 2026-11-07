-- Prove2me | Definitions.Def_ByzSigT_Term
-- name    : ByzSigT_Term
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:51:40.774505+00:00
-- url     : https://prove2.me/theorems/123739b1-765c-43e0-bfa1-871773e1e786
-- title:
--   Message terms with ideal signatures and signature tokens, and derivability
-- statement:
--   Messages of an $n$-party protocol with a $k$-SigT setup are symbolic **terms**. A term is a natural-number constant, a tuple of terms, a PKI signature $\mathrm{sig}_q(t)$ of party $q$ on a term $t$, or a token $\mathrm{SigT}^{(i)}_q(t)$: the environment's signature on $(t,q,i)$. A term is a **subterm** of another when it occurs inside it, including inside the signed content of a signature or a token.
--
--   A term $t$ is **derivable** from a set of terms $K$ by a party that signs for the parties in $S$ and obtains tokens for the parties in $T$ when it is built by the following rules:
--
--   1. every member of $K$ and every constant is derivable;
--   2. a tuple of derivable terms is derivable;
--   3. every subterm of a derivable term is derivable, so tuples can be split and signed contents read;
--   4. if $t$ is derivable, then so are $\mathrm{sig}_q(t)$ for $q\in S$ and $\mathrm{SigT}^{(i)}_q(t)$ for $q\in T$.
--
--   No rule produces a signature of a party outside $S$ or a token of a party outside $T$: those can only be copied from $K$.
--
--   This is the layer that makes unforgeability and readability of signatures precise for the whole mission. A correct party $p$ uses $S=\{p\}$, $T=\emptyset$; the adversary uses $S=T=F$, the corrupt set.
--
--   **Formalization Note** `tok q i t` has `i : Fin k` and stands for the paper's $\mathrm{SigT}^{(i+1)}_q(t)$. Token uniqueness for corrupt parties is a condition on executions, not on derivability.
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), §2, pp.4–5 (PDF 5–6); §1.2, p.3 (PDF 4)

import Mathlib

namespace ByzSigT

/-!
# Message terms with ideal signatures and signature tokens

Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…), §2 "Model" and "SigT setup", pp.4–5, and §1.2, p.3
("Our model treats the SigT as a black box").

**Formalization Note.** Messages are symbolic terms over `n` parties `Fin n` and `k` token
indices `Fin k`:
* `nat c` is a natural-number constant (tags, layers, views, the values `0, 1`);
* `list ts` is a tuple or a set of terms;
* `sig q t` is party `q`'s PKI signature on `t`;
* `tok q i t` is the environment's signature on `(t, q, i + 1)`, i.e. the paper's
  `SigT^{(i+1)}_q(t)`: the token index `i : Fin k` is the paper's index `i + 1 ∈ {1, …, k}`.

The cryptography is ideal: a signature is unforgeable and hides nothing (the signed content `t`
is readable from `sig q t` and `tok q i t`). This is the paper's own idealization (its proofs treat
"proved corrupt" as certain, Theorem 4.1 has no negligible-error term, and §1.2 black-boxes the
SigT). The security parameter λ of p.4 plays no role.

`Derivable S T K t` says that `t` can be computed from the set of terms `K` by a party able to
sign with the PKI keys of the parties in `S` and to obtain tokens of the parties in `T`: by taking
members of `K`, constants, building tuples, decomposing any term into its subterms (including
reading signed contents), and signing. No rule produces `sig q _` for `q ∉ S` or `tok q _ _` for
`q ∉ T`: such terms come only from `K`.
-/

/-- Symbolic message terms (see the module note). `tok q i t` is `SigT^{(i+1)}_q(t)`. -/
inductive Term (n k : ℕ) : Type where
  /-- A natural-number constant. -/
  | nat (c : ℕ) : Term n k
  /-- A tuple (or a collection) of terms. -/
  | list (ts : List (Term n k)) : Term n k
  /-- Party `q`'s PKI signature on `t`. -/
  | sig (q : Fin n) (t : Term n k) : Term n k
  /-- The environment's token signature `SigT^{(i+1)}_q(t)` on `(t, q, i + 1)`. -/
  | tok (q : Fin n) (i : Fin k) (t : Term n k) : Term n k

namespace Term

variable {n k : ℕ}

/-- `Child s t`: `s` is an immediate component of `t` (an entry of a tuple, or the content of a
signature or a token). -/
inductive Child : Term n k → Term n k → Prop where
  | list {t : Term n k} {ts : List (Term n k)} : t ∈ ts → Child t (list ts)
  | sig (q : Fin n) (t : Term n k) : Child t (sig q t)
  | tok (q : Fin n) (i : Fin k) (t : Term n k) : Child t (tok q i t)

/-- `Subterm s t`: `s` occurs in `t` (reflexive–transitive closure of `Child`). -/
def Subterm (s t : Term n k) : Prop := Relation.ReflTransGen Child s t

/-- `ProperSubterm s t`: `s` occurs in `t` and `s ≠ t` as an occurrence (transitive closure of
`Child`). -/
def ProperSubterm (s t : Term n k) : Prop := Relation.TransGen Child s t

/-- The signer of a signed term: `q` for `sig q _` and for `tok q _ _`. -/
def signer : Term n k → Option (Fin n)
  | sig q _ => some q
  | tok q _ _ => some q
  | _ => none

end Term

/-- Derivability of a term from knowledge `K` by a party that can sign for the parties in `S`
and produce tokens for the parties in `T` (see the module note). An honest party `p` uses
`S = {p}`, `T = ∅`, and `K` = the terms it received plus its own token replies; the adversary uses
`S = T = F` (the corrupt set). -/
inductive Derivable {n k : ℕ} (S T : Finset (Fin n)) (K : Set (Term n k)) : Term n k → Prop where
  | mem {t : Term n k} : t ∈ K → Derivable S T K t
  | nat (c : ℕ) : Derivable S T K (.nat c)
  | list {ts : List (Term n k)} : (∀ t ∈ ts, Derivable S T K t) → Derivable S T K (.list ts)
  | sub {s t : Term n k} : Derivable S T K t → Term.Subterm s t → Derivable S T K s
  | sig {q : Fin n} {t : Term n k} : q ∈ S → Derivable S T K t → Derivable S T K (.sig q t)
  | tok {q : Fin n} {t : Term n k} (i : Fin k) : q ∈ T → Derivable S T K t →
      Derivable S T K (.tok q i t)

end ByzSigT


