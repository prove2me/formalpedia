-- Prove2me | Definitions.Def_EarlyStoppingEIG_Exact_Authentication
-- name    : EarlyStoppingEIG_Exact_Authentication
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:55.777041+00:00
-- url     : https://prove2.me/theorems/074f7ccd-c54a-41ec-82bd-de917d71779f
-- title:
--   Ideal signatures and public term derivation
-- statement:
--   For any identity type, wire terms consist of public atoms, finite tuples and signed payloads with an owner and signature label. An occurrence relation makes nested signed evidence readable. The ideal authentication rule permits public construction and replay, and permits a new signature only with a key already corrupted:
--
--   $$\text{new signature under }j\text{ is derivable only after corruption of }j.$$
--
--   This is the source’s perfect correctness and unforgeability idealization, not a computational security claim. It supplies no common election, secret correlated setup or efficiency bound. Signature labels preserve the identity of exact signed receipts.
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), §2, p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Mathlib

namespace EarlyStoppingEIG.Exact

/-- Finite wire terms for the ideal signature model of §2, p.15.
The natural label distinguishes different signatures on the same payload.
`atom` and `tuple` also permit arbitrary malformed wire data. Public keys are
identified by their authenticated owner; possession of a key is represented by
the corruption event, not by a trusted setup or a static faulty set. -/
inductive AuthTerm (ι : Type) where
  | atom : ℕ → AuthTerm ι
  | tuple : List (AuthTerm ι) → AuthTerm ι
  | sig : ι → ℕ → AuthTerm ι → AuthTerm ι

/-- Occurrence includes a signed term itself and all readable nested contents. -/
inductive Occurs {ι : Type} : AuthTerm ι → AuthTerm ι → Prop where
  | refl (m) : Occurs m m
  | tuple {m a xs} : a ∈ xs → Occurs m a → Occurs m (.tuple xs)
  | sig {m j q a} : Occurs m a → Occurs m (.sig j q a)

/-- Public construction and replay, with new signatures available only under
keys already corrupted. A signature inside a known term can be extracted and
copied, but no constructor strips its owner or changes its payload. -/
inductive Derivable {ι : Type} (keys : Set ι) (known : Set (AuthTerm ι)) :
    AuthTerm ι → Prop where
  | atom (a) : Derivable keys known (.atom a)
  | extract {m a} : a ∈ known → Occurs m a → Derivable keys known m
  | tuple {xs} : (∀ a ∈ xs, Derivable keys known a) → Derivable keys known (.tuple xs)
  | sign {j q a} : j ∈ keys → Derivable keys known a → Derivable keys known (.sig j q a)

end EarlyStoppingEIG.Exact


