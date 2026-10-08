-- Prove2me | Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
-- name    : GOSNIZK_BGNCommit_BGNSetup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:42.141095+00:00
-- url     : https://prove2.me/theorems/5e11e0b8-4673-4f61-9e5b-7a9dab37e8eb
-- title:
--   The BGN bilinear group $(p, q, \mathbb G, \mathbb G_T, e, g)$ of composite order $n = pq$ (§4, p. 8)
-- statement:
--   A **BGN bilinear group** (the output of the generator $\mathcal G_{\mathrm{BGN}}$ of Boneh, Goh and Nissim) is a tuple $(p, q, \mathbb G, \mathbb G_T, e, g)$ such that
--
--   1. $p$ and $q$ are primes with $p < q$;
--   2. $\mathbb G$ and $\mathbb G_T$ are finite commutative groups, written multiplicatively, of order $n = pq$;
--   3. $e : \mathbb G \times \mathbb G \to \mathbb G_T$ is bilinear: for all $u, v \in \mathbb G$ and $a, b \in \mathbb Z$,
--   $$e(u^a, v^b) = e(u, v)^{ab};$$
--   4. $g$ generates $\mathbb G$ and $e(g, g)$ generates $\mathbb G_T$.
--
--   In particular $\mathbb G$ and $\mathbb G_T$ are cyclic of order $n$. The definition also introduces the order $n = pq$ and the reduction map $\mathbb Z_n \to \mathbb Z_p$, $a \mapsto a \bmod p$, which is well defined because $p \mid n$.
--
--   This is the algebraic setting of the subgroup-decision commitment scheme of Groth, Ostrovsky and Sahai: every statement of the mission is about an arbitrary such tuple.
--
--   **Formalization Note** Bilinearity is encoded by taking $e$ to be a group homomorphism from $\mathbb G$ into the group homomorphisms $\mathbb G \to \mathbb G_T$; this is equivalent to $e(u^a, v^b) = e(u,v)^{ab}$ for all integers $a, b$. The randomized algorithm $\mathcal G_{\mathrm{BGN}}$, its security parameter and the requirement that group operations, membership tests and $e$ be efficiently computable are not modelled: theorems quantify over every tuple in the support of the generator, i.e. every tuple with the four properties above.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 8, Section 4 (definition of G_BGN)

import Mathlib

namespace GOSNIZK.BGNCommit

/-- The output `(p, q, 𝔾, 𝔾_T, e, g)` of the BGN group generator `𝒢_BGN` of Groth, Ostrovsky, Sahai,
*New Techniques for Noninteractive Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011,
§4, p. 8: primes `p < q`, cyclic groups `𝔾`, `𝔾_T` of order `n = pq`, a bilinear map `e : 𝔾 × 𝔾 → 𝔾_T`,
a generator `g` of `𝔾` such that `e(g, g)` generates `𝔾_T`.

Formalization Note: the groups are the type parameters `G`, `GT` (finite commutative groups, written
multiplicatively). Bilinearity `e(u^a, v^b) = e(u, v)^{ab}` for all `a, b ∈ ℤ` is encoded by taking `e`
to be a monoid homomorphism into the monoid homomorphisms `G →* GT`. Cyclicity of `𝔾` and `𝔾_T` follows
from the generator fields `hg` and `he`. The randomness of `𝒢_BGN` and the efficiency requirements are
not modelled: theorems quantify over every such tuple. -/
structure BGNSetup (G GT : Type*) [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT] where
  /-- the smaller prime `p` -/
  p : ℕ
  /-- the larger prime `q` -/
  q : ℕ
  hp : p.Prime
  hq : q.Prime
  hpq : p < q
  /-- `𝔾` has order `n = pq` -/
  card_G : Fintype.card G = p * q
  /-- `𝔾_T` has order `n = pq` -/
  card_GT : Fintype.card GT = p * q
  /-- the bilinear map `e : 𝔾 × 𝔾 → 𝔾_T` -/
  e : G →* G →* GT
  /-- the generator `g` of `𝔾` -/
  g : G
  hg : ∀ u : G, u ∈ Subgroup.zpowers g
  /-- `e(g, g)` generates `𝔾_T` -/
  he : ∀ z : GT, z ∈ Subgroup.zpowers (e g g)

namespace BGNSetup

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- The group order `n = pq`. -/
abbrev n (S : BGNSetup G GT) : ℕ := S.p * S.q

instance (S : BGNSetup G GT) : NeZero S.n := ⟨Nat.mul_ne_zero S.hp.ne_zero S.hq.ne_zero⟩

instance (S : BGNSetup G GT) : Fact S.p.Prime := ⟨S.hp⟩

/-- Reduction modulo `p`, `ℤ_n → ℤ_p` (well defined since `p ∣ n`). -/
def toZp (S : BGNSetup G GT) : ZMod S.n →+* ZMod S.p :=
  ZMod.castHom (dvd_mul_right S.p S.q) (ZMod S.p)

end BGNSetup

end GOSNIZK.BGNCommit


