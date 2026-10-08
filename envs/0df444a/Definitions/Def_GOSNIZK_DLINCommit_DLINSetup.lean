-- Prove2me | Definitions.Def_GOSNIZK_DLINCommit_DLINSetup
-- name    : GOSNIZK_DLINCommit_DLINSetup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:33.066678+00:00
-- url     : https://prove2.me/theorems/be861e45-0ab5-4106-98ec-244b010ac306
-- title:
--   The bilinear group $(p, \mathbb G, \mathbb G_T, e, g)$ of prime order, and linear tuples (§5, p. 11)
-- statement:
--   A **DLIN bilinear group** (an output of the generator $\mathcal G_{\mathrm{DLIN}}$) is a tuple $(p, \mathbb G, \mathbb G_T, e, g)$ such that
--
--   1. $p$ is a prime;
--   2. $\mathbb G$ and $\mathbb G_T$ are finite commutative groups, written multiplicatively, of order $p$;
--   3. $e : \mathbb G \times \mathbb G \to \mathbb G_T$ is bilinear: for all $u, v \in \mathbb G$ and $a, b \in \mathbb Z$,
--   $$e(u^a, v^b) = e(u, v)^{ab};$$
--   4. $g$ generates $\mathbb G$ and $e(g, g)$ generates $\mathbb G_T$.
--
--   Given elements $f, h, g \in \mathbb G$, a triple $(a, b, c) \in \mathbb G^3$ is a **linear tuple with respect to $(f, h, g)$** if it has the form
--   $$(a, b, c) = (f^r, h^s, g^{r+s}) \qquad \text{for some } r, s \in \mathbb Z_p.$$
--
--   This is the algebraic setting of the decisional-linear commitment scheme of Groth, Ostrovsky and Sahai: every statement of the mission is about an arbitrary such tuple. The decisional linear problem is to tell a linear tuple from a random triple.
--
--   **Formalization Note** Bilinearity is encoded by taking $e$ to be a group homomorphism from $\mathbb G$ into the group homomorphisms $\mathbb G \to \mathbb G_T$; this is equivalent to $e(u^a, v^b) = e(u,v)^{ab}$ for all integers $a, b$. A group of prime order is cyclic, so assuming commutativity loses nothing. Exponents $a \in \mathbb Z_p$ act through their representative `a.val` $\in \{0, \dots, p-1\}$; since the groups have order $p$ this is the usual power. The randomized algorithm, its security parameter and the efficiency requirements are not modelled: theorems quantify over every tuple with properties 1–4.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 11, Section 5 (definition of G_DLIN and of linear tuples)

import Mathlib

namespace GOSNIZK.DLINCommit

/-- An output `(p, 𝔾, 𝔾_T, e, g)` of the bilinear group generator `𝒢_DLIN` of Groth, Ostrovsky, Sahai,
*New Techniques for Noninteractive Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011,
§5, p. 11: a prime `p`, groups `𝔾`, `𝔾_T` of order `p`, a bilinear map `e : 𝔾 × 𝔾 → 𝔾_T`, a generator
`g` of `𝔾` such that `e(g, g)` generates `𝔾_T`.

Formalization Note: the groups are the type parameters `G`, `GT` (finite commutative groups, written
multiplicatively; a group of prime order is cyclic, hence commutative). Bilinearity
`e(u^a, v^b) = e(u, v)^{ab}` for all `a, b ∈ ℤ` is encoded by taking `e` to be a monoid homomorphism into
the monoid homomorphisms `G →* GT`. The randomness of `𝒢_DLIN` and the efficiency requirements are not
modelled: theorems quantify over every such tuple. -/
structure DLINSetup (G GT : Type*) [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT] where
  /-- the prime `p` -/
  p : ℕ
  hp : p.Prime
  /-- `𝔾` has order `p` -/
  card_G : Fintype.card G = p
  /-- `𝔾_T` has order `p` -/
  card_GT : Fintype.card GT = p
  /-- the bilinear map `e : 𝔾 × 𝔾 → 𝔾_T` -/
  e : G →* G →* GT
  /-- the generator `g` of `𝔾` -/
  g : G
  hg : ∀ u : G, u ∈ Subgroup.zpowers g
  /-- `e(g, g)` generates `𝔾_T` -/
  he : ∀ z : GT, z ∈ Subgroup.zpowers (e g g)

namespace DLINSetup

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

instance (S : DLINSetup G GT) : Fact S.p.Prime := ⟨S.hp⟩

instance (S : DLINSetup G GT) : NeZero S.p := ⟨S.hp.ne_zero⟩

/-- A *linear tuple* with respect to `(f, h, g)` (p. 11): a triple of the form `(f^r, h^s, g^{r+s})` with
`r, s ∈ ℤ_p`. Exponents in `ℤ_p` act through their representative `a.val ∈ {0, …, p − 1}`. -/
def IsLinearTuple (S : DLINSetup G GT) (f h g : G) (c : G × G × G) : Prop :=
  ∃ r s : ZMod S.p, c = (f ^ r.val, h ^ s.val, g ^ (r + s).val)

end DLINSetup

end GOSNIZK.DLINCommit


