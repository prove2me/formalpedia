-- Prove2me | Definitions.Def_GroupIsoPoly_encMACInst
-- name    : GroupIsoPoly_encMACInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:52.099206+00:00
-- url     : https://prove2.me/theorems/2d8b6d8b-25e1-4bb5-93ca-8eeae397d5cc
-- title:
--   Binary input of module action compatibility
-- statement:
--   The data of Definition 27 are coded as: $p$, $a$, $n=|Q|$; the Cayley table of $Q$ under a labelling; the number $t$ and the labels of a generating list $S_1,\dots,S_t$ of $Q$; the matrices $\theta(S_i)$ and $\theta'(S_i)$ (entries as numbers below $p$); the degree $k=|\Omega|$; the number $s$ and the image lists of the generators $g_1,\dots,g_s$ of $\Gamma$; and for each $g_i$ the table of the automorphism $\beta(g_i)$ of $Q$ in the labels. The length is the paper's $\mathrm{InSize}$.
--
--   Representations and $\beta$ are given only on generators, as in the paper (§3.5, p.19); since $S$ generates $Q$ and the $g_i$ generate $\Gamma$, these values determine the homomorphisms. A compatible pair in an answer is written as the entries of $\alpha$ followed by the image list of $g$ (`macNats`).
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 27 and Theorem 9.3, p.93 (PDF p.97); §3.5, p.19 (PDF p.23)

import Mathlib
import Definitions.Def_GroupIsoPoly_encPair
import Definitions.Def_GroupIsoPoly_encIsoAnswer
import Definitions.Def_GroupIsoPoly_compatPairs

set_option autoImplicit false

namespace GroupIsoPoly

open ExponomialAssortment.FPTAS (encodeNat)

/-- An `a × a` matrix over `F_p`, written as its entries (row by row) as numbers below `p`. -/
def glNats {p a : ℕ} (M : GL (Fin a) (ZMod p)) : List ℕ :=
  (List.ofFn fun i : Fin a => List.ofFn fun j : Fin a => ((M : Matrix (Fin a) (Fin a) (ZMod p)) i j).val).flatten

/-- A permutation of `Fin k`, written as its list of images. -/
def permNats {k : ℕ} (σ : Equiv.Perm (Fin k)) : List ℕ :=
  List.ofFn fun x : Fin k => (σ x : ℕ)

/-- A compatible pair `(α, g)`, written as the entries of `α` followed by the images of `g`. -/
def macNats {p a k s : ℕ} {gens : Fin s → Equiv.Perm (Fin k)}
    (x : GL (Fin a) (ZMod p) × ↥(gammaOf gens)) : List ℕ :=
  glNats x.1 ++ permNats (x.2 : Equiv.Perm (Fin k))

/-- **The binary input of module action compatibility** (Definition 27).

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 27 and Theorem 9.3, p.93 (PDF p.97):
"representations θ : Q → GL(M) and θ′ : Q → GL(M′) given on a specified generating set of Q. Also
given are generators of Γ ≤ Sym(Ω) and their images under β : Γ → Aut(Q) … with n = |Q| and total
explicit input length InSize".

The code lists `p`, `a`, `n = |Q|`, the Cayley table of `Q` (labelling `eQ : Q ≃ Fin n`), the number
`t` and the labels of the generators `S₁, …, S_t` of `Q`, the matrices `θ(S_i)` and `θ′(S_i)`, the
degree `k = |Ω|`, the number `s` and the images of the generators `g₁, …, g_s` of `Γ`, and for each
`g_i` the table of the automorphism `β(g_i)` of `Q` in the labels of `eQ`. Its length is `InSize`.

**Formalization Note.** Representations and `β` are given only by their values on the generators,
as in the paper (§3.5, p.19: "Representations and affine actions are specified on the given
generators"); the theorem quantifies over the homomorphisms, which these values determine. -/
def encMACInst {p a n t k s : ℕ} {Q : Type*} [Group Q] (eQ : Q ≃ Fin n) (S : Fin t → Q)
    (θ θ' : Q →* GL (Fin a) (ZMod p)) (gens : Fin s → Equiv.Perm (Fin k))
    (β : ↥(gammaOf gens) →* MulAut Q) : List Bool :=
  encodeNat p ++ encodeNat a ++ encodeNat n ++ encTable n (cayley eQ) ++
    encodeNat t ++ (List.ofFn fun i : Fin t => encodeNat (eQ (S i) : ℕ)).flatten ++
    (List.ofFn fun i : Fin t => ((glNats (θ (S i))).map encodeNat).flatten).flatten ++
    (List.ofFn fun i : Fin t => ((glNats (θ' (S i))).map encodeNat).flatten).flatten ++
    encodeNat k ++ encodeNat s ++
    (List.ofFn fun i : Fin s => ((permNats (gens i)).map encodeNat).flatten).flatten ++
    (List.ofFn fun i : Fin s =>
      ((autLabels eQ (β ⟨gens i, Subgroup.subset_closure ⟨i, rfl⟩⟩)).map encodeNat).flatten).flatten

end GroupIsoPoly


