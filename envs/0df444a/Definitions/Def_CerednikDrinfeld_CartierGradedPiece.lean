-- Prove2me | Definitions.Def_CerednikDrinfeld_CartierGradedPiece
-- name    : CerednikDrinfeld_CartierGradedPiece
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/3111fe94-e1d8-50b0-90be-9937292e39b0
-- title:
--   Graded pieces of the Cartier module of a formal OD​-module
-- statement:
--   Fix a prime $p$, a commutative ring $B$, an object $X$ of the project's type `FormalODModule p B` (a two-dimensional formal group law `X.F` over $B$ together with the data packaged in that structure, in particular an operation `X.actEnd` assigning to an element of the ring `Zp2 p` — the Witt vectors of the field `GaloisField p 2`, i.e. $W(\mathbb F_{p^2})$ — an endomorphism of `X.F`), a ring homomorphism $j\colon$ `Zp2 p` $\to B$, and a natural number $n$. The definition `gradedPiece` produces the additive subgroup of the Cartier module `CartierModule p X.F` consisting of those $f$ satisfying
--   $$\mathrm{endAct}\bigl(X.\mathrm{actEnd}([c])\bigr)\,f \;=\; \mathrm{homothety}\bigl(j([c])^{p^n}\bigr)\,f \qquad\text{for every } c\in\mathbb F_{p^2},$$
--   where $[c]=$ `WittVector.teichmuller p c` is the Teichmüller representative, `endAct` is the action of $\mathrm{End}(X.F)$ on the Cartier module by post-composition of the defining power series, and `homothety b` is pre-composition with the Teichmüller endomorphism of the Witt law, i.e. the rescaling $e\mapsto b^{p^{\,\cdot}}$ of the coefficient family. Closure under $0$, $+$ and $-$ holds because both sides are additive homomorphisms in $f$; the condition is imposed only on Teichmüller representatives, not on all of `Zp2 p`.
--
--   The accompanying lemmas are: `mem_gradedPiece_iff`, the defining membership criterion (true by definition); `pow_card_galoisField`, that $c^{p^2}=c$ in `GaloisField p 2`; `apply_teichmuller_pow_pow_add_two`, that $j([c])^{p^{n+2}}=j([c])^{p^n}$; and the resulting periodicity $M_{n+2}=M_n$, hence $M_{n+2k}=M_n$, so that only two distinct subgroups arise. No direct-sum decomposition of the Cartier module into these pieces, and no statement about how Frobenius, Verschiebung or the uniformiser shift the index, is asserted here.
--
--   **Relation to Mathlib.** Mathlib has no formal $\mathcal O_D$-modules and no Cartier modules of multivariate formal group laws; these are the project's own notions, built on the project's `CartierModule`, `endAct` and `homothety`. Mathlib's `WittVector.teichmuller`, `GaloisField` and `FiniteField.pow_card` are used.
--
--   **Where it is used.** The graded pieces are part of the project's Cartier-theoretic analysis of special formal $\mathcal O_D$-modules, the local objects underlying the Čerednik–Drinfeld $p$-adic uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_CartierGradedPiece.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

def gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    AddSubgroup (CartierModule p X.F) where
  carrier := {f | ∀ c : GaloisField p 2,
    endAct (X.actEnd (WittVector.teichmuller p c)) f =
      homothety (j (WittVector.teichmuller p c) ^ p ^ n) f}
  zero_mem' := fun c => by simp only [map_zero]
  add_mem' := fun {f g} hf hg c => by simp only [map_add, hf c, hg c]
  neg_mem' := fun {f} hf c => by simp only [map_neg, hf c]

theorem mem_gradedPiece_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) :
    f ∈ X.gradedPiece j n ↔ ∀ c : GaloisField p 2,
      endAct (X.actEnd (WittVector.teichmuller p c)) f =
        homothety (j (WittVector.teichmuller p c) ^ p ^ n) f :=
  Iff.rfl

theorem pow_card_galoisField (c : GaloisField p 2) : c ^ p ^ 2 = c := by
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]
  rw [← hcard]
  exact FiniteField.pow_card c

theorem apply_teichmuller_pow_pow_add_two (j : Zp2 p →+* B) (c : GaloisField p 2) (n : ℕ) :
    j (WittVector.teichmuller p c) ^ p ^ (n + 2) = j (WittVector.teichmuller p c) ^ p ^ n := by
  rw [pow_add, pow_mul, ← map_pow, ← map_pow, ← map_pow, ← map_pow, ← pow_mul, mul_comm, pow_mul,
    pow_card_galoisField]

theorem gradedPiece_add_two (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    X.gradedPiece j (n + 2) = X.gradedPiece j n := by
  ext f
  simp only [mem_gradedPiece_iff, apply_teichmuller_pow_pow_add_two]

theorem gradedPiece_add_two_mul (X : FormalODModule p B) (j : Zp2 p →+* B) (n k : ℕ) :
    X.gradedPiece j (n + 2 * k) = X.gradedPiece j n := by
  induction k with
  | zero => rw [mul_zero, add_zero]
  | succ k ih => rw [mul_add, mul_one, ← add_assoc, gradedPiece_add_two, ih]

end FormalODModule

end CerednikDrinfeld

end


