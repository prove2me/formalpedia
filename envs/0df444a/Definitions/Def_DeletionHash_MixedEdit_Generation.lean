-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Generation
-- name    : DeletionHash_MixedEdit_Generation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:21.288557+00:00
-- url     : https://prove2.me/theorems/f4b71125-09be-4655-88df-e23a61739f41
-- title:
--   Generating sequences, underlying sets and witness parameters
-- statement:
--   A generating sequence at a spectrum $v$ is an ordered finite family of catalogue rules with linearly independent reductions over $\mathbb F_2$. Every negative gram of rule $j$ must belong to the support of $v$ or to the support of an earlier rule, of either sign. A generating set is the underlying finite set of a sequence admitting such an order. The counting function counts these sets, not their orders, using extended natural cardinality so an infinite family cannot default to zero. The witness size bound is $M=1+2t(2L+2b-2)L$. The exponent criterion is equation (6):
--   $$(2tR+1)(LR)^{aR}\le L^{\lambda R}\quad(2\le R\le M).$$
--   No bound on the number of generating sets or favorable witness is assumed by these definitions.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Definition 4.3, printed p. 13 (PDF p. 15); Lemma 4.6, printed p. 14 (PDF p. 16); §6.1 equation (6), printed p. 18 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_SupportComponents
import Definitions.Def_DeletionHash_MixedEdit_Regime

namespace DeletionHash.MixedEdit

universe u

noncomputable def ruleSet {α : Type u} {L R : ℕ} (G : Fin R → Spectrum α L) : Finset (Spectrum α L) := by
  classical
  exact Finset.univ.image G

def GeneratingSequence {α : Type u} [DecidableEq α] {L R : ℕ}
    (k t b : ℕ) (v : Spectrum α L) (G : Fin R → Spectrum α L) : Prop :=
  (∀ j, G j ∈ Catalogue k L t b) ∧ LinearIndependent (ZMod 2) (fun j => parity (G j)) ∧
  (∀ j g, G j g = -1 → v g ≠ 0 ∨ ∃ i, i < j ∧ G i g ≠ 0)

def GeneratingSet {α : Type u} [DecidableEq α] {L : ℕ}
    (k t b : ℕ) (v : Spectrum α L) (F : Finset (Spectrum α L)) : Prop :=
  ∃ G : Fin F.card → Spectrum α L, GeneratingSequence k t b v G ∧ ruleSet G = F

/-- Extended cardinal prevents an infinite family from silently being counted as zero. -/
noncomputable def generatingCount {α : Type u} [DecidableEq α] {L : ℕ}
    (k t b : ℕ) (v : Spectrum α L) (R c : ℕ) : ℕ∞ :=
  Set.encard {F : Finset (Spectrum α L) | GeneratingSet k t b v F ∧ F.card = R ∧ componentCount F = c}

def witnessBound (t b L : ℕ) : ℕ := 1 + 2*t*(2*L+2*b-2)*L

/-- Equation (6), including its entire range of witness sizes. -/
def ExponentBound (t b a lam L : ℕ) : Prop :=
  ∀ R : ℕ, 2 ≤ R → R ≤ witnessBound t b L →
    (2*t*R+1)*(L*R)^(a*R) ≤ L^(lam*R)

end DeletionHash.MixedEdit


