-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Labels
-- name    : DeletionHash_MixedEdit_Labels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:09.53163+00:00
-- url     : https://prove2.me/theorems/12782024-1c4a-47d8-9d85-1b2f2877b8f5
-- title:
--   Product-uniform binary labels and surviving rules
-- statement:
--   Fix $r\ge1$ and $Q=2^r$. A sample $\xi$ assigns each length-$L$ gram an arbitrary vector in $\mathbb F_2^r$. The full finite function space is sampled uniformly, so its gram coordinates are independent uniform vectors by construction. Define
--   $$H_\xi(p)=\sum_g\overline p_g\xi_g,\qquad K_\xi=\{w\in K_0:H_\xi(w)=0\}.$$
--   The word label is $H_\xi(R_L(y))$. Event probability is the number of satisfying samples divided by the cardinality of this full product space, which is nonempty. This explicit finite law supplies every probability in the mission; independence of images of independent differences is a theorem, not an axiom.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Definition 3.1, labels and surviving rules, printed p. 9 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Rules

namespace DeletionHash.MixedEdit

universe u

abbrev Label (r : ℕ) := Fin r → ZMod 2
abbrev HashSample (α : Type u) (L r : ℕ) := Gram α L → Label r

/-- Uniform counting probability on the full finite product of gram labels. -/
noncomputable def uniformProbability {Ω : Type u} [Fintype Ω] (event : Ω → Prop) : ℝ :=
  (Nat.card {ω : Ω // event ω} : ℝ) / (Fintype.card Ω : ℝ)

noncomputable def hash {α : Type u} [Fintype α] {L r : ℕ}
    (ξ : HashSample α L r) (p : Spectrum α L) : Label r :=
  ∑ g, (parity p g) • ξ g

def Survives {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (k t b : ℕ) (ξ : HashSample α L r) (w : Spectrum α L) : Prop :=
  w ∈ Catalogue k L t b ∧ hash ξ w = 0

end DeletionHash.MixedEdit


