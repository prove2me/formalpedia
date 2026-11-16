-- Prove2me | Definitions.Def_XORFullTilt_Hardness_Supplement_CommutingModel
-- name    : XORFullTilt_Hardness_Supplement_CommutingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:23:23.081086+00:00
-- url     : https://prove2.me/theorems/abb7d591-1045-49e0-932b-36ca9021a69b
-- title:
--   Hilbert-space POVMs, commuting strategies and value
-- statement:
--   A POVM on a complete complex Hilbert space $H$ is a finite family of bounded self-adjoint positive operators summing to the identity. A commuting-operator strategy consists of a unit vector $\psi\in H$ and question-indexed POVMs $P^x_a,Q^y_b$ satisfying $P^x_aQ^y_b=Q^y_bP^x_a$ for every question and answer pair. No finite-dimensionality assumption is imposed. Its probabilities and value are
--   $$p(a,b\mid x,y)=\operatorname{Re}\langle\psi,P^x_aQ^y_b\psi\rangle,\qquad \omega(G,p)=\sum_{x,y,a,b}\pi(x,y)V(a,b\mid x,y)p(a,b\mid x,y).$$
--   The commuting value $\omega^{\rm co}(G)$ is the supremum of these winning values over all such Hilbert spaces and strategies. Binary observables are $P_0-P_1$. This is the general POVM model; it imposes no synchrony or tracial-state condition.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.31, Definition 6.2

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame
import Definitions.Def_PoQHierarchy_Main_ICO

namespace XORFullTilt.Hardness.Supplement

/-- Reuse the published all-quantum, two-player Hilbert-space POVM model.
    `I = univ` makes the extra classical-player clause vacuous. -/
abbrev COStrategy (X Y A B : Type) [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] :=
  PoQHierarchy.Main.ICOStrategy 2 ![Fintype.card X, Fintype.card Y]
    ![Fintype.card A, Fintype.card B] Finset.univ

noncomputable def coAlice {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (S : COStrategy X Y A B) (x : X) (a : A) :
    S.H →L[ℂ] S.H :=
  S.P 0 (Fintype.equivFin X x) (Fintype.equivFin A a)

noncomputable def coBob {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (S : COStrategy X Y A B) (y : Y) (b : B) :
    S.H →L[ℂ] S.H :=
  S.P 1 (Fintype.equivFin Y y) (Fintype.equivFin B b)

noncomputable def coStrategyValue {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : MIPRE.Game X Y A B) (S : COStrategy X Y A B) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
    (inner ℂ S.Ω (coAlice S x a (coBob S y b S.Ω))).re

/-- Supremum of actual winning values on the base game, over the full reused model. -/
noncomputable def coValue {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : MIPRE.Game X Y A B) : ℝ :=
  sSup {v | ∃ S : COStrategy X Y A B, v = coStrategyValue G S}

noncomputable def coAliceObservable {X Y : Type} [Fintype X] [Fintype Y]
    (S : COStrategy X Y Bool Bool) (x : X) : S.H →L[ℂ] S.H :=
  coAlice S x false - coAlice S x true

noncomputable def coBobObservable {X Y : Type} [Fintype X] [Fintype Y]
    (S : COStrategy X Y Bool Bool) (y : Y) : S.H →L[ℂ] S.H :=
  coBob S y false - coBob S y true

end XORFullTilt.Hardness.Supplement


