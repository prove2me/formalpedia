-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_ExtremePoints
-- name    : PlanarMetricElections_Peer_ExtremePoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:49.27558+00:00
-- url     : https://prove2.me/theorems/164c4056-f4a2-4433-b647-5f078c984115
-- title:
--   Easternmost and southernmost points of a finite set
-- statement:
--   For a nonempty finite planar set $X$, choose an easternmost point $\operatorname{East}(X)$ and a southernmost point $\operatorname{South}(X)$. They satisfy
--
--   $$\operatorname{East}(X)\in X,\quad \forall x\in X,\ x_1\le\operatorname{East}(X)_1,$$
--   $$\operatorname{South}(X)\in X,\quad \forall x\in X,\ \operatorname{South}(X)_2\le x_2.$$
--
--   These choices can coincide. They implement the specific selected set in Lemma A.8. The included lemmas are the immediate specifications of Mathlib's finite extremum choice.
--
--   **Formalization Note** The empty-input default is the origin. Lemma A.8 assumes positive mass in $F$, so that default is never used there. Classical choices break ties arbitrarily.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Appendix A, p. 13 and Lemma A.8, p. 20 (PDF pp. 14, 21)

import Definitions.Def_PlanarMetricElections_Peer_Mass

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer

/-- Easternmost voter; the unused empty-input default is the origin. -/
def eastPoint (X : Finset Plane) : Plane :=
  if h : X.Nonempty then Classical.choose (Finset.exists_max_image X Prod.fst h) else 0

/-- Southernmost voter; the unused empty-input default is the origin. -/
def southPoint (X : Finset Plane) : Plane :=
  if h : X.Nonempty then Classical.choose (Finset.exists_min_image X Prod.snd h) else 0

/-- Immediate specification of the choice, used for the concrete selection in A.8. -/
theorem eastPoint_spec (X : Finset Plane) (h : X.Nonempty) :
    eastPoint X ∈ X ∧ ∀ x ∈ X, x.1 ≤ (eastPoint X).1 := by
  simpa only [eastPoint, dif_pos h] using
    (Classical.choose_spec (Finset.exists_max_image X Prod.fst h))

theorem southPoint_spec (X : Finset Plane) (h : X.Nonempty) :
    southPoint X ∈ X ∧ ∀ x ∈ X, (southPoint X).2 ≤ x.2 := by
  simpa only [southPoint, dif_pos h] using
    (Classical.choose_spec (Finset.exists_min_image X Prod.snd h))

end PlanarMetricElections.Peer


