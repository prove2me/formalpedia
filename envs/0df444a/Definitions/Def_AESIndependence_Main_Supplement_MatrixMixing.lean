-- Prove2me | Definitions.Def_AESIndependence_Main_Supplement_MatrixMixing
-- name    : AESIndependence_Main_Supplement_MatrixMixing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:02:33.31776+00:00
-- url     : https://prove2.me/theorems/9ed36658-0f7d-442b-ab0c-cda7833a38b2
-- title:
--   Worst-case total-variation mixing for powers of a finite transition matrix
-- statement:
--   For a real matrix $K$ on a finite state space $X$, with columns representing the current state, let $u_X(y)=1/|X|$. The predicate $\operatorname{MixedAt}(K,\varepsilon,r)$ means
--
--   $$
--   \forall x\in X,\qquad \frac12\sum_{y\in X}|(K^r)(y,x)-u_X(y)|\le\varepsilon.
--   $$
--
--   It measures worst-case total-variation distance after exactly $r$ steps. Here $r$ is a natural number, so $K^0$ is the identity. Stochasticity and nonemptiness are hypotheses of the theorem using the predicate. No mixing time is defined, so failure ever to mix does not acquire a default successful time. The tuple carrier, uniform mass, and total variation are the existing published definitions. General column- and doubly-stochastic matrices are supplied directly by Mathlib, separately from this mixing predicate.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), §2.3, pp.12–13 (PDF pp.12–13), Theorem 2.16; quantitative explanation p.5 (PDF p.5)

import Mathlib
import Definitions.Def_AESIndependence_Main_LabelChains

namespace AESIndependence.Main.Supplement

noncomputable section

/-- Worst-case total-variation mixing to uniform at a specified integer time.
Matrices use the published column convention: `K y x = Pr[x → y]`.
The stochasticity and nonemptiness assumptions belong to the theorem using this predicate;
this definition does not assign a default mixing time when no time succeeds.
Source: Pelecanos–Tessaro–Vaikuntanathan, STOC 2027 submission #1279,
§2.3, pp.12–13 (PDF pp.12–13), Theorem 2.16. -/
def MixedAt {X : Type} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℝ) (ε : ℝ) (r : ℕ) : Prop :=
  ∀ x : X, totalVariation (fun y => (K ^ r) y x) (uniformMass X) ≤ ε

end
end AESIndependence.Main.Supplement


