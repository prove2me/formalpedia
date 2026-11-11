-- Prove2me | Definitions.Def_FlexRigidity_Game
-- name    : FlexRigidity_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:17:53.859517+00:00
-- url     : https://prove2.me/theorems/da5bb372-30cc-4036-81f6-e70bf7f1975a
-- title:
--   Two-player nonlocal games
-- statement:
--   A **nonlocal game** $\mathsf G=(X,Y,A,B,P_{XY},V)$ has finite input alphabets $X,Y$, finite output alphabets $A,B$, an input distribution $P_{XY}$ and a predicate $V:X\times Y\times A\times B\to\{0,1\}$. The verifier samples $(x,y)\sim P_{XY}$, sends $x$ to Alice and $y$ to Bob, receives $a,b$, and accepts when $V(x,y,a,b)=1$. `IsValid` says that $P_{XY}$ is a probability distribution.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 5.1, pp. 38–39

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Two-player nonlocal game**, Definition 5.1 (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, pp. 38–39): finite input alphabets `X, Y`, finite
output alphabets `A, B`, an input distribution `P_{XY}` and a predicate
`V : X × Y × A × B → {0, 1}`. `IsValid` says `P_{XY}` is a probability distribution.

**Formalization Note** The predicate is `Bool`-valued (`true` = 1). -/
structure Game (X Y A B : Type) where
  /-- the input distribution `P_{XY}` -/
  PXY : X → Y → ℝ
  /-- the winning predicate `V` -/
  V : X → Y → A → B → Bool

/-- `P_{XY}` is a probability distribution on `X × Y`. -/
def Game.IsValid {X Y A B : Type} [Fintype X] [Fintype Y] (G : Game X Y A B) : Prop :=
  (∀ x y, 0 ≤ G.PXY x y) ∧ ∑ x, ∑ y, G.PXY x y = 1

end FlexRigidity


