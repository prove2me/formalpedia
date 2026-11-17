-- Prove2me | Definitions.Def_CompNonlocal_Supplement_Game_IndepQuestions
-- name    : CompNonlocal_Supplement_Game_IndepQuestions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:10:01.190083+00:00
-- url     : https://prove2.me/theorems/8cd9b41e-7468-454b-be74-6a1ec680d8f8
-- title:
--   Independent questions
-- statement:
--   A game has **independent questions** if, at every security parameter $\kappa$, the joint law of the questions $(X,Y)\leftarrow Q(1^\kappa)$ is exactly the product of its marginals:
--   $$\Pr[X=x,Y=y]=\Pr[X=x]\Pr[Y=y]\qquad\text{for all strings }x,y.$$
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Theorem 11, p.69; §12, p.68

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_Game

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- Independent questions. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 11, p.69 ("a public-verification certificate with
independent questions X, Y"; proof: "Independence makes A(x) an exact sample from Y | X = x for
every x in the support of X") and §12, p.68 ("If the questions are independent, this conditional law
is just the marginal law of Y"): at every `κ`, the joint law of the questions `(X, Y) ← Q(1^κ)` is
exactly the product of its marginals. -/
def Game.IndepQuestions (G : Game) : Prop :=
  ∀ (κ : ℕ) (x y : Str), G.qProb κ x y = G.xProb κ x * G.yProb κ y

end CompNonlocal.Supplement


