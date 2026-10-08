-- Prove2me | Definitions.Def_SAGA_StronglyConvex_sagaStep
-- name    : SAGA_StronglyConvex_sagaStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:12:08.176176+00:00
-- url     : https://prove2.me/theorems/c33b0aa8-20ab-49e1-9d95-a7c035ed89c3
-- title:
--   One iteration of SAGA
-- statement:
--   Let $f_1',\dots,f_n':E\to E$ be component gradients, $P:E\to E$ a map (the proximal operator $\operatorname{prox}^h_\gamma$ in every theorem) and $\gamma$ a step size. From the state $(x^k,\phi^k)$, with $\phi^k=(\phi^k_1,\dots,\phi^k_n)$, and the index $j$ drawn at iteration $k+1$, **one SAGA iteration** produces the state $(x^{k+1},\phi^{k+1})$ given by
--
--   $$
--   x^{k+1}=P\big(w^{k+1}\big),\qquad
--   w^{k+1}=x^k-\gamma\Big[f_j'(x^k)-f_j'(\phi^k_j)+\frac1n\sum_{i=1}^n f_i'(\phi^k_i)\Big],
--   $$
--
--   $$
--   \phi^{k+1}_j=x^k,\qquad \phi^{k+1}_i=\phi^k_i\quad(i\ne j).
--   $$
--
--   This is the SAGA algorithm of Section 2 (steps 2 and 3, eqs. (1)–(2)) of Defazio, Bach and Lacoste-Julien: the table entry $j$ is replaced by the point $x^k$ at which the new gradient was taken, not by $x^{k+1}$.
--
--   **Formalization Note** The state is the pair $(x,\phi)$ with $\phi:\mathtt{Fin}\,n\to E$; the index $j$ is an argument (step 1, "pick $j$ uniformly at random", enters the theorems as an average over $j$).
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 2, Section 2, SAGA Algorithm, eqs. (1)-(2)

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_sagaW

namespace SAGA.StronglyConvex

/-- One iteration of SAGA (Section 2, p. 2) from the state `s = (x^k, φ^k)` with index `j`:
`x^{k+1} = P (w^{k+1})` (eq. (2), `P` playing the role of `prox_γ^h`) and the table entry `j`
is overwritten by `x^k` (`φ_j^{k+1} = x^k`), all other entries unchanged. -/
noncomputable def sagaStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f' : Fin n → E → E) (P : E → E) (γ : ℝ) (s : E × (Fin n → E)) (j : Fin n) :
    E × (Fin n → E) :=
  (P (sagaW f' γ s.1 s.2 j), Function.update s.2 j s.1)

end SAGA.StronglyConvex


