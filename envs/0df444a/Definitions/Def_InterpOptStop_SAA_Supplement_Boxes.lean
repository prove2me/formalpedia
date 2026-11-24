-- Prove2me | Definitions.Def_InterpOptStop_SAA_Supplement_Boxes
-- name    : InterpOptStop_SAA_Supplement_Boxes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:44:13.364811+00:00
-- url     : https://prove2.me/theorems/b7df3701-a880-406a-af48-262360f4f59e
-- title:
--   Finite unions of lower-open, upper-closed boxes
-- statement:
--   For endpoints $a^j,b^j\in\mathbb R^n$, define $B_j=\prod_i(a^j_i,b^j_i]$. The policy associated with $K$ such boxes is
--   $$\pi_{\rm boxes}(x)=\begin{cases}\mathrm{stop},&x\in\bigcup_{j=1}^K B_j,\\\mathrm{go},&\text{otherwise}.\end{cases}$$
--   No ordering, distinctness, disjointness or nonemptiness is required. Empty unions give the always-go policy. In zero physical dimension a box is the singleton empty vector. This definition is the target for exact representation using the published finite tree evaluator.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Lemma EC.4, (EC.30), p. ec22

import Mathlib
import Definitions.Def_InterpOptStop_SAA_TreePolicy

namespace InterpOptStop.SAA.Supplement

/-- No ordering is imposed on the endpoints; degenerate boxes may be empty. -/
def box {n : ℕ} (a b : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, a i < x i ∧ x i ≤ b i}

noncomputable def boxesPolicy {n K : ℕ} (a b : Fin K → Fin n → ℝ)
    (x : Fin n → ℝ) : Act :=
  by
    classical
    exact if ∃ j, x ∈ box (a j) (b j) then Act.stop else Act.go

end InterpOptStop.SAA.Supplement


