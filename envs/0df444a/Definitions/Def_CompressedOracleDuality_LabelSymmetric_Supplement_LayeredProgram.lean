-- Prove2me | Definitions.Def_CompressedOracleDuality_LabelSymmetric_Supplement_LayeredProgram
-- name    : CompressedOracleDuality_LabelSymmetric_Supplement_LayeredProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T22:06:58.920384+00:00
-- url     : https://prove2.me/theorems/11349273-dcee-4c07-bac7-eb9d18538992
-- title:
--   Deterministic layered oracle branching programs
-- statement:
--   Let $T$ be a natural number and let $X,Y,O$ be the query, answer, and output types. A deterministic layered oracle branching program has finite vertex sets $V_0,\ldots,V_T$, a singleton initial layer $V_0$, a query $q_t:V_t\to X$ and a total transition $\delta_t:V_t\times Y\to V_{t+1}$ for each $0\le t<T$, and a leaf-output map $o:V_T\to O$. Distinct edges may merge; queries may be adaptive or repeated. For an oracle $H:X\to Y$ its actual execution is
--   $$\mu_0(H)=\mathrm{start},\qquad \mu_{t+1}(H)=\delta_t(\mu_t(H),H(q_t(\mu_t(H)))).$$
--   The $S$-bit space predicate is $|V_t|\le2^S$ only for $1\le t<T$. There is no numerical bound on the finite terminal layer. The source's exact internal width is recovered by padding unreachable vertices. At $T=0$ the initial and terminal layer is the same singleton and the output is fixed.
--
--   This general query-program object is separate from the collision-specific alphabet, symmetry, and success definitions. It imposes no reversibility, success requirement, or matched-label bound.
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94; source.pdf SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, Definition 5.4 and execution paragraph, p.27

import Mathlib

namespace CompressedOracleDuality.LabelSymmetric.Supplement

/-- Definition 5.4, p.27: a deterministic layered oracle branching program.
`X`, `Y`, and `O` are the query, answer, and output types. Distinct edges may merge.
No width condition is built into the general object. -/
structure LayeredProgram (X Y O : Type) (T : ℕ) where
  Vertex : Fin (T + 1) → Type
  finite : ∀ t, Fintype (Vertex t)
  initial : Unique (Vertex 0)
  query : (t : Fin T) → Vertex t.castSucc → X
  step : (t : Fin T) → Vertex t.castSucc → Y → Vertex t.succ
  output : Vertex (Fin.last T) → O

attribute [instance] LayeredProgram.finite

/-- Actual execution: the next vertex depends only on the current vertex and query answer. -/
def LayeredProgram.run {X Y O : Type} {T : ℕ}
    (B : LayeredProgram X Y O T) (H : X → Y) : (t : Fin (T + 1)) → B.Vertex t :=
  Fin.induction B.initial.default (fun t m => B.step t m (H (B.query t m)))

/-- Definition 5.4: only layers 1,...,T-1 count against the S-bit width bound.
The source's exact width is recovered by padding unreachable internal vertices. -/
def LayeredProgram.SpaceBound {X Y O : Type} {T : ℕ}
    (B : LayeredProgram X Y O T) (S : ℕ) : Prop :=
  ∀ t : Fin (T + 1), 0 < t.val → t.val < T → Fintype.card (B.Vertex t) ≤ 2 ^ S

end CompressedOracleDuality.LabelSymmetric.Supplement


