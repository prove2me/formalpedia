-- Prove2me | Definitions.Def_TFNPRom_Supplement_SinkDagReduction
-- name    : TFNPRom_Supplement_SinkDagReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:26:39.319257+00:00
-- url     : https://prove2.me/theorems/e69f0729-0751-4b36-b59e-54ef388dd2fd
-- title:
--   Public reduction to Sink of Dag with identity instance distribution
-- statement:
--   Let $F$ be a search problem with inputs $u\in\Sigma^n$ and solutions in $O$. A **public reduction** $(\omega,f,g)$ with $\omega(u)=u$ from $F$ to Sink of Dag on the $K\times K$ grid consists of
--
--   1. decision trees $f_{ij}$ over $u$ computing the cells $\mathrm{Succ}_{ij}\in[K]\cup\{\bot\}$ of a target instance $f(u)$;
--   2. for every grid node $o$, a decision tree $g_o$ over $u$ computing a candidate solution $g_o(u)\in O$ of $u$;
--
--   all of depth at most $d$. Its complexity is $d+\log m$ with $m=K^2$ the number of target cells. No correctness is required: the reduction is measured by its error.
--
--   **Formalization Note** The identity $\omega$ is not stored, and $d$ bounds the depths of $f$ and $g$ only.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §5, p.28; §5.1, p.29

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical

namespace TFNPRom.Supplement

/-- A public (ROM) reduction of depth at most `d`, with the identity instance distribution, from a
search problem over inputs `u ∈ α^ι` with solutions in `O` to Sink of Dag on the `K × K` grid
(Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §5, p.28; §5.1, p.29: "All our lower bounds will be against the uniform distribution
`ω(u) = u`"). It consists of
1. decision trees `f i j` over `u` computing the cells `Succ_ij ∈ [K] ∪ {⊥}` of the target
   instance `f(u)` (the paper's `f`);
2. for every grid node `o = (i, j)` a decision tree `g i j` over `u` computing a candidate source
   solution `g_o(u) ∈ O` (the paper's `g`);
3. every tree makes at most `d` queries on every input.

No correctness is required: the quality of the reduction is its error (`sinkDagErr`).

**Formalization Note** `ω` is the identity, so its trees are not part of the structure and `d`
bounds the depths of `f` and `g` only. The target instance has `m = K²` cells, so the paper's
complexity `d + log m` is `d + log₂(K²)`. -/
structure SinkDagReduction (ι α O : Type) (K d : ℕ) where
  /-- the trees computing the target cells `Succ_ij` -/
  f : Fin K → Fin K → QAlgorithms.DecisionTree ι α (Option (Fin K))
  /-- the decoding trees `g_o` -/
  g : Fin K → Fin K → QAlgorithms.DecisionTree ι α O
  /-- depth bound for `f` -/
  f_depth : ∀ i j, (f i j).MakesAtMost d
  /-- depth bound for `g` -/
  g_depth : ∀ i j, (g i j).MakesAtMost d

end TFNPRom.Supplement


