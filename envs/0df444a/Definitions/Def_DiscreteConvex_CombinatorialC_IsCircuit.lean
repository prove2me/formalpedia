-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
-- name    : DiscreteConvex_CombinatorialC_IsCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:42:09.137958+00:00
-- url     : https://prove2.me/theorems/5281496e-74f4-4eea-a7a4-741e94465d67
-- title:
--   Circuit
-- statement:
--   $\pi:A\to\{0,\pm1\}$ with $\partial\pi=0$ and $\operatorname{supp}^+(\pi)\cup\operatorname{supp}^-(\pi)$ a simple cycle.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_Boundary
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSimpleCycle
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.84: a circuit, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `π : A → R` is a **circuit**: `π(a) ∈ \{0,\pm 1\}` for every arc, `∂π = 0` (conservation),
and `supp⁺(π) ∪ supp⁻(π)` forms a simple cycle. -/
def IsCircuit {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (pi : A → ℝ) : Prop :=
  (∀ a, pi a = 1 ∨ pi a = 0 ∨ pi a = -1) ∧ (∀ v, Boundary src dst pi v = 0) ∧
    ∃ (k : ℕ) (v : Fin (k + 1) → V) (arcs : Fin (k + 1) → A), IsSimpleCycle src dst k v arcs ∧
      Finset.image arcs Finset.univ = SuppPosR pi ∪ SuppNegR pi

end DiscreteConvex.CombinatorialC


