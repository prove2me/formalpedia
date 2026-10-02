-- Prove2me | Definitions.Def_DiscreteConvex_Combinatorial_RankAxioms
-- name    : DiscreteConvex_Combinatorial_RankAxioms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:25:33.813367+00:00
-- url     : https://prove2.me/theorems/9a19613a-60b8-4c25-9346-c69b501000c6
-- title:
--   Matroid rank axioms (R1)-(R3)
-- statement:
--   A set function $\rho$ on the subsets of a finite ground set $V$ satisfies Murota's **rank axioms (R1)-(R3)** if:
--
--   1. (R1) $0 \le \rho(X) \le |X|$ for every $X \subseteq V$;
--   2. (R2) $\rho$ is monotone: $X \subseteq Y \Rightarrow \rho(X) \le \rho(Y)$;
--   3. (R3) $\rho$ is submodular: $\rho(X) + \rho(Y) \ge \rho(X \cup Y) + \rho(X \cap Y)$ for all $X, Y \subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69-70, axiom (R).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69-70, axiom (R) = (R1),(R2),(R3)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69-70, axiom (R) = (R1),(R2),(R3): the rank
axioms of a matroid, stated for a `ℤ`-valued set function on the subsets of a finite ground
set. Definitional groundwork for Theorem 2.29 in `DiscreteConvex.Combinatorial`.
-/

namespace DiscreteConvex.Combinatorial

/-- A set function `ρ` on the subsets of a finite ground set `V` satisfies Murota's
**rank axioms (R1)-(R3)**: (R1) `0 ≤ ρ(X) ≤ |X|`; (R2) monotonicity; (R3) submodularity. -/
def RankAxioms {V : Type*} [DecidableEq V] (ρ : Finset V → ℤ) : Prop :=
  (∀ X : Finset V, 0 ≤ ρ X ∧ ρ X ≤ (X.card : ℤ)) ∧
  (∀ X Y : Finset V, X ⊆ Y → ρ X ≤ ρ Y) ∧
  (∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y))

end DiscreteConvex.Combinatorial


