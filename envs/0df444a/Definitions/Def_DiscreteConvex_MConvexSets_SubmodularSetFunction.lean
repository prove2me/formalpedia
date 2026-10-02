-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
-- name    : DiscreteConvex_MConvexSets_SubmodularSetFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:23.495278+00:00
-- url     : https://prove2.me/theorems/49e5b941-d466-4e53-82ca-e94ea6816451
-- title:
--   Submodular set function (Eq. 4.9-4.10)
-- statement:
--   $\rho : 2^V \to \mathbb R \cup \{+\infty\}$ is a **submodular set function** with $\rho(\emptyset)=0$ and $\rho(V)<+\infty$ (the class $S[\mathbb R]$): $\rho(X)+\rho(Y) \ge \rho(X\cup Y)+\rho(X\cap Y)$ for all $X,Y \subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103-104, Eq. (4.9)-(4.10).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103-104, Eq. (4.9)-(4.10)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103-104, Eq. (4.9)-(4.10): submodular set
functions, in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- `ρ : 2ⱽ → R ∪ {+∞}` is a **submodular set function** with `ρ(∅) = 0` and `ρ(V) < +∞`
(the class `S[R]`, Eq. (4.10)): `ρ(X) + ρ(Y) ≥ ρ(X ∪ Y) + ρ(X ∩ Y)` for all `X, Y ⊆ V`
(Eq. (4.9)). -/
def SubmodularSetFunction {V : Type*} [Fintype V] [DecidableEq V] (ρ : Finset V → WithTop ℝ) :
    Prop :=
  ρ ∅ = 0 ∧ ρ Finset.univ ≠ ⊤ ∧
    ∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y)

end DiscreteConvex.MConvexSets


