-- Prove2me | Definitions.Def_ReplParity_Supplement_IsReplicableOnRealizable
-- name    : ReplParity_Supplement_IsReplicableOnRealizable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:54:11.898071+00:00
-- url     : https://prove2.me/theorems/e2e1dab9-760e-4b75-9904-de8e251c32c2
-- title:
--   $\rho$-replicable on realizable distributions
-- statement:
--   Let $X$ be a finite domain and $H$ a class of functions $X\to\{0,1\}$. A learner $A$ with sample size $m$ and a seed $r$ uniform on a nonempty finite set $\Omega$ is **$\rho$-replicable on realizable distributions** (for $H$) if for every labeled distribution $D$ on $X\times\{0,1\}$ with $\mathrm{err}_D(h^\star)=0$ for some $h^\star\in H$,
--   $$\Pr_{S,S'\sim D^m,\,r}\big[A(S;r)\ne A(S';r)\big]\le\rho,$$
--   where $S$ and $S'$ are independent and the seed $r$ is shared by the two runs.
--
--   This is Definition 2.1 with the quantifier restricted to the distributions of Definition 2.2. Statement 1 of Theorem 5.3 asks for it, and statement 3 for the stronger property on every labeled distribution.
--
--   **Formalization Note** Probabilities are the base mission's finite sums over samples and seeds; $D$ is any distribution with real weights.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.10 (PDF p.12), paragraph after Definition 2.1

import Mathlib
import Definitions.Def_ReplParity_prIID
import Definitions.Def_ReplParity_err

set_option autoImplicit false

namespace ReplParity

namespace Supplement

/-- **ρ-replicable on realizable distributions.** Shen, Zhong, *Replicable Parity Learning: Cubic
Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), §2.1, p.10 (PDF p.12): "Some of our statements also use the weaker property of being
ρ-replicable on realizable distributions, where the condition is required only for distributions
realized by the target class".

A learner `A` with sample size `m`, seeds uniform on the nonempty finite type `Ω` and outputs in `β` is
ρ-replicable on the distributions realized by `H` if, for every labeled distribution `D` on
`X × ZMod 2` with `err_D(h⋆) = 0` for some `h⋆ ∈ H`, two runs on independent samples `S, S′ ∼ D^m`
that share the seed `r` disagree with probability at most `ρ`.

**Formalization Note.** This is the base mission's `ReplParity.IsReplicable` (Definition 2.1)
with the quantifier over `D` restricted to the realizable distributions of Definition 2.2
(`ReplParity.IsRealizablyPAC`). As there, `X` is finite, labels are `ZMod 2`, `D` is any `PMF`, and
probabilities are finite sums (`ReplParity.prIID2`). Nonemptiness of `Ω` rules out the nonexistent
uniform distribution on an empty seed space. -/
def IsReplicableOnRealizable {X Ω β : Type*} [Fintype X] [Fintype Ω] [Nonempty Ω]
    (H : Set (X → ZMod 2))
    {m : ℕ} (A : (Fin m → X × ZMod 2) → Ω → β) (ρ : ℝ) : Prop :=
  ∀ D : PMF (X × ZMod 2), (∃ h ∈ H, err D h = 0) →
    prIID2 D m (fun S S' r => A S r ≠ A S' r) ≤ ρ

end Supplement

end ReplParity


