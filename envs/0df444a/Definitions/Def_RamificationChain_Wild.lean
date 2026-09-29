-- Prove2me | Definitions.Def_RamificationChain_Wild
-- name    : RamificationChain_Wild
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/2b6ee890-e39a-5393-b2e4-8d5bedf958eb
-- title:
--   Weighted subgroup-chain sums and a Hasse–Arf divisibility predicate
-- statement:
--   Fix a group $G$. The module introduces three pieces of vocabulary for bookkeeping with a sequence of subgroups $Gs : \mathbb{N} \to \mathrm{Subgroup}\,G$ together with a weight function $cod : \mathrm{Subgroup}\,G \to \mathbb{N}$.
--
--   First, `wildSum Gs cod N` is the truncated weighted sum
--   $$\sum_{i=1}^{N} \#(Gs\,i)\cdot cod(Gs\,i),$$
--   the index ranging over the integer interval `Finset.Icc 1 N` and $\#$ being `Nat.card` of the subgroup (so the contribution of an infinite subgroup is $0$). Second, `wildDeltaChain Gs cod N` is `wildSum Gs cod N` divided by $\#(Gs\,0)$ in the natural numbers; this is truncating division, so the value agrees with the rational quotient exactly when $\#(Gs\,0)$ divides the weighted sum. Third, `HasseArfChain Gs` is the predicate asserting that for every index $i$ with $Gs\,i \neq Gs\,(i+1)$ one has
--   $$\#(Gs\,0) \ \Big|\ \sum_{j=1}^{i} \#(Gs\,j).$$
--
--   In the intended reading, $Gs$ is a ramification filtration in lower numbering and $cod$ the codimension of a fixed space, so that `wildSum` is the numerator of a wild Artin/Swan contribution and `wildDeltaChain` the contribution itself; `HasseArfChain` records the integrality of the corresponding upper-numbering breaks, which the Hasse–Arf theorem supplies for abelian extensions. None of this is built into the definitions: no decrease, normality, finiteness or exhaustion of the chain $Gs$ is required, the weight $cod$ is an arbitrary $\mathbb{N}$-valued function on subgroups, and the condition in `HasseArfChain` is attached to the indices at which the given presentation $Gs$ changes value rather than to jumps of an intrinsically defined filtration. Any identification of $Gs$ with a ramification filtration, and of $cod$ with a codimension, is a hypothesis to be provided by the user of these definitions.
--
--   **Relation to Mathlib.** Mathlib has no such abstract chain bookkeeping; these are the project's own definitions, phrased purely in terms of Mathlib's `Subgroup`, `Nat.card` and `Finset.Icc`.
--
--   **Where it is used.** These are the abstract counting primitives used in the conductor computations for the Frey curve and its associated Galois representations, where the wild part of a conductor exponent is a weighted sum over a ramification filtration divided by the order of the inertia group, and where integrality of the quotient is guaranteed by a Hasse–Arf type divisibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RamificationChain_Wild.lean

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Intervals

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace RamificationChain

variable {G : Type*} [Group G]

noncomputable def wildSum (Gs : ℕ → Subgroup G) (cod : Subgroup G → ℕ) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 N, Nat.card ↥(Gs i) * cod (Gs i)

noncomputable def wildDeltaChain (Gs : ℕ → Subgroup G) (cod : Subgroup G → ℕ) (N : ℕ) : ℕ :=
  wildSum Gs cod N / Nat.card ↥(Gs 0)

def HasseArfChain (Gs : ℕ → Subgroup G) : Prop :=
  ∀ i : ℕ, Gs i ≠ Gs (i + 1) →
    Nat.card ↥(Gs 0) ∣ ∑ j ∈ Finset.Icc 1 i, Nat.card ↥(Gs j)

end RamificationChain


