-- Prove2me | Definitions.Def_FreyPackage_IsConductorLevel
-- name    : FreyPackage_IsConductorLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/8f875119-38bf-5bec-9bf0-b627ac50385f
-- title:
--   Squarefree levels supported on the primes dividing abc
-- statement:
--   For a Frey package $P$ (the project's packaging of a normalised putative counterexample to Fermat's Last Theorem, with integers `P.a`, `P.b`, `P.c` and exponent prime `P.p`) and a natural number $N$, the `Prop`-valued structure [`FreyPackage.IsConductorLevel P N`](../def/FreyPackage_IsConductorLevel.html#L8) records three conditions and no data: $N>0$ (`pos`); $N$ is squarefree in Mathlib's sense (`squarefree`); and every prime $q$ dividing $N$ satisfies $q \mid abc$ as an integer divisibility $(q:\mathbb Z) \mid P.a \cdot P.b \cdot P.c$ (`support`). Nothing about elliptic curves, conductors or modular forms enters the definition: it is the purely arithmetic statement that $N$ is a positive squarefree number all of whose prime factors divide $abc$, equivalently a positive divisor of $\operatorname{rad}(abc)$. No converse is demanded, so a prime dividing $abc$ need not divide $N$.
--
--   The remaining declarations are the immediate consequences used downstream. `of_dvd` says the property passes to any positive divisor $M \mid N$. `p_dvd_abc` says that if the exponent prime `P.p` divides $N$ then $(P.p : \mathbb Z) \mid abc$, and `not_p_dvd` is its contrapositive: if `P.p` does not divide $abc$ then `P.p` does not divide $N$. `sq_not_dvd` says $q^2 \nmid N$ for every prime $q$, and `not_four_dvd` is the case $q=2$, i.e. $4 \nmid N$.
--
--   **Relation to Mathlib.** Mathlib has no notion of a level supported on the bad primes of a Frey curve; `IsConductorLevel` is the project's own predicate, built from Mathlib's `Squarefree` and `Nat.Prime`.
--
--   **Where it is used.** This predicate is the level invariant carried through the level-lowering stage of the route: the entry point asserts the existence of some $N$ with `P.IsConductorLevel N` together with the project's modularity-of-level-$N$ property for the mod-$p$ representation of the Frey curve, and the successive lowering steps shrink $N$ while preserving `IsConductorLevel`, ending at level $2$. The helper lemmas are what make the descent uniform: squarefreeness removes any need for a higher-exponent or $4 \mid N$ analysis, and `not_p_dvd` isolates the case distinction at the exponent prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_IsConductorLevel.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace FreyPackage

structure IsConductorLevel (P : FreyPackage) (N : ℕ) : Prop where

  pos : 0 < N

  squarefree : Squarefree N

  support : ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ∣ P.a * P.b * P.c

namespace IsConductorLevel

variable {P : FreyPackage} {N : ℕ}

theorem of_dvd (h : P.IsConductorLevel N) {M : ℕ} (hMN : M ∣ N) (hM : 0 < M) :
    P.IsConductorLevel M :=
  ⟨hM, h.squarefree.squarefree_of_dvd hMN, fun q hq hqM => h.support q hq (hqM.trans hMN)⟩

theorem p_dvd_abc (h : P.IsConductorLevel N) (hpN : P.p ∣ N) :
    (P.p : ℤ) ∣ P.a * P.b * P.c :=
  h.support P.p P.pp hpN

theorem not_p_dvd (h : P.IsConductorLevel N) (hp : ¬ (P.p : ℤ) ∣ P.a * P.b * P.c) :
    ¬ P.p ∣ N :=
  fun hpN => hp (h.p_dvd_abc hpN)

theorem sq_not_dvd (h : P.IsConductorLevel N) {q : ℕ} (hq : q.Prime) : ¬ q ^ 2 ∣ N := by
  intro hsq
  exact Nat.squarefree_iff_prime_squarefree.mp h.squarefree q hq (by rwa [← pow_two])

theorem not_four_dvd (h : P.IsConductorLevel N) : ¬ 4 ∣ N := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  exact h4 ▸ h.sq_not_dvd Nat.prime_two

end IsConductorLevel

end FreyPackage


