-- Prove2me | Definitions.Def_WildeQIT_Wiretap_privInfo
-- name    : WildeQIT_Wiretap_privInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:28:01.652999+00:00
-- url     : https://prove2.me/theorems/df18961e-ccb1-463c-a5c3-102e0fe17b47
-- title:
--   Private information $P(N)=\max_{p_{U,X}}[I(U;Y)-I(U;Z)]$ of a wiretap channel
-- statement:
--   The **private information** of a classical wiretap channel $N\equiv p_{Y,Z|X}$ (Definition 13.2.1) is
--
--   $$
--   P(N)\equiv\max_{p_{U,X}(u,x)}\bigl[I(U;Y)-I(U;Z)\bigr],
--   $$
--
--   where $U$ is an auxiliary random variable of arbitrary finite alphabet, $p_{U,X}$ is any joint distribution of $U$ and the channel input, and $(U,Y,Z)$ is distributed as $\sum_x p_{U,X}(u,x)\,p_{Y,Z|X}(y,z|x)$.
--
--   It measures how much more correlation Alice can establish with Bob than with Eve; it is non-negative and additive over independent wiretap channels.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second). The auxiliary alphabet ranges over $\{0,\dots,n-1\}$ for every $n\in\mathbb N$, which up to relabeling is every finite alphabet. The maximum is written as a supremum of the set of values $I(U;Y)-I(U;Z)$, since the book does not prove that it is attained. The set is bounded above by $\log_2|\mathcal Y|$, so the supremum is a finite real number when the input alphabet is nonempty; for an empty input alphabet Lean returns the junk value $0$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.2.1, eq. (13.57), p. 396

import Definitions.Def_WildeQIT_Wiretap_wiretapJoint
import Definitions.Def_WildeQIT_mutualInfo

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Private information of a classical wiretap channel** (Definition 13.2.1).
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.2.1, (13.57),
p. 396: `P(N) ≡ max_{p_{U,X}(u,x)} [I(U; Y) − I(U; Z)]` for a wiretap channel `N ≡ p_{Y,Z|X}`.

`privInfo N` is the supremum of `I(U; Y) − I(U; Z)` (in bits) over every finite auxiliary
alphabet `Fin n` (`n ∈ ℕ`) and every joint distribution `p_{U,X}` on `Fin n × α`, where `(U, Y, Z)`
has the distribution `wiretapJoint p N`.

**Formalization Note.** The book places no bound on the size of `U`; every finite alphabet is in
bijection with some `Fin n` and mutual information is invariant under relabeling, so ranging
over `Fin n` for all `n` is the book's range. The `max` is a supremum (the book does not prove
attainment). The set of values is bounded above by `log₂ |𝒴|` (`I(U;Y) ≤ H(Y)`,
`I(U;Z) ≥ 0`), so the real `sSup` is the book's quantity when the input alphabet is nonempty;
for an empty input alphabet the set is empty and the value is the junk `0`. -/
noncomputable def privInfo {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (N : WiretapChannel α β γ) : ℝ :=
  sSup {r : ℝ | ∃ (n : ℕ) (p : FinDist (Fin n × α)),
    r = mutualInfo (wiretapJoint p N).margXY - mutualInfo (wiretapJoint p N).margXZ}

end WildeQIT.Wiretap


