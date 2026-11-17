-- Prove2me | Definitions.Def_DSICHardRev_Supplement_TwoSimAlg
-- name    : DSICHardRev_Supplement_TwoSimAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:09:36.042528+00:00
-- url     : https://prove2.me/theorems/99e34b59-8e1b-4a68-ac94-f46a1429c563
-- title:
--   Randomized simultaneous algorithms for two bidders, expected welfare and communication
-- statement:
--   Fix two bidders and the item set $M=[m]$. An **allocation** is a pair $(S_1,S_2)$ of disjoint bundles (items may stay unallocated).
--
--   A **simultaneous algorithm** (Definitions 2.4–2.5) consists of
--   1. for each bidder $i$, a finite message alphabet of size $K_i$ and a message rule that maps bidder $i$'s own valuation $v_i$ to a probability distribution over messages (private, independent randomness);
--   2. a referee that maps the pair of messages to a probability distribution over allocations.
--
--   On a profile $(v_1,v_2)$ its **expected welfare** is $\mathbb E[v_1(S_1)+v_2(S_2)]$ over both bidders' coins and the referee's coins. Its **communication** is $\sum_i\lceil\log_2 K_i\rceil$ bits. It attains a **$\rho$-approximation** on a domain $\mathcal D$ (Definition 2.2, ratio $\rho=1/\eta\le1$) if on every profile from $\mathcal D$
--   $$
--   \mathbb E\big[v_1(S_1)+v_2(S_2)\big]\;\ge\;\rho\cdot\max_{(T_1,T_2)}\big(v_1(T_1)+v_2(T_2)\big).
--   $$
--
--   This is the model of the two-bidder simultaneous results, Theorems 1.4 and 1.6.
--
--   **Formalization Note** Distributions are Mathlib `PMF`s, so each alphabet is automatically nonempty; a deterministic algorithm is the case of point masses. The maximum over allocations is written as an inequality for every pair of disjoint bundles $T$, with no division. The communication convention is the base mission's `SimAlg.comm`.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2–§2.1 pp.7–8: Definitions 2.1, 2.2, 2.4, 2.5 and the blackboard model

import Mathlib
import Definitions.Def_DSICHardRev_Protocol

namespace DSICHardRev

namespace Supplement

/-!
# Randomized simultaneous algorithms for two bidders

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2–§2.1, pp.7–8: Definition 2.1 (allocation rule,
possibly random), Definition 2.2 (approximation ratio, in expectation), the blackboard model
("each bidder simultaneously sends a (possibly random) message"), Definition 2.4 (algorithm,
communication = worst-case transcript length), Definition 2.5 (simultaneous algorithm).

**Formalization Note.**
* Two bidders `Fin 2`, items `Fin m`. An allocation `Alloc2 m` is a pair of disjoint bundles
  (items may stay unallocated).
* A simultaneous algorithm (`TwoSimAlg m`) has a message alphabet `Fin (K i)` for each bidder.
  Bidder `i`'s message rule maps bidder `i`'s **own** valuation to a probability distribution
  (`PMF`) on its alphabet (private coins, independent across bidders); the referee maps the pair of
  messages to a probability distribution over allocations. A deterministic algorithm is the special
  case of point masses. Since a `PMF` on an empty type does not exist, `K i ≥ 1` automatically.
* `expWelfare A v` is the expected welfare `E[v₁(S₁) + v₂(S₂)]` on the profile `v`: a finite sum
  over message pairs and allocations of (product of the message probabilities) × (referee
  probability) × welfare.
* `comm A = ∑ i, ⌈log₂ (K i)⌉` bits (`Nat.clog 2`), the worst-case transcript length of one
  round in which each bidder writes a fixed-length message, as in the published `SimAlg.comm`.
* `IsApproxRatio A D ρ` (Definition 2.2 with the ratio `1/η = ρ ≤ 1` stated as on p.8): on every
  profile from `D`, every allocation `T` satisfies `ρ · welfare(T) ≤ expWelfare`; i.e.
  `E[welfare] ≥ ρ · OPT`, worst case over profiles, expectation over the algorithm's coins only.
-/

/-- Allocations to two bidders: a pair of disjoint bundles of the items `Fin m`. -/
def Alloc2 (m : ℕ) : Type := {S : Fin 2 → Finset (Fin m) // Disjoint (S 0) (S 1)}

instance (m : ℕ) : Fintype (Alloc2 m) := by
  unfold Alloc2
  infer_instance

/-- A (possibly randomized) simultaneous algorithm for two bidders on the items `Fin m`
(Definitions 2.4, 2.5): each bidder sends a random message drawn from a distribution that depends
only on its own valuation, and a referee draws an allocation from a distribution that depends only
on the two messages. -/
structure TwoSimAlg (m : ℕ) where
  /-- The size of bidder `i`'s message alphabet `Fin (K i)`. -/
  K : Fin 2 → ℕ
  /-- Bidder `i`'s message rule: a distribution over messages for each valuation of bidder `i`. -/
  msg : (i : Fin 2) → (Finset (Fin m) → ℝ) → PMF (Fin (K i))
  /-- The referee: a distribution over allocations for each pair of messages. -/
  referee : ((i : Fin 2) → Fin (K i)) → PMF (Alloc2 m)

namespace TwoSimAlg

variable {m : ℕ}

/-- Expected welfare of the algorithm on the profile `v` (expectation over both bidders' coins and
the referee's coins). -/
noncomputable def expWelfare (A : TwoSimAlg m) (v : Fin 2 → Finset (Fin m) → ℝ) : ℝ :=
  ∑ a : (i : Fin 2) → Fin (A.K i), (∏ i, (A.msg i (v i) (a i)).toReal) *
    ∑ S : Alloc2 m, (A.referee a S).toReal * Mechanism.welfare v S.1

/-- Communication of the algorithm: `∑ i, ⌈log₂ (K i)⌉` bits. -/
def comm (A : TwoSimAlg m) : ℕ := ∑ i, Nat.clog 2 (A.K i)

/-- The algorithm attains a `ρ`-approximation on the domain `D` (Definition 2.2): on every
profile from `D`, every allocation `T` satisfies `ρ · welfare(T) ≤ E[welfare]`. -/
def IsApproxRatio (A : TwoSimAlg m) (D : Set (Finset (Fin m) → ℝ)) (ρ : ℝ) : Prop :=
  ∀ v : Fin 2 → Finset (Fin m) → ℝ, (∀ i, v i ∈ D) →
    ∀ T : Fin 2 → Finset (Fin m), (Pairwise fun a b => Disjoint (T a) (T b)) →
      ρ * Mechanism.welfare v T ≤ A.expWelfare v

end TwoSimAlg

end Supplement

end DSICHardRev


