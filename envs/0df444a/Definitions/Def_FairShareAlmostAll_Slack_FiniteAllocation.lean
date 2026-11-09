-- Prove2me | Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
-- name    : FairShareAlmostAll_Slack_FiniteAllocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:18.997183+00:00
-- url     : https://prove2.me/theorems/874d82a3-4476-4526-b88e-97acda3a9f0b
-- title:
--   Finite probability laws, partial allocations and fractional allocations
-- statement:
--   A finite probability law assigns a nonnegative real weight to each outcome, with total weight one. Event probabilities and expectations are finite sums. A partial allocation is a family of pairwise disjoint bundles, and a fractional allocation is nonnegative with total share at most one per good.
--
--   For singleton values $v$, entitlement $b$ and target $t$, a certificate is a law $D$ on all bundles with
--   $$D(P)>0\implies v(P)\ge t,\qquad \Pr_{P\sim D}(g\in P)\le b.$$
--   These interfaces retain empty bundles and unused goods, and do not assert that certificates or fair allocations exist.
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 2 (PDF p. 3), §1.1; §1.5, printed p. 7 (PDF p. 8); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

namespace FairShareAlmostAll.Slack

/-- A probability law on an arbitrary finite carrier, with no nonemptiness axiom. -/
structure FiniteLaw (α : Type) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

noncomputable def probability {α : Type} [Fintype α] (D : FiniteLaw α)
    (event : α → Prop) : ℝ := by
  classical
  exact ∑ a, if event a then D.weight a else 0

noncomputable def expectation {α : Type} [Fintype α] (D : FiniteLaw α)
    (f : α → ℝ) : ℝ := ∑ a, D.weight a * f a

/-- Empty bundles and unused goods are permitted. -/
def PartialAllocation {J U : Type} (A : J → Finset U) : Prop :=
  ∀ i k, i ≠ k → Disjoint (A i) (A k)

def FractionalAllocation {J U : Type} [Fintype J] (y : J → U → ℝ) : Prop :=
  (∀ i g, 0 ≤ y i g) ∧ ∀ g, ∑ i, y i g ≤ 1

noncomputable def certificate {m : ℕ} (v : Fin m → ℝ) (b t : ℝ)
    (D : FiniteLaw (Finset (Fin m))) : Prop :=
  (∀ P, 0 < D.weight P → t ≤ AnyPriceShare.Bidding.addVal v P) ∧
  ∀ g, probability D (fun P => g ∈ P) ≤ b

end FairShareAlmostAll.Slack


