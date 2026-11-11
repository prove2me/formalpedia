-- Prove2me | Definitions.Def_NoMenuRevenue186_TrustedXOS_Auction
-- name    : NoMenuRevenue186_TrustedXOS_Auction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:19.969597+00:00
-- url     : https://prove2.me/theorems/e050be11-e2c1-4129-85b2-61d7f5dbfa67
-- title:
--   Hidden priors, buyer incentives, and deterministic revenue benchmarks
-- statement:
--   There are $n$ items and one buyer. Bundles are subsets of $\mathrm{Fin}(n)$. Valid valuations are nonnegative monotone real functions with value zero at the empty bundle; the XOS predicate is the published finite maximum of additive nonnegative clauses. A finite outer law $\mathcal D$ samples an actual finite prior $D$, then $D$ samples $v$. A protocol has a public binary tree with fixed leaf bundles and nonnegative real payments, a seller strategy depending only on $D$, and a buyer strategy depending only on $v$.
--
--   On each jointly supported $(D,v)$, ex-post IR requires $v(T)-p\ge0$, and buyer-PIC requires the prescribed strategy to maximize this utility over every complete buyer strategy against the prescribed seller strategy. Its revenue is
--
--   $$\mathrm{Rev}(\Pi)=\mathbb E_{D\sim\mathcal D}\mathbb E_{v\sim D}[p_\Pi(D,v)],\qquad
--   \mathrm{Opt}=\mathbb E_{D\sim\mathcal D}[\mathrm{Opt}(D)].$$
--
--   The known-prior benchmark optimizes direct allocation/payment tables on the finite support, with every IC comparison and the no-trade outside option. The buy-many benchmark optimizes nonnegative subadditive bundle prices and utility-maximizing choices, including no trade. Normalization and monotonicity of prices are not imposed. Both values are real suprema of feasible revenues; maximum attainment is a separate explicit predicate asserted for the goal's witnesses. Exact rational precision and the epsilon/threshold definition of little-o are also provided.
--
--   These definitions keep the optimization over mechanisms and the averaging over priors in their source order.
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.8–11, PDF p.10–13, Sections 2.1–2.3; Section 3.1

import Mathlib
import Definitions.Def_DSICHardRev_ValuationClasses
import Definitions.Def_NoMenuRevenue186_TrustedXOS_FiniteLaw
import Definitions.Def_NoMenuRevenue186_TrustedXOS_BinaryTree

namespace NoMenuRevenue186.TrustedXOS

abbrev Bundle (n : ℕ) := Finset (Fin n)
abbrev Valuation (n : ℕ) := Bundle n → ℝ
abbrev Prior (n : ℕ) := FiniteLaw (Valuation n)
abbrev Instance (n : ℕ) := FiniteLaw (Prior n)

/-- The valuation convention of Section 2.1. -/
def IsValuation {n : ℕ} (v : Valuation n) : Prop :=
  v ∅ = 0 ∧ (∀ T, 0 ≤ v T) ∧ Monotone v

def XOSInstance {n : ℕ} (H : Instance n) : Prop :=
  ∀ D ∈ H.law.support, ∀ v ∈ D.law.support, IsValuation v ∧ DSICHardRev.IsXOS v

/-- An exact rational representation with numerator and denominator of at most b bits. -/
def Precision {n : ℕ} (H : Instance n) (b : ℕ) : Prop :=
  ∀ D ∈ H.law.support, ∀ v ∈ D.law.support, ∀ T,
    ∃ a d : ℕ, a < 2 ^ b ∧ 0 < d ∧ d < 2 ^ b ∧ v T = (a : ℝ) / (d : ℝ)

structure Outcome (n : ℕ) where
  bundle : Bundle n
  payment : ℝ
  payment_nonneg : 0 ≤ payment

def noTrade (n : ℕ) : Outcome n := ⟨∅, 0, le_rfl⟩

def utility {n : ℕ} (v : Valuation n) (o : Outcome n) : ℝ := v o.bundle - o.payment

/-- Prescriptions depend only on the party's actual private input. Total extensions
    outside the marginal supports are unconstrained and carry no incentive requirement. -/
structure Protocol (n : ℕ) where
  tree : BinaryTree (Outcome n)
  seller : Prior n → Strategy
  buyer : Valuation n → Strategy

namespace Protocol
variable {n : ℕ}

def outcome (P : Protocol n) (D : Prior n) (v : Valuation n) : Outcome n :=
  P.tree.run (P.seller D) (P.buyer v) []

def cc (P : Protocol n) : ℕ := P.tree.depth

def IR (P : Protocol n) (H : Instance n) : Prop :=
  ∀ D ∈ H.law.support, ∀ v ∈ D.law.support, 0 ≤ utility v (P.outcome D v)

def PIC (P : Protocol n) (H : Instance n) : Prop :=
  ∀ D ∈ H.law.support, ∀ v ∈ D.law.support, ∀ b : Strategy,
    utility v (P.tree.run (P.seller D) b []) ≤ utility v (P.outcome D v)

def Feasible (P : Protocol n) (H : Instance n) : Prop := P.IR H ∧ P.PIC H

noncomputable def revenue (P : Protocol n) (H : Instance n) : ℝ :=
  H.expect (fun D => D.expect (fun v => (P.outcome D v).payment))
end Protocol

/-- Direct finite-support allocation/payment tables: all support-to-support IC
    comparisons and the outside option. They encode unrestricted deterministic mechanisms. -/
def DirectFeasible {n : ℕ} (D : Prior n) (M : Valuation n → Outcome n) : Prop :=
  ∀ v ∈ D.law.support, 0 ≤ utility v (M v) ∧
    ∀ w ∈ D.law.support, utility v (M w) ≤ utility v (M v)

noncomputable def deterministicRevenues {n : ℕ} (D : Prior n) : Set ℝ :=
  {r | ∃ M : Valuation n → Outcome n, DirectFeasible D M ∧
    r = D.expect (fun v => (M v).payment)}

noncomputable def opt {n : ℕ} (D : Prior n) : ℝ := sSup (deterministicRevenues D)

noncomputable def Opt {n : ℕ} (H : Instance n) : ℝ := H.expect opt

/-- Buy-many benchmark: arbitrary nonnegative subadditive prices, with a free
    no-trade option and an arbitrary utility-maximizing selection. Prices need
    not be normalized or monotone. Section 2.3, printed p.10. -/
def BuyManyPrices {n : ℕ} (p : Bundle n → ℝ) : Prop :=
  (∀ T, 0 ≤ p T) ∧ ∀ S T, p (S ∪ T) ≤ p S + p T

def menuUtility {n : ℕ} (v : Valuation n) (p : Bundle n → ℝ) : Option (Bundle n) → ℝ
  | none => 0
  | some T => v T - p T

def menuPayment {n : ℕ} (p : Bundle n → ℝ) : Option (Bundle n) → ℝ
  | none => 0
  | some T => p T

def BuyManyFeasible {n : ℕ} (D : Prior n) (p : Bundle n → ℝ)
    (choice : Valuation n → Option (Bundle n)) : Prop :=
  BuyManyPrices p ∧ ∀ v ∈ D.law.support, ∀ T : Option (Bundle n),
    menuUtility v p T ≤ menuUtility v p (choice v)

noncomputable def buyManyRevenues {n : ℕ} (D : Prior n) : Set ℝ :=
  {r | ∃ (p : Bundle n → ℝ) (choice : Valuation n → Option (Bundle n)),
    BuyManyFeasible D p choice ∧ r = D.expect (fun v => menuPayment p (choice v))}

noncomputable def optBM {n : ℕ} (D : Prior n) : ℝ := sSup (buyManyRevenues D)
noncomputable def OptBM {n : ℕ} (H : Instance n) : ℝ := H.expect optBM

/-- Attainment and real upper bounds are explicit obligations, never hypotheses
    substituted for a hard instance's benchmark. -/
def BenchmarksAttained {n : ℕ} (H : Instance n) : Prop :=
  ∀ D ∈ H.law.support,
    IsGreatest (deterministicRevenues D) (opt D) ∧
    IsGreatest (buyManyRevenues D) (optBM D)

/-- Explicit epsilon/threshold form of a little-o relation for sequences. -/
def LittleO (a b : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ i ≥ M, |a i| ≤ η * |b i|

end NoMenuRevenue186.TrustedXOS


