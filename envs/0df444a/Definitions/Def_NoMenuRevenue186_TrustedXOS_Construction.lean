-- Prove2me | Definitions.Def_NoMenuRevenue186_TrustedXOS_Construction
-- name    : NoMenuRevenue186_TrustedXOS_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:00.201719+00:00
-- url     : https://prove2.me/theorems/256fe2e6-0f42-4206-be66-2ebe5e9965e3
-- title:
--   Almost-disjoint bundle instance with actual seller priors
-- statement:
--   Let $\mathcal F$ be a family of $k$-item bundles with pairwise intersections at most $\epsilon k$, where $k>0$ and $0<\epsilon<1$. Let $K\ge1$, $V=2^K$, $N=|\mathcal F|=4R$, and let $R>0$ be divisible by $2V-1$. Set
--
--   $$m_j=\frac{R2^{K-j}}{2V-1},\qquad W_K=2-2^{-K},\qquad
--   w_B(T)=\max_{S\in B}\frac{|T\cap S|}{k},\qquad v_{B,2^j}=2^j w_B.$$
--
--   A seed consists of an $R$-element subcollection $A$ and labels with exactly $m_j$ occurrences of index $j$. The actual prior $D_{A,u}$ chooses $S^*$ uniformly in $A$, chooses $R-1$ fillers uniformly outside $A$, and returns $v_{\{S^*\}\cup H,2^{u(S^*)}}$. The outer law uniformly samples $A$ and balanced labels and pushes forward to the actual prior, merging equal mass functions. The seller is never given the seed separately.
--
--   The validity predicate contains only the size, positivity, divisibility, and intersection assumptions. It does not assume any valuation bounds, recoverability, revenue extraction, or communication lower bound. Separate predicates express the elementary valuation properties and prior recovery for use in audits. Applicability of the buy-many branch requires $\epsilon V<1-\epsilon$.
--
--   This is the concrete finite construction underlying the supporting statements and the full goal.
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.14–16, PDF p.16–18, Sections 4.1–4.2

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Auction

namespace NoMenuRevenue186.TrustedXOS

/-- Exact-size almost-disjoint family (Section 4.1, printed pp.14–15). -/
def Separated {n : ℕ} (F : Finset (Bundle n)) (k : ℕ) (ε : ℝ) : Prop :=
  (∀ S ∈ F, S.card = k) ∧
  ∀ S ∈ F, ∀ T ∈ F, S ≠ T → ((S ∩ T).card : ℝ) ≤ ε * (k : ℝ)

/-- Parameters, not a structure bundling any consequences of the construction. -/
structure Construction (n : ℕ) where
  F : Finset (Bundle n)
  k : ℕ
  K : ℕ
  R : ℕ
  ε : ℝ

namespace Construction
variable {n : ℕ}

def V (C : Construction n) : ℕ := 2 ^ C.K

def Valid (C : Construction n) : Prop :=
  0 < C.k ∧ 0 < C.ε ∧ C.ε < 1 ∧ 1 ≤ C.K ∧ 0 < C.R ∧
  C.F.card = 4 * C.R ∧ (2 * C.V - 1) ∣ C.R ∧ Separated C.F C.k C.ε

def count (C : Construction n) (j : Fin (C.K + 1)) : ℕ :=
  C.R * 2 ^ (C.K - j.val) / (2 * C.V - 1)

noncomputable def W (C : Construction n) : ℝ := 2 - (2 : ℝ) ^ (-(C.K : ℤ))

/-- Maximum over the actual finite collection; the empty collection is unused
    by valid inputs and is assigned the zero valuation. -/
noncomputable def base (C : Construction n) (B : Finset (Bundle n)) (T : Bundle n) : ℝ := by
  classical
  exact if h : B.Nonempty then B.sup' h (fun S => ((T ∩ S).card : ℝ) / (C.k : ℝ)) else 0

noncomputable def value (C : Construction n) (B : Finset (Bundle n))
    (j : Fin (C.K + 1)) : Valuation n :=
  fun T => (2 : ℝ) ^ j.val * C.base B T

/-- A finite carrier used only to sample; the seller never receives this seed.
    Labels outside A are set to zero to give a canonical extension. -/
abbrev Seed (C : Construction n) := Finset (Bundle n) × (Bundle n → Fin (C.K + 1))

noncomputable def seeds (C : Construction n) : Finset C.Seed := by
  classical
  exact Finset.univ.filter (fun a => a.1 ⊆ C.F ∧ a.1.card = C.R ∧
    (∀ S, S ∉ a.1 → a.2 S = 0) ∧
    ∀ j : Fin (C.K + 1), (a.1.filter (fun S => a.2 S = j)).card = C.count j)

noncomputable def seedLaw (C : Construction n) : FiniteLaw C.Seed :=
  FiniteLaw.uniform C.seeds (∅, fun _ => 0)

/-- The actual seller prior: sample the common bundle and the R−1 fillers,
    then push forward to valuation functions. Equal priors are the same input. -/
noncomputable def prior (C : Construction n) (a : C.Seed) : Prior n := by
  classical
  exact (FiniteLaw.uniform a.1 ∅).bind (fun S =>
    (FiniteLaw.uniform ((C.F \ a.1).powersetCard (C.R - 1)) ∅).map
      (fun H => C.value (insert S H) (a.2 S)))

noncomputable def instanceLaw (C : Construction n) : Instance n :=
  C.seedLaw.map C.prior

/-- Supported tuples in the source parameterization. This predicate is used for
    pointwise conclusions; it grants neither party the seed of the other. -/
def Supported (C : Construction n) (a : C.Seed) (B : Finset (Bundle n))
    (S : Bundle n) : Prop :=
  a ∈ C.seeds ∧ B ⊆ C.F ∧ B.card = C.R ∧ a.1 ∩ B = {S}

/-- Both are consequences to be checked against the definitions, not assumptions
    in Valid: actual prior/valuation recovery and nonempty sampling domains. -/
def Recovery (C : Construction n) : Prop :=
  C.seeds.Nonempty ∧
  (∀ a ∈ C.seeds, ((C.F \ a.1).powersetCard (C.R - 1)).Nonempty) ∧
  (∀ a ∈ C.seeds, ∀ a' ∈ C.seeds, C.prior a = C.prior a' → a = a') ∧
  (∀ B ⊆ C.F, B.Nonempty → ∀ j : Fin (C.K + 1),
    C.value B j Finset.univ = (2 : ℝ) ^ j.val ∧
    ∀ S ∈ C.F, (C.value B j S = (2 : ℝ) ^ j.val ↔ S ∈ B))

/-- The concrete elementary properties on printed p.15. -/
def ValuationProperties (C : Construction n) : Prop :=
  ∀ B ⊆ C.F, B.Nonempty →
    IsValuation (C.base B) ∧
    (∀ T, 0 ≤ C.base B T ∧ C.base B T ≤ 1) ∧
    (∀ S ∈ B, C.base B S = 1) ∧
    (∀ S ∈ C.F \ B, C.base B S ≤ C.ε) ∧
    ∀ j : Fin (C.K + 1), DSICHardRev.IsXOS (C.value B j)

/-- Which of Proposition 4.6's two benchmarks is applicable. No buy-many
    restriction is imposed on the protocol whose communication is bounded. -/
def Applicable (C : Construction n) (α : ℝ) (P : Protocol n) : Prop :=
  Opt C.instanceLaw / α ≤ P.revenue C.instanceLaw ∨
  (C.ε * (C.V : ℝ) < 1 - C.ε ∧ OptBM C.instanceLaw / α ≤ P.revenue C.instanceLaw)

end Construction
end NoMenuRevenue186.TrustedXOS


