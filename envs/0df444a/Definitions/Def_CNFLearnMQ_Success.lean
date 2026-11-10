-- Prove2me | Definitions.Def_CNFLearnMQ_Success
-- name    : CNFLearnMQ_Success
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:45.949718+00:00
-- url     : https://prove2.me/theorems/ed8cd899-a1e1-4294-b419-9a748ef42da3
-- title:
--   Success events $E_{\mathrm{seed}}$, $E_{\mathrm{grow}}$, $E_{\mathrm{prob}}$, $E_{\mathrm{core}}$, $q_s(b)$, and approximate learning
-- statement:
--   For a satisfiable $\Phi$ with uniform solution law $\mu_\Phi$:
--
--   1. The **conditional core probability** $q_s(b)=\Pr_{X\sim\mu_\Phi}[\,b\in\mathcal C(\mathcal R_X)\mid X_S=\sigma_S\,]$ for $q_s>0$.
--   2. $\mathcal R=\bigcup_i\mathcal R_{X_i}$, the union of the exact core families of samples $X_1,\dots,X_N$.
--   3. $E_{\mathrm{seed}}$: the initial queue contains a subclause of every target clause.
--   4. $E_{\mathrm{grow}}$: every LearnCore call made within ExtendSubclause recovers all cores of its input.
--   5. $E_{\mathrm{prob}}$: for every subclause $s$ of width at most $k$, $\widehat q_s\le 2\eta\Rightarrow q_s\le 3\eta$ and $\widehat q_s>2\eta\Rightarrow q_s\ge\eta$.
--   6. $\widetilde q_s(b)$ (eq. (13)): the fraction of the first $N_{\mathrm{ext}}$ pool samples violating $s$ whose exact core family induces $b$.
--   7. $E_{\mathrm{core}}$: for all $s,b$ with $q_s>0$, $S\cap B=\emptyset$ and $1\le|B|\le k-|S|$, $\widetilde q_s(b)\le q_s(b)+\phi$ whenever at least $N_{\mathrm{ext}}$ pool samples violate $s$.
--   8. **Approximate learning** (Definition 1.3): an output succeeds if it is a formula $\widehat\Phi$ (not $\bot$), $\widehat\Phi$ is satisfiable, and $d_{\mathrm{TV}}(\mu_\Phi,\mu_{\widehat\Phi})\le\varepsilon$.
--
--   **Formalization Note** $q_s(b)$ is computed as $\Pr[b\in\mathcal C(\mathcal R_X)\wedge X\text{ violates }s]/q_s$; it is used only where $q_s>0$. $d_{\mathrm{TV}}$ is the published `HybridXorLift.tvDist`, half the $\ell_1$ distance.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Definition 1.3, p.4; p.26; Definitions 5.4, 5.16, 5.21 and eq. (13), pp.21, 33, 35

import Mathlib
import Definitions.Def_CNFLearnMQ_learnCNF
import Definitions.Def_CNFLearnMQ_memOracle

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

variable {n : ℕ}

/-- The conditional core probability `q_s(b) = P_{X∼µ_Φ}[b ∈ C(R_X) | X_S = σ_S]` (Feng, Yu, Zhang,
STOC 2027 submission (manuscript sha256 519ee6d4…), p.26), computed as
`P[b ∈ C(R_X) ∧ X violates s] / q_s`.

**Formalization Note** The paper defines `q_s(b)` only for `q_s > 0`; every statement that uses it
assumes `q_s > 0` (or `q_s ≥ η > 0`). For `q_s = 0` Lean's division returns `0`. -/
noncomputable def qcond (Φ : CNF n) (h : (solutions Φ).Nonempty) (s b : Clause n) : ℝ :=
  eventProb (solutionLaw Φ h) (fun X => b ∈ inducedFamily X (cores Φ X) ∧ Violates s X) / q Φ h s

/-- The union `R = ⋃ᵢ R_{Xᵢ}` of the exact core families of the samples `X_1, …, X_N`
(Definition 5.4, p.21). -/
noncomputable def coreUnion (Φ : CNF n) (Xs : List (Assignment n)) : Finset (Finset (Fin n)) :=
  (Xs.map (cores Φ)).foldr (· ∪ ·) ∅

/-- The event `E_seed` (Definition 5.16 item 1, p.33): the initial queue contains a subclause of
every target clause. -/
def ESeed (Φ : CNF n) (Q : List (Clause n)) : Prop := ∀ c ∈ Φ, ∃ s ∈ Q, Subclause s c

/-- The event `E_grow` (Definition 5.16 item 2, p.33): every LearnCore call made within
ExtendSubclause recovers all cores of its input solution. -/
def EGrow (Φ : CNF n) (calls : List (ExtCall n)) : Prop :=
  ∀ call ∈ calls, call.Rs = call.Zs.map (cores Φ)

/-- The event `E_prob` on the pool `Y` (Definition 5.16 item 3, p.33): for every subclause `s` of
width at most `k`, `q̂_s ≤ 2η` implies `q_s ≤ 3η`, and `q̂_s > 2η` implies `q_s ≥ η`. -/
def EProb (Φ : CNF n) (h : (solutions Φ).Nonempty) (k : ℕ) (η : ℝ) (Y : List (Assignment n)) :
    Prop :=
  ∀ s : Clause n, width s ≤ k →
    (qhatPool Y s ≤ 2 * η → q Φ h s ≤ 3 * η) ∧ (2 * η < qhatPool Y s → η ≤ q Φ h s)

/-- `q̃_s(b)` of eq. (13), p.35: the fraction of the first `N` pool samples violating `s` whose exact
core family induces `b`. -/
noncomputable def qtilde (Φ : CNF n) (N : ℕ) (Y : List (Assignment n)) (s b : Clause n) : ℝ :=
  qhatCore N (firstViolating Y s N) ((firstViolating Y s N).map (cores Φ)) b

/-- The event `E_core` on the pool `Y` (Definition 5.21, p.35), with `N = N_ext` and tolerance `ϕ`:
for every pair of subclauses `s = (S, σ_S)`, `b = (B, τ_B)` with `q_s > 0`, `S ∩ B = ∅` and
`1 ≤ |B| ≤ k − |S|`, `q̃_s(b) ≤ q_s(b) + ϕ` whenever at least `N` samples of `Y` violate `s`. -/
def ECore (Φ : CNF n) (h : (solutions Φ).Nonempty) (k N : ℕ) (ϕ : ℝ) (Y : List (Assignment n)) :
    Prop :=
  ∀ s b : Clause n, 0 < q Φ h s → Disjoint (support s) (support b) → 1 ≤ width b →
    width b + width s ≤ k → N ≤ (firstViolating Y s (Y.length)).length →
    qtilde Φ N Y s b ≤ qcond Φ h s b + ϕ

/-- Success of a learner's output (Feng, Yu, Zhang, §1, p.2: "The learner ... outputs an explicit satisfiable CNF formula Φ̂ on the same variables. ... For approximate learning, we require d_TV(µ_Φ, µ_Φ̂) ≤ ε"): the
output is a formula `Φ̂` (not ⊥), `Φ̂` is satisfiable, and `d_TV(µ_Φ, µ_Φ̂) ≤ ε`. -/
def Success (Φ : CNF n) (h : (solutions Φ).Nonempty) (ε : ℝ) (out : Option (CNF n)) : Prop :=
  ∃ Φhat : CNF n, out = some Φhat ∧ ∃ h' : (solutions Φhat).Nonempty,
    HybridXorLift.tvDist (solutionLaw Φ h).prob (solutionLaw Φhat h').prob ≤ ε

end CNFLearnMQ


