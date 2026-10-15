-- Prove2me | Definitions.Def_FairGuarantees_BidChoose_Guarantees
-- name    : FairGuarantees_BidChoose_Guarantees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:10.538361+00:00
-- url     : https://prove2.me/theorems/acbd9a68-8215-42a9-b975-56fe3fedb401
-- title:
--   §5.1–5.2, pp. 16–19 — moving knife κ, benchmark measure θ, u^κ, indirect utility u^θ (5), Υ(n) and Γ^α (6)
-- statement:
--   Objects of the Moving Knife and Bid & Choose rules (§5.1–5.2), built on the model of `FairGuarantees.BidChoose.Setting`.
--
--   1. **Moving knife.** A path $\kappa:[0,1]\ni t\mapsto K(t)\in\mathcal B$ with $K(0)=\emptyset$, $K(1)=\Omega$, continuous for $\delta$, and strictly inclusion increasing: for $0\le t<t'\le1$, $K(t)\subsetneq K(t')$ and $|K(t')\setminus K(t)|>0$.
--   2. **Benchmark measure.** A measure $\theta$ carried by $\Omega$ with $\theta(\Omega)=1$, absolutely continuous with respect to Lebesgue measure on $\Omega$ and vice versa.
--   3. **Knife utility.** For $0\le t^1\le t^2\le1$, $u^\kappa(t^1,t^2)=u(K(t^2)\setminus K(t^1))$.
--   4. **Indirect utility (5).**
--   $$
--   u^\theta(t^1,t^2)=\inf_{T:\,\theta(T)=t^1}\ \sup_{S:\,S\cap T=\emptyset,\ \theta(S)=t^2-t^1}u(S),
--   $$
--   with $S,T$ ranging over shares.
--   5. **Sequences $\Upsilon(n)$.** $\tau=(t^k)_{0\le k\le n}$ with $t^0=0\le t^1\le\dots\le t^{n-1}\le 1=t^n$.
--   6. **Guarantees (6).** For $\alpha\in\{\kappa,\theta\}$,
--   $$
--   \Gamma^\alpha(u;n)=\sup_{\tau\in\Upsilon(n)}\ \min_{0\le k\le n-1}u^\alpha(t^k,t^{k+1}).
--   $$
--
--   $\Gamma^\kappa$ and $\Gamma^\theta$ are the utility levels the paper attaches to the Moving Knife rule $\mathrm{MK}^\kappa_n$ and the Bid & Choose rule $\mathrm{B\&C}^\theta_n$.
--
--   **Formalization Note.** The knife is a function `ℝ → Set (E d)` whose values outside $[0,1]$ play no role; continuity is stated with $\varepsilon$–$\eta$ for $\delta$ on $[0,1]$. Mutual absolute continuity is stated as `θ ≪ volume.restrict Ω` and `volume.restrict Ω ≪ θ` (the paper's "absolutely continuous … and vice versa"), together with $\theta(\Omega^c)=0$ and $\theta(\Omega)=1$; $\theta$-values are read through `toReal`, which is exact because $\theta$ is finite. The min/max in (5) and the max in (6) are read as inf/sup (p. 9). The sets are bounded because $u$ is bounded on shares; the inner set of (5) is nonempty on the triangle because $\theta$ has no atoms; and the set in (6) is nonempty for $n\ge1$ because $t^k=k/n$ lies in $\Upsilon(n)$. Off the triangle ($t^2<t^1$) and for $n=0$ the definitions return the junk value $0$; no theorem uses them there.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, pp. 16–19, §5.1 (moving knife, measure θ), §5.2 (u^κ, u^θ eq. (5), Υ(n), Γ^α eq. (6))

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting

open MeasureTheory

namespace FairGuarantees.BidChoose

variable {d : ℕ}

/-- §5.1, pp. 16–17: a moving knife `κ : [0, 1] ∋ t ↦ K(t)`: from `K(0) = ∅` to `K(1) = Ω`,
through shares, `δ`-continuous on `[0, 1]`, and strictly inclusion increasing with
positive-measure increments. Values of `K` outside `[0, 1]` play no role. -/
def IsKnife (Ω : Set (FairGuarantees.DivideChoose.E d)) (K : ℝ → Set (FairGuarantees.DivideChoose.E d)) : Prop :=
  K 0 = ∅ ∧ K 1 = Ω ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, FairGuarantees.DivideChoose.IsShare Ω (K t)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ε > 0, ∃ η > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |t - s| < η → FairGuarantees.DivideChoose.δ (K t) (K s) < ε) ∧
    ∀ t t' : ℝ, 0 ≤ t → t < t' → t' ≤ 1 → K t ⊂ K t' ∧ 0 < volume (K t' \ K t)

/-- §5.1, p. 17: a benchmark measure `θ`: a measure carried by `Ω`, normalised to
`θ(Ω) = 1`, mutually absolutely continuous with Lebesgue measure on `Ω`. -/
def IsBenchmark (Ω : Set (FairGuarantees.DivideChoose.E d)) (θ : Measure (FairGuarantees.DivideChoose.E d)) : Prop :=
  θ Ωᶜ = 0 ∧ θ Ω = 1 ∧ θ ≪ volume.restrict Ω ∧ volume.restrict Ω ≪ θ

/-- §5.2, p. 18: the knife utility `u^κ(t¹, t²) = u(K(t²) ∖ K(t¹))`. -/
def uKnife (u : Set (FairGuarantees.DivideChoose.E d) → ℝ) (K : ℝ → Set (FairGuarantees.DivideChoose.E d)) (t₁ t₂ : ℝ) : ℝ :=
  u (K t₂ \ K t₁)

/-- §5.2, p. 18, display (5): the indirect utility
`u^θ(t¹, t²) = min_{T : θ(T) = t¹} max_{S : S ∩ T = ∅, θ(S) = t² - t¹} u(S)`, over shares,
with min/max read as inf/sup (p. 9). -/
noncomputable def uBid (Ω : Set (FairGuarantees.DivideChoose.E d)) (θ : Measure (FairGuarantees.DivideChoose.E d)) (u : Set (FairGuarantees.DivideChoose.E d) → ℝ)
    (t₁ t₂ : ℝ) : ℝ :=
  sInf {y | ∃ T, FairGuarantees.DivideChoose.IsShare Ω T ∧ (θ T).toReal = t₁ ∧
    y = sSup {x | ∃ S, FairGuarantees.DivideChoose.IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = t₂ - t₁ ∧ x = u S}}

/-- §5.2, p. 18: `τ ∈ Υ(n)`, a sequence `t⁰ = 0 ≤ t¹ ≤ ⋯ ≤ tⁿ⁻¹ ≤ 1 = tⁿ`. -/
def IsUpsilon (n : ℕ) (τ : Fin (n + 1) → ℝ) : Prop :=
  τ 0 = 0 ∧ τ (Fin.last n) = 1 ∧ Monotone τ

/-- §5.2, p. 19, display (6): `Γ^α(u; n) = max_{τ ∈ Υ(n)} min_{0 ≤ k ≤ n-1} u^α(t^k, t^{k+1})`,
with max read as sup. `Γ^κ` is `Gamma n (uKnife u K)` and `Γ^θ` is `Gamma n (uBid Ω θ u)`. -/
noncomputable def Gamma (n : ℕ) (v : ℝ → ℝ → ℝ) : ℝ :=
  sSup {y | ∃ τ : Fin (n + 1) → ℝ, IsUpsilon n τ ∧ y = ⨅ k : Fin n, v (τ k.castSucc) (τ k.succ)}

end FairGuarantees.BidChoose


