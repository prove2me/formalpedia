-- Prove2me | Definitions.Def_FairGuarantees_DivideChoose_Setting
-- name    : FairGuarantees_DivideChoose_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:58.478974+00:00
-- url     : https://prove2.me/theorems/53b803c5-19fe-4299-ad4f-772e4fa262db
-- title:
--   §3.1–3.3, pp. 8–11 — manna, shares, n-partitions, δ-continuous utilities D(Ω), equipartitions, minMax and Maxmin
-- statement:
--   The non-atomic fair division model of §3.1–§3.3.
--
--   1. **Manna.** The manna $\Omega$ is a bounded Lebesgue-measurable subset of $\mathbb R^d$ with $|\Omega|>0$, where $|\cdot|$ is Lebesgue measure.
--   2. **Shares.** A share is a (possibly empty) measurable subset $S\subseteq\Omega$; $\mathcal B$ is the set of shares.
--   3. **Pseudo-metric.** For shares $S,T$, $\delta(S,T)=|S\otimes T|$, the measure of the symmetric difference.
--   4. **Utilities.** The domain $\mathcal D(\Omega)$ consists of the maps $u:\mathcal B\to\mathbb R$ with $u(\emptyset)=0$ that are bounded and continuous for $\delta$. Utilities need not be monotone, additive or of constant sign. The monotone subdomains are $\mathcal M^+(\Omega)$ ($S\subseteq T\Rightarrow u(S)\le u(T)$) and $\mathcal M^-(\Omega)$ ($S\subseteq T\Rightarrow u(S)\ge u(T)$).
--   5. **Partitions.** For a share $S$, an $n$-partition $\Pi=(S_i)_{i=1}^n\in\mathcal P_n(S)$ is an $n$-tuple of shares with $\bigcup_i S_i=S$ and $|S_i\cap S_j|=0$ for $i\neq j$.
--   6. **Equipartitions** (Definition 1). $\Pi\in\mathcal{EP}_n(S;u)$ when $\Pi\in\mathcal P_n(S)$ and $u(S_i)=u(S_j)$ for all $i,j$.
--   7. **Benchmarks** (Definition 2).
--   $$\mathrm{minMax}(u;n)=\inf_{\Pi\in\mathcal P_n(\Omega)}\ \max_{1\le i\le n}u(S_i),\qquad \mathrm{Maxmin}(u;n)=\sup_{\Pi\in\mathcal P_n(\Omega)}\ \min_{1\le i\le n}u(S_i).$$
--
--   These objects are shared by every statement of the mission: minMax is the level the Divide & Choose rule guarantees, and equipartitions are what a Divider proposes.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin d)` with `volume`. A utility is a function on all subsets, but every condition is imposed on shares only, so values off shares never matter. Partitions are indexed by `Fin n`; parts may overlap on null sets and their union is exactly $S$. The paper writes min/max in Definition 2 and explains on p. 9 that they are an infimum and a supremum; they are `sInf`/`sSup` of real sets, which are the true inf/sup when $n\ge1$ (the set of partitions is nonempty, since $(\Omega,\emptyset,\dots,\emptyset)$ is one, and $u$ is bounded). Every theorem using them assumes $n\ge1$; for $n=0$ both definitions return $0$.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 8, §3.1; p. 9, §3.2 Definition 1; p. 11, §3.3 Definition 2

import Mathlib

namespace FairGuarantees.DivideChoose

open MeasureTheory

/-- The ambient Euclidean space `ℝ^d`, with Lebesgue measure `volume`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- §3.1, p. 8: the manna `Ω` is a bounded measurable set of positive Lebesgue measure. -/
def IsManna (Ω : Set (E d)) : Prop :=
  MeasurableSet Ω ∧ Bornology.IsBounded Ω ∧ 0 < volume Ω

/-- §3.1, p. 8: a share is a (possibly empty) measurable subset of `Ω`. -/
def IsShare (Ω S : Set (E d)) : Prop :=
  MeasurableSet S ∧ S ⊆ Ω

/-- §3.1, p. 8: the pseudo-metric `δ(S, T) = |S ⊗ T|` (Lebesgue measure of the symmetric
difference). It is finite on shares because `Ω` is bounded. -/
noncomputable def δ (S T : Set (E d)) : ℝ :=
  (volume (symmDiff S T)).toReal

/-- §3.1, p. 8: the domain `D(Ω)`. A utility is a map from shares to `ℝ` with `u(∅) = 0`,
bounded on shares and continuous for the pseudo-metric `δ` on shares. Values of `u` on sets
that are not shares are irrelevant. -/
def IsUtility (Ω : Set (E d)) (u : Set (E d) → ℝ) : Prop :=
  u ∅ = 0 ∧ (∃ C : ℝ, ∀ S, IsShare Ω S → |u S| ≤ C) ∧
    ∀ S, IsShare Ω S → ∀ ε > 0, ∃ η > 0, ∀ T, IsShare Ω T → δ S T < η → |u T - u S| < ε

/-- §3.1, p. 8: `M⁺(Ω)`, monotone increasing utilities (on shares). -/
def IsIncreasing (Ω : Set (E d)) (u : Set (E d) → ℝ) : Prop :=
  ∀ S T, IsShare Ω S → IsShare Ω T → S ⊆ T → u S ≤ u T

/-- §3.1, p. 8: `M⁻(Ω)`, monotone decreasing utilities (on shares). -/
def IsDecreasing (Ω : Set (E d)) (u : Set (E d) → ℝ) : Prop :=
  ∀ S T, IsShare Ω S → IsShare Ω T → S ⊆ T → u T ≤ u S

/-- §3.1, p. 8: `P ∈ P_n(S)`, an `n`-partition of the share `S`: `n` shares contained in `S`
whose union is exactly `S` and whose pairwise intersections are Lebesgue-null. -/
def IsPartition (Ω S : Set (E d)) (n : ℕ) (P : Fin n → Set (E d)) : Prop :=
  (∀ i, IsShare Ω (P i) ∧ P i ⊆ S) ∧ (⋃ i, P i) = S ∧
    ∀ i j, i ≠ j → volume (P i ∩ P j) = 0

/-- Definition 1, p. 9: `P ∈ EP_n(S; u)`, an `n`-equipartition of `S` for `u`: an
`n`-partition of `S` all of whose parts have the same utility. -/
def IsEquipartition (Ω : Set (E d)) (u : Set (E d) → ℝ) (S : Set (E d)) (n : ℕ)
    (P : Fin n → Set (E d)) : Prop :=
  IsPartition Ω S n P ∧ ∀ i j, u (P i) = u (P j)

/-- Definition 2, p. 11: `minMax(u; n)`, the infimum over `n`-partitions of `Ω` of the
utility of the best part (p. 9: the "min" is an infimum). -/
noncomputable def minMax (Ω : Set (E d)) (u : Set (E d) → ℝ) (n : ℕ) : ℝ :=
  sInf {x | ∃ P : Fin n → Set (E d), IsPartition Ω Ω n P ∧ x = ⨆ i, u (P i)}

/-- Definition 2, p. 11: `Maxmin(u; n)`, the supremum over `n`-partitions of `Ω` of the
utility of the worst part (p. 9: the "max" is a supremum). -/
noncomputable def Maxmin (Ω : Set (E d)) (u : Set (E d) → ℝ) (n : ℕ) : ℝ :=
  sSup {x | ∃ P : Fin n → Set (E d), IsPartition Ω Ω n P ∧ x = ⨅ i, u (P i)}

end FairGuarantees.DivideChoose


