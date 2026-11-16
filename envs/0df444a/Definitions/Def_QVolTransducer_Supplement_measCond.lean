-- Prove2me | Definitions.Def_QVolTransducer_Supplement_measCond
-- name    : QVolTransducer_Supplement_measCond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:33:21.721799+00:00
-- url     : https://prove2.me/theorems/7a6b109e-314f-4ca8-bcdb-741492090062
-- title:
--   Markov kernels on measurable spaces: irreducibility, reversibility, conductance, induced discretization
-- statement:
--   Let $(\Omega,\Sigma)$ be a measurable space and $P$ a Markov kernel, with iterates $P^0(x,A)=\delta_x(A)$, $P^t(x,A)=\int_\Omega P(x,dy)P^{t-1}(y,A)$.
--
--   1. $P$ is **$\mu$-irreducible** ($\mu\ne0$) if for every $x\in\Omega$ and $A\in\Sigma$ with $\mu(A)>0$ there is $t\in\mathbb N=\{1,2,\dots\}$ with $P^t(x,A)>0$.
--   2. $P$ is **reversible** with respect to a probability measure $\pi$ if $\int_AP(x,B)\,d\pi(x)=\int_BP(x,A)\,d\pi(x)$ for all $A,B\in\Sigma$; $\pi$ is **stationary** if $\int_\Omega P(x,A)\,d\pi(x)=\pi(A)$.
--   3. The **conductance** is
--   $$\varphi(P)=\inf_{A\in\Sigma,\ 0<\pi(A)<1}\frac{\int_AP(x,\Omega\setminus A)\,d\pi(x)}{\min\{\pi(A),\pi(\Omega\setminus A)\}},$$
--   and for a finite chain $\varphi(P)=\min_{S}\frac{\sum_{x\in S,y\notin S}\pi(x)P(x,y)}{\min\{\pi(S),\pi(\Omega\setminus S)\}}$.
--   4. For a measurable partition $\Omega=\Omega_1\sqcup\dots\sqcup\Omega_n$, the **induced discretization** lives on $\Omega'=\{j:\pi(\Omega_j)>0\}$ with $P'_{ij}=\frac1{\pi(\Omega_i)}\int_{\Omega_i}P(x,\Omega_j)\,d\pi(x)$ and $\pi'_i=\pi(\Omega_i)$.
--
--   These notions transfer conductance bounds between continuous walks and their discretizations (Theorems 6.8 and 6.10).
--
--   **Formalization Note** Conductances take values in $[0,\infty]$ and equal $+\infty$ when no set $A$ (resp. $S$) has $0<\pi(A)<1$; this is the infimum over an empty family, not Lean's real $\operatorname{sInf}\emptyset=0$. Integrals are lower Lebesgue integrals. The finite minimum is over the sets with $0<\pi(S)<1$, the only ones with a nonzero denominator. Reversibility and conductance are stated for any map from states to measures, so that explicitly defined walks can use them.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definitions 6.1, 6.2, 6.4, 6.6, 6.7, pp.39–40 (PDF pp.41–42); Definition 2.24, p.16 (PDF p.18)

import Mathlib

namespace QVolTransducer.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The iterated kernel `P^t` (Cornelissen, Apers, Gribling, *Improved quantum volume estimation
with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3, 2026,
sha256 40d7b52d…), Definition 6.1, p.39): `P^0(x, A) = δ_x(A)` and
`P^t(x, A) = ∫_Ω P(x, dy) P^{t−1}(y, A)`. -/
noncomputable def kpow {Ω : Type*} [MeasurableSpace Ω] (P : Kernel Ω Ω) : ℕ → Kernel Ω Ω
  | 0 => Kernel.id
  | t + 1 => Kernel.comp (kpow P t) P

/-- `µ`-irreducibility of a Markov kernel (arXiv:2609.40217, Definition 6.2, p.39): `µ ≠ 0`, and
for every `x ∈ Ω` and `A ∈ Σ` with `µ(A) > 0` there is `t ∈ ℕ = {1, 2, …}` with `P^t(x, A) > 0`. -/
def IsIrreducibleWrt {Ω : Type*} [MeasurableSpace Ω] (P : Kernel Ω Ω) (μ : Measure Ω) : Prop :=
  μ ≠ 0 ∧ ∀ (x : Ω) (A : Set Ω), MeasurableSet A → 0 < μ A → ∃ t : ℕ, 1 ≤ t ∧ 0 < kpow P t x A

/-- Reversibility of a transition law `P` with respect to a measure `π` (arXiv:2609.40217,
Definition 6.4, p.40): `∫_A P(x, B) dπ(x) = ∫_B P(x, A) dπ(x)` for all `A, B ∈ Σ`.

**Formalization Note** `P` is a map from states to measures; for a Markov kernel it is the
kernel's evaluation. The integrals are lower Lebesgue integrals in `ℝ≥0∞`. -/
def IsReversibleWrt {Ω : Type*} [MeasurableSpace Ω] (P : Ω → Measure Ω) (π : Measure Ω) : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    ∫⁻ x in A, P x B ∂π = ∫⁻ x in B, P x A ∂π

/-- Stationarity `πP = π` (arXiv:2609.40217, Definition 6.1, p.39: `(qP)(A) = ∫_Ω P(x, A) dq(x)`). -/
def IsStationaryWrt {Ω : Type*} [MeasurableSpace Ω] (P : Ω → Measure Ω) (π : Measure Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → ∫⁻ x, P x A ∂π = π A

/-- The conductance of a Markov kernel on a measurable space (arXiv:2609.40217, Definition 6.6,
p.40): `φ(P) = inf_{A ∈ Σ, 0 < π(A) < 1} ∫_A P(x, Ω∖A) dπ(x) / min{π(A), π(Ω∖A)}`.

**Formalization Note** The value is in `[0, ∞]`; the infimum of the empty family (no `A` with
`0 < π(A) < 1`, e.g. `π` a point mass) is `+∞`. The formula is applied to any transition law and
any measure; the paper defines it for `µ`-irreducible kernels reversible w.r.t. `π`. -/
noncomputable def measCond {Ω : Type*} [MeasurableSpace Ω] (P : Ω → Measure Ω) (π : Measure Ω) :
    ℝ≥0∞ :=
  ⨅ (A : Set Ω) (_ : MeasurableSet A ∧ 0 < π A ∧ π A < 1),
    (∫⁻ x in A, P x Aᶜ ∂π) / min (π A) (π Aᶜ)

/-- The conductance of a finite Markov chain (arXiv:2609.40217, Definition 2.24, p.16):
`φ(P) := min_{S ⊆ Ω} Σ_{(x,y) ∈ S × (Ω∖S)} π(x)P(x, y) / min{π(S), π(Ω∖S)}`.

**Formalization Note** The minimum is over the sets `S` with `0 < π(S) < 1` (for the other sets
the denominator vanishes); the value is in `[0, ∞]`, `+∞` when there is no such `S`. -/
noncomputable def finCond {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (π : S → ℝ) : ℝ≥0∞ :=
  ⨅ (A : Finset S) (_ : 0 < ∑ x ∈ A, π x ∧ ∑ x ∈ A, π x < 1),
    ENNReal.ofReal (∑ x ∈ A, ∑ y ∈ Aᶜ, π x * P x y) /
      ENNReal.ofReal (min (∑ x ∈ A, π x) (∑ x ∈ Aᶜ, π x))

/-- The state space `Ω′ = {j ∈ [n] : π(Ω_j) > 0}` of the induced discretization
(arXiv:2609.40217, Definition 6.7, p.40). -/
abbrev InducedIdx {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (π : Measure Ω)
    (parts : Fin n → Set Ω) : Type :=
  {j : Fin n // 0 < π (parts j)}

/-- The induced discretization `P′_{ij} := (1/π(Ω_i)) ∫_{Ω_i} P(x, Ω_j) dπ(x)` on
`Ω′ = {j : π(Ω_j) > 0}` (arXiv:2609.40217, Definition 6.7, p.40). -/
noncomputable def inducedP {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Kernel Ω Ω)
    (π : Measure Ω) (parts : Fin n → Set Ω) :
    Matrix (InducedIdx π parts) (InducedIdx π parts) ℝ :=
  fun i j => (∫⁻ x in parts i.1, P x (parts j.1) ∂π).toReal / (π (parts i.1)).toReal

/-- The induced distribution `π′_i = π(Ω_i)` on `Ω′` (arXiv:2609.40217, Theorem 6.8, p.41). -/
noncomputable def inducedStat {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (π : Measure Ω)
    (parts : Fin n → Set Ω) (i : InducedIdx π parts) : ℝ :=
  (π (parts i.1)).toReal

end QVolTransducer.Supplement


