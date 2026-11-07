-- Prove2me | Definitions.Def_RobustKellyTV_Setting
-- name    : RobustKellyTV_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:36.082386+00:00
-- url     : https://prove2.me/theorems/f4088eac-6c8f-4551-9bdc-e1bbf6a8e980
-- title:
--   Finite-alphabet TV-ball model: $P$, $\epsilon_0$, $D_{\mathrm{TV}}$, the null ball $\mathcal P_0$, $\Delta(S)$, $\ell$, $\eta_0$, $c_0$
-- statement:
--   The observation space is the finite alphabet $\mathcal X=\{1,\dots,d\}$. A **setting** consists of a nominal probability mass function $P=(P_1,\dots,P_d)$ and a robustness radius $\epsilon_0$ satisfying the standing assumptions of the paper:
--
--   $$d\ge 2,\qquad P_i>0\ \ (i=1,\dots,d),\qquad \sum_i P_i=1,\qquad 0<\epsilon_0<1-\min_i P_i .$$
--
--   Probability distributions on $\mathcal X$ are identified with their mass functions, i.e. points of the simplex $\Delta_d=\{R\in\mathbb R^d: R_i\ge 0,\ \sum_i R_i=1\}$. The **total variation distance** is $D_{\mathrm{TV}}(R,P)=\tfrac12\sum_{i=1}^d|R_i-P_i|$, and the **null class** is the total-variation ball
--
--   $$\mathcal P_0=B_{\mathrm{TV}}(P,\epsilon_0)=\{R\in\Delta_d: D_{\mathrm{TV}}(R,P)\le\epsilon_0\}.$$
--
--   The interior of the simplex is $\Delta_d^\circ=\{U\in\Delta_d: U_i>0\ \forall i\}$. For an alternative $S$ the **gap** is $\Delta(S)=D_{\mathrm{TV}}(S,P)-\epsilon_0$, positive exactly when $S\notin\mathcal P_0$, and $\ell(x)=\log\log(e^e/x)$ for $0<x\le 1$. Finally
--
--   $$\eta_0=\min_{A\subseteq\mathcal X:\ P(A)>\epsilon_0}\{P(A)-\epsilon_0\},\qquad c_0=\min\{\epsilon_0,\eta_0\},$$
--
--   where the minimum runs over the (nonempty: $A=\mathcal X$ qualifies) family of events with $P(A)>\epsilon_0$. Also $\min_i P_i$ and $\max_i P_i$ are recorded.
--
--   These are the objects in which every result of the mission is stated.
--
--   **Formalization Note** The alphabet is `Fin d`. The condition $\epsilon_0<1-\min_iP_i$ is written as "there is an $i$ with $\epsilon_0<1-P_i$", which is the same condition. Events are finsets of `Fin d`.
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §1 eq. (2) p.2, p.3 (D_TV); §2 standing assumptions p.6 (∆°_d); §3 p.11 (∆(S), ℓ); Lemma 3.1 p.11 (η0, c0); Lemma A.1 p.22 (max_i P_i)

import Mathlib

namespace RobustKellyTV

/-- The standing finite-alphabet total-variation model of
A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, §1 eq. (2), p.2, and the standing assumptions of
§2, p.6: "We assume throughout that d ≥ 2, Pᵢ > 0 for every i, and 0 < ϵ0 < 1 − minᵢ Pᵢ".

The observation space `X = {1, …, d}` is `Fin d`; `P` is the nominal probability mass function and
`ε₀` the robustness radius.

**Formalization Note.** The condition `ϵ0 < 1 − minᵢ Pᵢ` is written `∃ i, ε₀ < 1 − P i`, which is
the same condition (`1 − minᵢ Pᵢ = maxᵢ (1 − Pᵢ)`) and needs no choice of a nonempty index set. -/
structure Setting (d : ℕ) where
  /-- The nominal law `P = (P₁, …, P_d)`. -/
  P : Fin d → ℝ
  /-- The robustness radius `ϵ0`. -/
  ε₀ : ℝ
  two_le : 2 ≤ d
  P_pos : ∀ i, 0 < P i
  P_sum : ∑ i, P i = 1
  ε₀_pos : 0 < ε₀
  ε₀_lt : ∃ i, ε₀ < 1 - P i

variable {d : ℕ}

/-- Total variation distance `D_TV(R, P) = ½ Σᵢ |Rᵢ − Pᵢ|` between probability mass functions
(arXiv:2611.02130v1, p.3). -/
noncomputable def tv (R Q : Fin d → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |R i - Q i|

/-- The null class `P0 = B_TV(P, ϵ0) = {R ∈ ∆_d : D_TV(R, P) ≤ ϵ0}` (arXiv:2611.02130v1, eq. (2),
p.2). `∆_d` is Mathlib's `stdSimplex ℝ (Fin d)`: nonnegative vectors summing to one. -/
def nullBall (σ : Setting d) : Set (Fin d → ℝ) :=
  {R | R ∈ stdSimplex ℝ (Fin d) ∧ tv R σ.P ≤ σ.ε₀}

/-- The interior `∆°_d = {U ∈ ∆_d : Uᵢ > 0 for all i}` of the simplex (arXiv:2611.02130v1, p.6). -/
def interiorSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {U | U ∈ stdSimplex ℝ (Fin d) ∧ ∀ i, 0 < U i}

/-- The gap `∆(S) = D_TV(S, P) − ϵ0` (arXiv:2611.02130v1, §3, p.11). It is positive exactly when
`S ∉ P0` (for `S` in the simplex). -/
noncomputable def gap (σ : Setting d) (S : Fin d → ℝ) : ℝ :=
  tv S σ.P - σ.ε₀

/-- `ℓ(x) = log log(e^e / x)` for `0 < x ≤ 1` (arXiv:2611.02130v1, §3, p.11). On `(0, 1]` it is
at least `1`, so no junk value of `Real.log` is met there; it is only applied to such `x`. -/
noncomputable def ell (x : ℝ) : ℝ :=
  Real.log (Real.log (Real.exp (Real.exp 1) / x))

/-- `minᵢ Pᵢ`, the smallest nominal mass (arXiv:2611.02130v1, p.6). -/
noncomputable def Pmin (σ : Setting d) : ℝ :=
  Finset.univ.inf' ⟨⟨0, by have := σ.two_le; omega⟩, Finset.mem_univ _⟩ σ.P

/-- `maxᵢ Pᵢ`, the largest nominal mass (arXiv:2611.02130v1, Lemma A.1, p.22). -/
noncomputable def Pmax (σ : Setting d) : ℝ :=
  Finset.univ.sup' ⟨⟨0, by have := σ.two_le; omega⟩, Finset.mem_univ _⟩ σ.P

/-- The whole alphabet is an event `A` with `P(A) > ϵ0`, so the family in the definition of `η0`
is nonempty. -/
theorem univ_mem_bigEvents (σ : Setting d) :
    (Finset.univ : Finset (Fin d)) ∈
      (Finset.univ : Finset (Finset (Fin d))).filter (fun A => σ.ε₀ < ∑ i ∈ A, σ.P i) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [σ.P_sum]
  obtain ⟨i, hi⟩ := σ.ε₀_lt
  linarith [σ.P_pos i]

/-- `η0 = min_{A ⊆ X : P(A) > ϵ0} {P(A) − ϵ0}` (arXiv:2611.02130v1, Lemma 3.1, p.11). The minimum
runs over the finitely many events `A` (finsets of `Fin d`) with `P(A) > ϵ0`, a nonempty family. -/
noncomputable def eta0 (σ : Setting d) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin d))).filter (fun A => σ.ε₀ < ∑ i ∈ A, σ.P i)).inf'
    ⟨_, univ_mem_bigEvents σ⟩ (fun A => ∑ i ∈ A, σ.P i - σ.ε₀)

/-- `c0 = min{ϵ0, η0}` (arXiv:2611.02130v1, Lemma 3.1, p.11). -/
noncomputable def c0 (σ : Setting d) : ℝ :=
  min σ.ε₀ (eta0 σ)

end RobustKellyTV


