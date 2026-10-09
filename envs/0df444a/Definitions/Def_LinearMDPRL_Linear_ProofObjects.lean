-- Prove2me | Definitions.Def_LinearMDPRL_Linear_ProofObjects
-- name    : LinearMDPRL_Linear_ProofObjects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:22.816847+00:00
-- url     : https://prove2.me/theorems/4d3a2149-d508-4616-8d85-296aae811433
-- title:
--   Lemma D.6 (p. 28) function class 𝒱 and Lemma B.3 (p. 17) good event 𝔈
-- statement:
--   This file defines two objects used in the proof of Theorem 3.1.
--
--   1. **The value class of Lemma D.6** (p. 28). Given $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ and numbers $H$, $L$, $B$, $\lambda$, the class $\mathcal V$ consists of all functions
--   $$
--   V(x)=\min\Big\{\max_a\Big[w^\top\phi(x,a)+\beta\sqrt{\phi(x,a)^\top\Lambda^{-1}\phi(x,a)}\Big],\ H\Big\}
--   $$
--   with $\|w\|\le L$, $\beta\in[0,B]$ and $\Lambda$ a symmetric $d\times d$ matrix with minimum eigenvalue at least $\lambda$ (that is, $v^\top\Lambda v\ge\lambda\|v\|^2$ for all $v$). The value estimates $V^k_h$ of LSVI-UCB have this form.
--
--   2. **The good event $\mathfrak E$ of Lemma B.3** (p. 17), as a property of the observed data of LSVI-UCB run with $\lambda=1$ and $\beta=c_\beta\cdot dH\sqrt\iota$, $\iota=\log(2dT/p)$, $T=KH$: for all $(k,h)\in[K]\times[H]$,
--   $$
--   \Big\|\sum_{\tau=1}^{k-1}\phi^\tau_h\big[V^k_{h+1}(x^\tau_{h+1})-\mathbb P_hV^k_{h+1}(x^\tau_h,a^\tau_h)\big]\Big\|_{(\Lambda^k_h)^{-1}}\le C\cdot dH\sqrt\chi,\qquad \chi=\log\big[2(c_\beta+1)dT/p\big],
--   $$
--   where $\|v\|_{M}=\sqrt{v^\top Mv}$ and $\mathbb P_hV(x,a)=\int V\,d\mathbb P_h(\cdot\mid x,a)$.
--
--   The event $\mathfrak E$ is the high-probability event on which the deterministic part of the regret analysis (Lemmas B.4–B.6) runs.
--
--   **Formalization Note.** $\mathfrak E$ is stated for one fixed data sequence; the random event of Lemma B.3 is obtained by evaluating it along a run.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma D.6, p. 28 (class 𝒱); Lemma B.3, p. 17 (event 𝔈)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory Matrix

/-- The function class `𝒱` of Lemma D.6 (p. 28): all functions `S → ℝ` of the form
`V(x) = min{ max_a [w^⊤ φ(x, a) + β √(φ(x, a)^⊤ Λ^{-1} φ(x, a))], H }`
whose parameters satisfy `‖w‖ ≤ L`, `β ∈ [0, B]`, and `Λ` is a symmetric `d × d` matrix whose
minimum eigenvalue is at least `λ`, i.e. `v^⊤ Λ v ≥ λ ‖v‖²` for every `v`. -/
def valueClass {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (H L B lam : ℝ) : Set (S → ℝ) :=
  {V | ∃ (w : EuclideanSpace ℝ (Fin d)) (β : ℝ) (Λ : Matrix (Fin d) (Fin d) ℝ),
      ‖w‖ ≤ L ∧ β ∈ Set.Icc 0 B ∧ Λ.IsHermitian ∧
      (∀ v : Fin d → ℝ, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Λ *ᵥ v)) ∧
      V = fun x => min (Finset.univ.sup' Finset.univ_nonempty (fun a =>
            inner ℝ w (φ x a) +
              β * Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ (Λ⁻¹ *ᵥ WithLp.ofLp (φ x a))))) H}

/-- The good event `𝔈` of Lemma B.3 (p. 17), as a property of the observed data `xs`, `as` of
LSVI-UCB run with `λ = 1` and `β = c_β · dH√ι`, `ι = log(2dT/p)`, `T = KH`: for every
`(k, h) ∈ [K] × [H]`,
`‖Σ_{τ=1}^{k-1} φ^τ_h [V^k_{h+1}(x^τ_{h+1}) − (P_h V^k_{h+1})(x^τ_h, a^τ_h)]‖_{(Λ^k_h)^{-1}} ≤ C · dH√χ`,
with `χ = log[2(c_β + 1) dT / p]`, `φ^τ_h = φ(x^τ_h, a^τ_h)`, and
`(P_h V)(x, a) = ∫ V dP_h(· | x, a)`. -/
def goodEvent {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] [Nonempty A]
    {d : ℕ} (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (C cβ p : ℝ) (H K : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) : Prop :=
  let β : ℕ → ℝ := fun _ => cβ * d * H * Real.sqrt (iota d K H p)
  ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
    let s : Fin d → ℝ := ∑ τ ∈ Finset.Ico 1 k,
      (lsviV φ M.r 1 β H xs as k (h + 1) (xs τ (h + 1)) -
          ∫ y, lsviV φ M.r 1 β H xs as k (h + 1) y ∂(M.P h (xs τ h, as τ h))) •
        WithLp.ofLp (φ (xs τ h) (as τ h))
    Real.sqrt (s ⬝ᵥ ((gram φ 1 xs as k h)⁻¹ *ᵥ s))
      ≤ C * d * H * Real.sqrt (Real.log (2 * (cβ + 1) * d * ((K : ℝ) * H) / p))

end LinearMDPRL.Linear


