-- Prove2me | Definitions.Def_GMFGLearn_GMFV
-- name    : GMFGLearn_GMFV
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:13.323811+00:00
-- url     : https://prove2.me/theorems/bdb55d70-aac9-480a-a1a9-825a4f01f6d6
-- title:
--   GMF-V (Algorithm 2): the sample count $T_{\mathcal M}(\epsilon,\delta)$ (22), $\epsilon_k$, $K_{\epsilon,\eta}$, the $\epsilon$-net, $\mathrm{Proj}_{S_\epsilon}$, and the iterates $\mathcal L_k$
-- statement:
--   The objects of the learning algorithm GMF-V for finite $\mathcal S,\mathcal A$:
--
--   1. **Sample count (22).** $T_{\mathcal M}(\epsilon,\delta)=\sum_{i=1}^mC^{(i)}_{\mathcal M}(1/\epsilon)^{\alpha^{(i)}_1}(\log1/\epsilon)^{\alpha^{(i)}_2}(1/\delta)^{\alpha^{(i)}_3}(\log1/\delta)^{\alpha^{(i)}_4}$.
--   2. **Tolerances and iteration count.** $\epsilon_k=(k+1)^{-(1+\eta)}$ and
--   $$K_{\epsilon,\eta}=\Big\lceil2\max\big\{(\eta\epsilon/c)^{-1/\eta},\ \log_d\big(\epsilon/\max\{\operatorname{diam}(\mathcal S\times\mathcal A),c\}\big)+1\big\}\Big\rceil,\qquad d=d_1d_2+d_3 .$$
--   3. **$\epsilon$-net with action gap $\varphi(\epsilon)$.** A finite set $S_\epsilon\subseteq\mathcal P(\mathcal S\times\mathcal A)$ such that every $\mathcal L$ has some $\mathcal L^{(i)}\in S_\epsilon$ with $d_{TV}(\mathcal L,\mathcal L^{(i)})\le\epsilon$, and $\max_{a'}Q^\star_{\mathcal L^{(i)}}(s,a')-Q^\star_{\mathcal L^{(i)}}(s,a)\ge\varphi(\epsilon)$ for every $\mathcal L^{(i)}\in S_\epsilon$, $s$, and non-maximizing $a$.
--   4. **Projection.** $\mathrm{Proj}_{S_\epsilon}(\mathcal L)$ is a $d_{TV}$-nearest point of $S_\epsilon$ to $\mathcal L$.
--   5. **Iterates.** $\mathcal L_0$ is given; at step $k$ the learner returns $\hat Q_k$, the policy is $\pi_k(s)=f(\hat Q_k(s,\cdot))$, and $\mathcal L_{k+1}=\mathrm{Proj}_{S_\epsilon}(\Gamma_2(\pi_k,\mathcal L_k))$.
--
--   Theorem 2 bounds $W_1(\mathcal L_{K_{\epsilon,\eta}},\mathcal L^\star)$ for these iterates and sums $T$ over the $K_{\epsilon,\eta}$ steps.
--
--   **Formalization Note** Powers are real powers and $\log_d$ is `Real.logb d`; they are evaluated in the mission only where their bases are nonnegative and $d\in(0,1)$. $\operatorname{diam}(\mathcal S\times\mathcal A)$ replaces the printed $\operatorname{diam}(\mathcal S)\operatorname{diam}(\mathcal A)$ (see Theorem 2). The learner's outputs are random estimates $\hat Q_k(\omega)$ on a sample space; the simulator's output $\tilde{\mathcal L}_{k+1}$ is $\Gamma_2(\pi_k,\mathcal L_k)$, as in the proof of Theorem 2. The sup-norm error is $\max_{(s,a)}|\hat Q(s,a)-Q(s,a)|$.
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, Definition 2, (22), pp.12–13; §4.2 (ε-net), p.12; Algorithm 2 and Proj, p.13; Theorem 2, p.13; proof of Theorem 2, p.22

import Mathlib
import Definitions.Def_GMFGLearn_FiniteLayer

open MeasureTheory

namespace GMFGLearn

/-- **The sample count of a value-based guarantee (22).** Guo–Hu–Xu–Zhang, *A General Framework for
Learning Mean-Field Games*, arXiv:2003.06069v3, Definition 2, (22), pp.12–13:
`T_M(ϵ,δ) = Σ_{i=1}^m C^{(i)}_M (1/ϵ)^{α^{(i)}_1} (log 1/ϵ)^{α^{(i)}_2} (1/δ)^{α^{(i)}_3}
(log 1/δ)^{α^{(i)}_4}`.

**Formalization Note** Powers are `Real.rpow`; they are evaluated in the mission only at
`ϵ, δ ∈ (0,1]`, where every base is nonnegative. -/
noncomputable def sampleBound {m : ℕ} (C α₁ α₂ α₃ α₄ : Fin m → ℝ) (ε δ : ℝ) : ℝ :=
  ∑ i, C i * (1 / ε) ^ α₁ i * Real.log (1 / ε) ^ α₂ i * (1 / δ) ^ α₃ i * Real.log (1 / δ) ^ α₄ i

/-- **The tolerance `ϵ_k = (k + 1)^{−(1+η)}`** of Theorem 2, p.13. -/
noncomputable def epsK (η : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ (-(1 + η))

/-- **The number of outer iterations `K_{ϵ,η}`** of Theorem 2, p.13, with `diam(S × A)` in place of
the printed `diam(S)diam(A)`:
`K_{ϵ,η} := ⌈2 max{(ηϵ/c)^{−1/η}, log_d(ϵ / max{diam(S×A), c}) + 1}⌉`, where `d = d₁d₂ + d₃`.

**Formalization Note** `diam` is the argument `diam(S × A)` (the mission passes `diamSA S A`);
`log_d` is `Real.logb d`, used only at `d ∈ (0,1)`; the ceiling is `Nat.ceil`. -/
noncomputable def Kiter (ε η c d diam : ℝ) : ℕ :=
  ⌈2 * max ((η * ε / c) ^ (-1 / η)) (Real.logb d (ε / max diam c) + 1)⌉₊

/-- **The sup-norm error `‖Q − Q′‖_∞ = max_{(s,a)} |Q(s,a) − Q′(s,a)|`** ("understood element-wisely",
p.13). -/
noncomputable def supErr {S A : Type*} (Q Q' : S → A → ℝ) : ℝ :=
  ⨆ p : S × A, |Q p.1 p.2 - Q' p.1 p.2|

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype S] [Fintype A]
  [Nonempty A]

/-- **An `ϵ`-net with action gap `φ(ϵ)`.** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, §4.2, p.12: an
`ϵ`-net `S_ϵ := {L^{(1)},…,L^{(N_ϵ)}} ⊆ P(S × A)` with "min_{i=1,…,N_ϵ} d_TV(L,L^{(i)}) ≤ ϵ for any
L ∈ P(S × A)", and "max_{a′∈A} Q⋆_{L^{(i)}}(s,a′) − Q⋆_{L^{(i)}}(s,a) ≥ φ(ϵ) for any i = 1,…,N_ϵ,
s ∈ S, and any a ∉ argmax_{a∈A} Q⋆_{L^{(i)}}(s,a)".

**Formalization Note** The net is a `Finset`; `φ` is the value `φ(ϵ)`. A minimum over a finite set
is `≤ ϵ` iff some element is. -/
def IsEpsNet (M : GMFG S A) (net : Finset (ProbabilityMeasure (S × A))) (ε φ : ℝ) : Prop :=
  (∀ L : ProbabilityMeasure (S × A), ∃ L' ∈ net, dTV L L' ≤ ε) ∧
    ∀ L' ∈ net, ∀ (s : S) (a : A), a ∉ argmaxSet (M.optQL L' s) →
      φ ≤ xmax (M.optQL L' s) - M.optQL L' s a

/-- **The projection `Proj_{S_ϵ}`.** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, p.13:
`Proj_{S_ϵ}(L) = argmin_{L^{(1)},…,L^{(N_ϵ)}} d_TV(L^{(i)},L)`.

**Formalization Note** Any `d_TV`-nearest point of the net; ties are broken arbitrarily. -/
def IsProj (net : Finset (ProbabilityMeasure (S × A)))
    (proj : ProbabilityMeasure (S × A) → ProbabilityMeasure (S × A)) : Prop :=
  ∀ L, proj L ∈ net ∧ ∀ L' ∈ net, dTV (proj L) L ≤ dTV L' L

/-- **The GMF-V iterates `L_k` (Algorithm 2).** Guo–Hu–Xu–Zhang, arXiv:2003.06069v3, Algorithm 2,
p.13: from `L₀`, at step `k` take the approximate Q-function `Q̂⋆_k` of `M_{L_k}`, set
`π_k(s) = f_{c,c′}(Q̂⋆_k(s,·))`, obtain `L̃_{k+1}` from the simulator, and `L_{k+1} = Proj_{S_ϵ}(L̃_{k+1})`.

**Formalization Note** The learner's outputs are the random estimates `Qhat k ω` on a sample space
`Ω`. The simulator's population output is `L̃_{k+1} = Γ₂(π_k, L_k)`, as the proof of Theorem 2 uses
it ("W₁(L̃_{k+1},L⋆) = W₁(Γ₂(π_k,L_k),…)", p.22). -/
noncomputable def gmfvRun [MeasurableSingletonClass S] (M : GMFG S A)
    (f : (A → ℝ) → ProbabilityMeasure A)
    (proj : ProbabilityMeasure (S × A) → ProbabilityMeasure (S × A))
    (L₀ : ProbabilityMeasure (S × A)) {Ω : Type*} (Qhat : ℕ → Ω → S → A → ℝ) :
    ℕ → Ω → ProbabilityMeasure (S × A)
  | 0, _ => L₀
  | k + 1, ω => proj (M.Gamma2 (smoothPolicy f (Qhat k ω)) (gmfvRun M f proj L₀ Qhat k ω))

end GMFGLearn


