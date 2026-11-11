-- Prove2me | Definitions.Def_QNoiseStab_successProb
-- name    : QNoiseStab_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:40.11818+00:00
-- url     : https://prove2.me/theorems/d65e8585-5813-42ff-a707-a3aabbc49752
-- title:
--   Success probability of a $T$-query algorithm for a relation $R$ on a uniform input
-- statement:
--   Let $X$ be a finite set with a bijection $\mathrm{enc}:X\to\mathbb Z_d$, let $\hat Y$ be any set, and let $R\subseteq X^n\times\hat Y$ be a relation. Let $\mathcal A$ be a $T$-query algorithm with query register $[n]$, phase register $\mathbb Z_d$ and a finite workspace $W$, querying the phase oracle $O_{\mathrm{enc}(x)}$ with root $\omega$; let $|\psi_T^x\rangle$ be its final state on input $x$, and let $\mathrm{out}$ map each computational-basis outcome of the registers $QPW$ to an answer in $\hat Y$. The **success probability** of $\mathcal A$ for $R$ on a uniformly random input is
--
--   $$
--   \mathrm{succ}_R(\mathcal A)=\frac1{|X|^{n}}\sum_{x\in X^n}\ \sum_{z:\ (x,\mathrm{out}(z))\in R}\bigl|\langle z|\psi_T^x\rangle\bigr|^2 .
--   $$
--
--   For the purified uniform input $|U\rangle=|X|^{-n/2}\sum_x|x\rangle$ this equals the paper's $\|\Pi^R_{\mathrm{succ}}|\psi_T\rangle\|^2$. It is the quantity bounded by the Quantum Noise Stability Bound.
--
--   **Formalization Note** The algorithm is the published `QAlgorithms.QueryAlg`, whose start state is an arbitrary input-independent unit vector. The output map reads the measured $QPW$ registers; the paper's post-processing $q(w)$ of the measured workspace is the case $\mathrm{out}=q\circ\mathrm{pr}_W$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.1, pp.6–7 (success probability ‖Π_succ|ψ_T⟩‖²); proof of Theorem 3.5, p.13 (Π^R_succ)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QNoiseStab_phaseQuery

namespace QNoiseStab

open Classical in
/-- The success probability of a `T`-query algorithm for a relation `R ⊆ Xⁿ × Ŷ` on a uniformly
random input (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.1, pp.6–7, and the proof of Theorem 3.5, p.13: "The probability that the
algorithm produces a correct answer for R is given by ‖Π^R_succ |ψ_T⟩‖²"). The input alphabet
`X` is identified with `ZMod d` by the bijection `enc` (p.6: "a bijective map v between X and
[d]"); on input `x` the algorithm `A` queries the phase oracle `phaseQuery ω (enc ∘ x)`, its
whole register `QPW` is measured in the computational basis, and it outputs `out` of the
outcome. The value is
`|X|^{-n} Σ_x Pr[(x, out(outcome)) ∈ R]`.

**Formalization Note** For the purified uniform input `|D⟩ = |X|^{-n/2} Σ_x |x⟩` (p.6) the paper's
`‖Π^R_succ |ψ_T⟩‖²` is exactly this average. The output map reads the measured `QPW` registers;
the paper's `q(w)` of the measured workspace is the special case `out = q ∘ Prod.snd`. -/
noncomputable def successProb {X Ŷ W : Type} [Fintype X] [Fintype W] [DecidableEq W]
    {n d T : ℕ} [NeZero d] (enc : X ≃ ZMod d) (ω : ℂ)
    (A : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (out : (Fin n × ZMod d) × W → Ŷ)
    (R : Set ((Fin n → X) × Ŷ)) : ℝ :=
  ((Fintype.card X : ℝ) ^ n)⁻¹ *
    ∑ x : Fin n → X,
      QAlgorithms.probEvent (A.finalState (phaseQuery ω (fun i => enc (x i))))
        (fun z => (x, out z) ∈ R)

end QNoiseStab


