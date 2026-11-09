-- Prove2me | Definitions.Def_AgnosticTNS_Run_IsValid
-- name    : AgnosticTNS_Run_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:38.574133+00:00
-- url     : https://prove2.me/theorems/d9d90864-f6b1-4315-a31b-6c78a6f37848
-- title:
--   Admissible run of Algorithm 1
-- statement:
--   A run with residual sizes $p_i$ and eigenvector counts $\Lambda_i$ is **admissible** if:
--   1. (lines 5–6) when $|M_i|\le p_i$, $R_i=M_i$;
--   2. (lines 7–12) when $|M_i|>p_i$: $R_i\subseteq M_i$ with $|R_i|=p_i$; $\hat\sigma_i\ge0$; $\tilde U_i$ is unitary on $M_i$; and $\tilde U_iW_i\subseteq|0^{|Q_i|}\rangle_{Q_i}\otimes\mathcal H_{R_i}$ for a span $W_i$ of eigenvectors of $\hat\sigma_i$ for its $\Lambda_i$ largest eigenvalues, counted with multiplicity (any choice);
--   3. (lines 20–21) $\hat\tau\ge0$ and $|\hat\varphi\rangle$ is a normalised eigenvector of $\hat\tau$ for its largest eigenvalue.
--
--   **Formalization Note** Sub-Tomography also returns estimates of trace at most one; only positivity is required here, so the admissible runs include every run of the paper's algorithm.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1, p.19; p.20

import Mathlib
import Definitions.Def_AgnosticTNS_Run
import Definitions.Def_AgnosticTNS_IsTopSpan
open Matrix
open scoped ComplexOrder

namespace AgnosticTNS

/-- **Admissible choices of a run of Algorithm 1**, p.19 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)), for residual sizes `p_i` and
eigenvector counts `Λ_i`:
* lines 5–6: if `|M_i| ≤ p_i` then `R_i = M_i`;
* lines 7–12: if `|M_i| > p_i` then `R_i ⊆ M_i` with `|R_i| = p_i`, the estimate `σ̂_i` is positive
  semidefinite, `Ũ_i` is unitary on `M_i`, and `Ũ_i W_i ⊆ |0⟩_{Q_i} ⊗ H_{R_i}` (`Q_i = M_i ∖ R_i`) for
  a span `W_i` of eigenvectors of `σ̂_i` for its `Λ_i` largest eigenvalues, counted with multiplicity
  (any choice, `IsTopSpan`);
* lines 20–21: `τ̂` is positive semidefinite and `φ̂` is a normalised eigenvector of `τ̂` for its
  largest eigenvalue.

**Formalization Note** `Ũ W ⊆ |0⟩_Q ⊗ H_R` says that every image vector vanishes on the configurations
of `M_i` with a nonzero label on `Q_i`. The estimates are only required to be positive semidefinite
(Sub-Tomography also returns trace at most one), so the class of runs is at least as large as the
paper's. -/
def Run.IsValid {d n : ℕ} {Ls : LearningSequence n} (run : Run d n Ls) (p Λ : Fin Ls.L → ℕ) :
    Prop :=
  (∀ i, (Mset Ls run.R i).card ≤ p i → run.R i = Mset Ls run.R i) ∧
  (∀ i, p i < (Mset Ls run.R i).card →
    run.R i ⊆ Mset Ls run.R i ∧ (run.R i).card = p i ∧ (run.σhat i).PosSemidef ∧
    (run.U i)ᴴ * run.U i = 1 ∧
    ∃ W, IsTopSpan (run.σhat i) (Λ i) W ∧
      ∀ v ∈ W, ∀ y : ↥(Mset Ls run.R i) → Fin d,
        (∃ q : ↥(Mset Ls run.R i), q.1 ∉ run.R i ∧ (y q : ℕ) ≠ 0) → (run.U i *ᵥ v) y = 0) ∧
  run.τhat.PosSemidef ∧ ∑ x, ‖run.φhat x‖ ^ 2 = 1 ∧
  ∃ μ : ℝ, run.τhat *ᵥ run.φhat = (μ : ℂ) • run.φhat ∧
    ∀ x, (star x ⬝ᵥ (run.τhat *ᵥ x)).re ≤ μ * ∑ y, ‖x y‖ ^ 2

end AgnosticTNS


