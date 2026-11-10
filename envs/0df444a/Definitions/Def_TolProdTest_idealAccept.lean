-- Prove2me | Definitions.Def_TolProdTest_idealAccept
-- name    : TolProdTest_idealAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:31.439011+00:00
-- url     : https://prove2.me/theorems/0b69006b-18dc-4ad8-b969-ed59168cf522
-- title:
--   Acceptance probability of the ideal Protocol 3.1
-- statement:
--   Protocol 3.1 runs the $k$-copy product test (Protocol 2.1) on $T$ independent groups of $k$ copies, with $X_j\in\{0,1\}$ the outcome of trial $j$, and accepts iff $T^{-1}\sum_jX_j\ge(p_Y+p_N)/2$. With exact local measurements its acceptance probability on $\rho$ is
--
--   $$
--   \mathrm{Tr}\Big[P\,\rho^{\otimes Tk}\Big],\qquad
--   P=\sum_{s\in\{0,1\}^T:\ \sum_js_j\ \ge\ T(p_Y+p_N)/2}\ \bigotimes_{j=1}^T\big(s_j\,?\,Q_k : I-Q_k\big),
--   $$
--
--   where trial $j$ acts on copies $jk,\dots,jk+k-1$ and $k,T,p_Y,p_N$ are the parameters (67)–(70).
--
--   This is the ideal protocol whose statistical error the proof of Theorem 3.8 bounds; the gate-level implementation is compared with it.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Protocol 3.1, p.17

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_TolProdTest_symProjOn
import Definitions.Def_TolProdTest_protoT
import Definitions.Def_ShadowTomography_UpperBound_tensorPow

set_option autoImplicit false

namespace TolProdTest

/-- Copy `l` of trial `j` is copy `j·k + l` of the `T·k` copies (`finProdFinEquiv (j, l) = l + k·j`). -/
def trialBlock {T k : ℕ} {X : Type} (x : Fin (T * k) → X) (j : Fin T) : Fin k → X :=
  fun l => x (finProdFinEquiv (j, l))

/-- The accepting operator of a threshold protocol on `T` independent trials of the `k`-copy product test:
`Σ_{s ∈ {0,1}^T, #{j : s_j = 1} ≥ thr} ⊗_j (s_j ? Q_k : I − Q_k)`, trial `j` acting on copies
`j·k, …, j·k + k − 1`. -/
noncomputable def thresholdOp (n d k T : ℕ) (thr : ℝ) :
    Matrix (Fin (T * k) → Config n d) (Fin (T * k) → Config n d) ℂ :=
  Matrix.of fun x y => ∑ s : Fin T → Bool,
    if thr ≤ ((Finset.univ.filter fun j => s j = true).card : ℝ) then
      ∏ j, (if s j then qk (Fin n) d k else 1 - qk (Fin n) d k) (trialBlock x j) (trialBlock y j)
    else 0

/-- **Acceptance probability of the ideal Protocol 3.1**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Protocol 3.1, p.17: "1. Set k, T, p_Y, and p_N
as above. 2. Run Protocol 2.1 on T independent groups of k copies, and let X_j ∈ {0, 1} indicate acceptance in
trial j. 3. Accept if T^{−1} Σ_{j=1}^T X_j ≥ (p_Y + p_N)/2; otherwise, reject."

The value is `Re Tr(P ρ^{⊗Tk})` with `P = thresholdOp n d k T (T (p_Y + p_N)/2)` and the parameters of (67)–(70):
the exact Born probability that the protocol accepts when every local measurement `{Q_{k,i}, I − Q_{k,i}}` is
performed perfectly (a trial accepts iff all its local outcomes are symmetric, i.e. on `Q_k`).

**Formalization Note** The `T·k` copies are grouped as in `trialBlock`; the mean condition
`T^{−1} Σ X_j ≥ (p_Y + p_N)/2` is the count condition `Σ X_j ≥ T(p_Y + p_N)/2`. -/
noncomputable def idealAccept (n d : ℕ) (a b δ : ℝ) (ρ : Matrix (Config n d) (Config n d) ℂ) : ℝ :=
  (thresholdOp n d (protoK a b) (protoT a b δ)
      ((protoT a b δ : ℝ) * (protoPY a b + protoPN a b) / 2) *
    ShadowTomography.UpperBound.tensorPow ρ (protoT a b δ * protoK a b)).trace.re

end TolProdTest


