-- Prove2me | Definitions.Def_QMAPlusGap_thresholdOp
-- name    : QMAPlusGap_thresholdOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:00.289149+00:00
-- url     : https://prove2.me/theorems/0569a7ed-adee-43b4-8237-b42c84feb148
-- title:
--   Threshold acceptance operator $B$
-- statement:
--   Let $0\preceq A\preceq I$ be an acceptance operator on a proof space $\mathcal W=\mathbb C^{\kappa}$, let $L\in\mathbb N$ and $\theta\in\mathbb R$, and let $\mathcal H=\mathcal W^{\otimes L}$. Measuring $\{A,I-A\}$ on each of the $L$ registers and accepting iff at least $\lceil\theta L\rceil$ outcomes are $A$ has acceptance operator
--   $$
--   B=\sum_{S\subseteq[L],\ |S|\ge\lceil\theta L\rceil}\ \bigotimes_{i=1}^{L}C_i(S),\qquad C_i(S)=\begin{cases}A,&i\in S,\\ I-A,&i\notin S.\end{cases}
--   $$
--   It amplifies the one-proof verifier of Theorem 7 inside each register of the two-proof protocol.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), §3, p.14

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_kronFamily

set_option autoImplicit false

namespace QMAPlusGap

/-- The **threshold acceptance operator `B`** on `H = W^{⊗L}`, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), §3, p.14: "accept the H-register if at least
⌈θL⌉ runs accept. Let B be the accepting POVM element of this threshold test. Equivalently, measure {A, I − A} on
every W-register, and B = Σ_{S⊆[L], |S|≥⌈θL⌉} ⊗_{i=1}^{L} C_i(S), C_i(S) = A if i ∈ S, I − A if i ∉ S."

**Formalization Note** `W = ℂ^κ` and `H = W^{⊗L}` has basis `Fin L → κ`; `⌈θL⌉` is the integer ceiling. -/
noncomputable def thresholdOp {κ : Type} [DecidableEq κ] (A : Matrix κ κ ℂ) (L : ℕ) (θ : ℝ) :
    Matrix (Fin L → κ) (Fin L → κ) ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin L))).filter (fun S => ⌈θ * (L : ℝ)⌉ ≤ (S.card : ℤ)),
    OptimalSpectrum.Entangled.kronFamily (fun i : Fin L => if i ∈ S then A else 1 - A)

end QMAPlusGap


