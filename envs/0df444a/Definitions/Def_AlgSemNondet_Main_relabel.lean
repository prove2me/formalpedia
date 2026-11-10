-- Prove2me | Definitions.Def_AlgSemNondet_Main_relabel
-- name    : AlgSemNondet_Main_relabel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:46:16.933845+00:00
-- url     : https://prove2.me/theorems/0dbd1bda-6c6e-45e4-abdf-bc873af4bfa8
-- title:
--   Lemma 4.1 (construction) — the relabelled machine $M_\pi$ and relabelled configurations $\pi(C)$
-- statement:
--   For a permutation $\pi$ of the tape alphabet $\Gamma$, the relabelled machine $M_\pi = (Q, \Sigma, \Gamma, \delta_\pi, q_0, q_{\mathrm{accept}}, q_{\mathrm{reject}})$ has the same states, input alphabet, blank and distinguished states as $M$, and
--   $$\delta_\pi(q, \pi(c)) = (q', \pi(c'), D) \iff \delta(q, c) = (q', c', D),$$
--   that is, $\delta_\pi(q, x)$ is $\delta(q, \pi^{-1}(x))$ with the written symbol replaced by its $\pi$-image, and undefined exactly where $\delta(q, \pi^{-1}(x))$ is undefined. For a configuration $C$, $\pi(C)$ replaces every tape symbol $c$ by $\pi(c)$ and keeps the state and the head position.
--
--   Formalization Note: the construction is defined for every permutation; the source uses it only for permutations with $\pi(B) = B$ (Definition 4.2, Corollary 4.3) and additionally $\pi(\Sigma) = \Sigma$ (Lemma 4.1), and those conditions are hypotheses of the theorems that use it.
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Lemma 4.1 (construction of M_π and π(C)), pp.14-15, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib
import Definitions.Def_AlgSemNondet_Main_TuringMachine

namespace AlgSemNondet.Main

/-- `π(C)`: replace every tape symbol `c` of the configuration `C` by `π(c)`, keeping the state
and the head position (Lemma 4.1). -/
def Config.relabel {Q Γ : Type*} (π : Equiv.Perm Γ) (C : Config Q Γ) : Config Q Γ where
  state := C.state
  tape := fun i => π (C.tape i)
  head := C.head

/-- The relabelled machine `M_π = (Q, Σ, Γ, δ_π, q₀, q_accept, q_reject)` of Lemma 4.1:
`δ_π(q, π(c)) = (q', π(c'), D)` iff `δ(q, c) = (q', c', D)`, i.e. `δ_π(q, x)` is `δ(q, π⁻¹ x)`
with the written symbol mapped by `π`, and undefined exactly where `δ(q, π⁻¹ x)` is. The input
alphabet `Σ`, the blank and the three distinguished states are unchanged. -/
def TuringMachine.relabel {Q Γ : Type*} [Fintype Q] [Fintype Γ] {B : Γ}
    (M : TuringMachine Q Γ B) (π : Equiv.Perm Γ) : TuringMachine Q Γ B where
  inputAlphabet := M.inputAlphabet
  blank_not_mem := M.blank_not_mem
  δ := fun q x => (M.δ q (π.symm x)).map fun t => (t.1, π t.2.1, t.2.2)
  q₀ := M.q₀
  qaccept := M.qaccept
  qreject := M.qreject

end AlgSemNondet.Main


