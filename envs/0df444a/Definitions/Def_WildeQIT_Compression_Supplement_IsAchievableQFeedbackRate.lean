-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_IsAchievableQFeedbackRate
-- name    : WildeQIT_Compression_Supplement_IsAchievableQFeedbackRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:03:55.324883+00:00
-- url     : https://prove2.me/theorems/668c3949-22c9-4cbb-9768-fd0e178a586d
-- title:
--   Rate achievable with quantum feedback
-- statement:
--   A rate $C$ is **achievable for $\mathcal N$ with quantum feedback** if for all $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$ there is a protocol for classical communication with quantum feedback (Figure 21.4) over $n$ uses of $\mathcal N$ with $|\mathcal M|\ge 2^{n(C-\delta)}$ messages and error $\Pr\{M'\neq M\}\le\varepsilon$ for a uniformly distributed message.
--
--   The quantum feedback capacity is the supremum of these rates; Theorem 21.5.2 shows that it equals the entanglement-assisted classical capacity.
--
--   **Formalization Note** The form is that of the published entanglement-assisted achievable rate `WildeQIT.EADamping.IsAchievableEARate` (§21.1), with its code replaced by the feedback protocol and the maximal error by the error $\Pr\{M'\neq M\}$ with uniform $M$ that the book uses for feedback codes. Logarithms are base 2.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 21.5.2 and its proof, pp. 605–606; §21.1, p. 590

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_QFeedbackCode_errorProb

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 21.5.2, p. 605, and
its proof, pp. 605–606 (rates achievable with a quantum feedback channel); §21.1, p. 590, for the
form of an achievable rate.
-/

namespace WildeQIT.Compression.Supplement

/-- **Rate achievable for `N` with quantum feedback** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, Theorem 21.5.2, p. 605, and pp. 605–606): `C` is achievable if for all
`ε ∈ (0, 1)`, `δ > 0` and all sufficiently large `n` there is a protocol for classical
communication with quantum feedback (Figure 21.4) over `n` channel uses, with rate
`(1/n) log |M| ≥ C − δ` and error `Pr{M′ ≠ M} ≤ ε` for a uniformly distributed message.

**Formalization Note.** The form of the definition is that of the published
`WildeQIT.EADamping.IsAchievableEARate` (§21.1, p. 590), with the entanglement-assisted code
replaced by the quantum-feedback protocol `QFeedbackCode` and the maximal error replaced by the
error `Pr{M′ ≠ M}` with uniform `M` that the book uses for feedback codes (p. 606, (21.115)).
"Rate `C − δ`" is `|M| ≥ 2^{n(C−δ)}`; logarithms are base 2. -/
def IsAchievableQFeedbackRate {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ k : ℕ, (2 : ℝ) ^ ((n : ℝ) * (C - δ)) ≤ k ∧
      ∃ c : QFeedbackCode a b n k, c.errorProb N ≤ ε

end WildeQIT.Compression.Supplement


