-- Prove2me | Definitions.Def_BindingEntChannels_AdaptiveState
-- name    : BindingEntChannels_AdaptiveState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:41.404212+00:00
-- url     : https://prove2.me/theorems/1bf29d7c-9e50-468d-964b-5f252a234a4d
-- title:
--   Adaptive LQCC protocols using the channel $n$ times, with bipartite output
-- statement:
--   A **protocol** of Alice and Bob that uses the channel $\Lambda$ exactly $n$ times and ends with a bipartite state on $\mathbb C^c\otimes\mathbb C^d$ (Alice's register first) is built from the following steps, acting on the joint state of Alice's memory and Bob's memory:
--
--   1. **keep**: stop; the joint memory is the output;
--   2. **discard**: reject the current branch (post-selection, or filtering); it contributes nothing to the output;
--   3. **Alice's instrument** (resp. **Bob's**): apply a local Kraus instrument $\{E_i\}$, $\sum_i E_i^\dagger E_i=1$, to one's own memory, announce the outcome $i$, and continue with a protocol that may depend on $i$; the branches are summed;
--   4. **channel use**: send a register of Alice's memory through $\Lambda$; the output joins Bob's memory.
--
--   All branches of an instrument use the channel the same number of times. Applied to an initial state, a protocol yields an unnormalized output, the sum over accepted branches, whose trace is the success probability.
--
--   These are the "LQCC operations" with "(possibly multiply) use of the channel" of clause (ii) of the Definition.
--
--   **Formalization Note** Steps 3 and 4 are those of the platform's adaptive protocols defining $Q_2$. Step 2 reads "LQCC" as including filtering, as the paper does when it calls a non-trace-preserving $\Gamma\otimes I$ an LQCC action (p. 2) and filtering an LQCC action (p. 3). Local state preparation, ancillas and partial traces are instruments between memories of different dimensions.
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, Definition, pp. 1–2, and §I, p. 1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_RetroCorr_Separation_TwoWay

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
p. 1 ("Alice and Bob are allowed to support the quantum channel by using LQCC operations") and the
Definition, pp. 1–2 ("by means of (possibly multiply) use of the channel and LQCC operations"):
the protocols of Alice and Bob that use the channel `Λ` exactly `n` times, interleaved with local
quantum operations and adaptive two-way classical communication, and end with a bipartite state on
`Fin c × Fin d` (Alice's register first). The predicate holds of the (unnormalized) map from the
joint state of Alice's memory `Fin a` and Bob's memory `Fin b` to the final state.

* `keep`: the protocol ends; the joint memory is the output.
* `discard`: the branch is rejected (post-selection, "filtering"); it contributes nothing.
* `alice` / `bob`: a party applies a complete Kraus instrument (ancillas, local state preparation
  and discarding of subsystems are included through the dimensions); its outcome `i` is
  announced, the rest of the protocol may depend on it, and the branches are summed.
* `send`: a register of Alice's memory (chosen by the relabelling `e`) goes through `Λ` and its
  output joins Bob's memory (relabelling `f`); one more channel use.

**Formalization Note.** The `alice`, `bob` and `send` steps are those of the published
`RetroCorr.Separation.Adaptive` (which defines `Q₂`), with the published `aliceBranch`,
`bobBranch`, `sendVia`; the differences are that the output is the bipartite state instead of
Bob's decoded message, and `discard`, which reads "LQCC" as including filtering, as the paper does
for `Γ ⊗ I` with `Γ` not trace preserving (p. 2) and for filtering (p. 3). All branches of an
instrument use the channel the same number `n` of times; `discard` is available at every `n`. The
output of a protocol run on a state is the sum over accepted branches, whose trace is the success
probability. -/
inductive AdaptiveState {I O : Type*} [Fintype I] [Fintype O] (Λ : QAlgorithms.Superop I O)
    (c d : ℕ) : {n a b : ℕ} → QAlgorithms.Superop (Fin a × Fin b) (Fin c × Fin d) → Prop
  | keep : AdaptiveState Λ c d (n := 0) (a := c) (b := d) (fun X => X)
  | discard {n a b : ℕ} : AdaptiveState Λ c d (n := n) (a := a) (b := b) (fun _ => 0)
  | alice {n a b h r : ℕ} (E : Fin r → Matrix (Fin h) (Fin a) ℂ)
      (complete : QAlgorithms.IsKrausFamily E)
      (next : Fin r → QAlgorithms.Superop (Fin h × Fin b) (Fin c × Fin d))
      (valid : ∀ i, AdaptiveState Λ c d (n := n) (next i)) :
      AdaptiveState Λ c d (n := n)
        (fun X => ∑ i, next i (RetroCorr.Separation.aliceBranch (b := b) (E i) X))
  | bob {n a b h r : ℕ} (E : Fin r → Matrix (Fin h) (Fin b) ℂ)
      (complete : QAlgorithms.IsKrausFamily E)
      (next : Fin r → QAlgorithms.Superop (Fin a × Fin h) (Fin c × Fin d))
      (valid : ∀ i, AdaptiveState Λ c d (n := n) (next i)) :
      AdaptiveState Λ c d (n := n)
        (fun X => ∑ i, next i (RetroCorr.Separation.bobBranch (a := a) (E i) X))
  | send {n a a' b b' : ℕ} (e : Fin a ≃ Fin a' × I) (f : Fin b' ≃ O × Fin b)
      (next : QAlgorithms.Superop (Fin a' × Fin b') (Fin c × Fin d))
      (valid : AdaptiveState Λ c d (n := n) next) :
      AdaptiveState Λ c d (n := n + 1)
        (fun X => next (RetroCorr.Separation.sendVia e f Λ X))

end BindingEntChannels


