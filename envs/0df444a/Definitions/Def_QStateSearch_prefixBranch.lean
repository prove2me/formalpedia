-- Prove2me | Definitions.Def_QStateSearch_prefixBranch
-- name    : QStateSearch_prefixBranch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:35.49921+00:00
-- url     : https://prove2.me/theorems/2b8c7ba3-a53e-4d21-ae75-dec067a2ecd9
-- title:
--   Identity-prefix branch vectors
-- statement:
--   In the **identity-prefix execution** every oracle call before slot $t$ is replaced by the identity. For a transcript $h$ before slot $t$, the identity-prefix branch vector $\phi_h$ is the unnormalized verifier vector just before slot $t$ when the prover's replies are those recorded in $h$. It depends neither on the hidden state nor on the prover.
--
--   Against a prover $P_\psi$, the branch with transcript $h$ is $\phi_h$ if $P_\psi$ sends every prover message recorded in $h$, and $0$ otherwise; its probability is $\|\phi_h\|^2$ in the first case.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 3, pp.10–11

import Mathlib
import Definitions.Def_QStateSearch_ctrlQuery
import Definitions.Def_QStateSearch_Step
open Matrix

namespace QStateSearch

/-- The identity-prefix branches. `prefixBranch steps t φ h h'` is the unnormalized verifier
vector just before the query slot with 0-based index `t`, on the branch with transcript `h'`,
when every earlier query is the identity and the prover's replies are the ones recorded in `h'`
(the run starts in `φ` after transcript `h`).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 3, pp.10–11: "replace every verifier oracle call before slot t by the identity.
… We call this the identity-prefix execution."

**Formalization Note.** The vector does not depend on the hidden state or on the prover: a
prover message sums over all replies `z ∈ Fin (2 ^ b)`, each recorded in the transcript. Against a
prover `P`, the actual identity-prefix branch with transcript `h'` is `prefixBranch … h'` when `P`
sends every prover message recorded in `h'` (`consistent`) and `0` otherwise. Earlier queries
apply `controlled-I`. Lean slot `t` is the paper's slot `t + 1`. -/
noncomputable def prefixBranch {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] :
    List (Step D W) → ℕ → (Reg D W → ℂ) → List ℕ → List ℕ → Reg D W → ℂ
  | [], _, φ, h => fun h' => if h' = h then φ else 0
  | .query :: _, 0, φ, h => fun h' => if h' = h then φ else 0
  | .query :: rest, t + 1, φ, h => prefixBranch rest t (ctrlQuery 1 *ᵥ φ) h
  | .unitary U :: rest, t, φ, h =>
      prefixBranch rest t ((U : Matrix (Reg D W) (Reg D W) ℂ) *ᵥ φ) h
  | .vmsg m K :: rest, t, φ, h => fun h' =>
      ∑ a : Fin m, prefixBranch rest t (K a *ᵥ φ) (h ++ [a.val]) h'
  | .pmsg b U :: rest, t, φ, h => fun h' =>
      ∑ z : Fin (2 ^ b),
        prefixBranch rest t ((U z : Matrix (Reg D W) (Reg D W) ℂ) *ᵥ φ) (h ++ [z.val]) h'

end QStateSearch


