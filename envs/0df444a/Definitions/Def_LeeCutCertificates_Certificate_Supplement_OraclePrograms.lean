-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Supplement_OraclePrograms
-- name    : LeeCutCertificates_Certificate_Supplement_OraclePrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:00:18.00503+00:00
-- url     : https://prove2.me/theorems/b7c8c8d8-07fa-4e75-95fc-460c407e2931
-- title:
--   Deterministic exact-real oracle programs
-- statement:
--   A deterministic **oracle program** either returns an output or asks one specified query and continues as a function of the exact real answer. Execution returns its output and the number of query nodes actually visited. For every real answer function $f$, a cap $b$ means
--
--   $$\operatorname{cost}(p,f)\le b.$$
--
--   The program has no access to a hidden graph, matrix or measure other than through these answers. Offline choices are unrestricted. Correctness and resource bounds are asserted by the subsequent theorems, rather than assumed by the program type.
--
--   **Formalization Note** The inductive interaction tree is well founded; every run terminates. Its continuation may branch on any exact real answer.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §6, printed p.17 (PDF p.18); §11.8, printed p.42 (PDF p.43); Appendix A, printed p.53 (PDF p.54)

import Mathlib

set_option autoImplicit false

namespace LeeCutCertificates.Certificate.Supplement

/-- Deterministic exact-real oracle interaction, with no hidden-input access. -/
inductive OracleProgram (Q O : Type) where
  | done (output : O)
  | ask (query : Q) (next : ℝ → OracleProgram Q O)

/-- The output and the number of ask nodes actually visited. -/
def OracleProgram.run {Q O : Type} : OracleProgram Q O → (Q → ℝ) → O × ℕ
  | .done o, _ => (o, 0)
  | .ask q next, oracle =>
    let r := (next (oracle q)).run oracle
    (r.1, r.2 + 1)

/-- A bound on all answer paths, including answers inconsistent with any input. -/
def OracleProgram.Capped {Q O : Type} (p : OracleProgram Q O) (b : ℝ) : Prop :=
  ∀ oracle : Q → ℝ, ((p.run oracle).2 : ℝ) ≤ b

end LeeCutCertificates.Certificate.Supplement


