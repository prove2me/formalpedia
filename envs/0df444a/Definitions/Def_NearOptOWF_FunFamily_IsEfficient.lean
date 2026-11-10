-- Prove2me | Definitions.Def_NearOptOWF_FunFamily_IsEfficient
-- name    : NearOptOWF_FunFamily_IsEfficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:22.144204+00:00
-- url     : https://prove2.me/theorems/d7e14cf1-a2f6-4d47-b403-6f639a50aa45
-- title:
--   Efficiently sampleable family
-- statement:
--   A family is **efficiently sampleable** if it uses polynomially many coins in $n$, every sampled circuit has $m(n)$ output bits, and one machine computes the description of the sampled circuit from $(1^n, \rho)$ in polynomial time. In particular the sampled circuits have polynomial size.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_NearOptOWF_FunFamily
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace NearOptOWF

open LaconicBarrier

/-- The family is **efficiently sampleable** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13); the candidate
`H` of Eq. (1) is sampled by a PPT algorithm): polynomially many coins in `n`, every sampled circuit
has `m(n)` output wires, and one machine computes the description of `samp n ρ` from `(1ⁿ, ρ)` in
polynomial time (so the sampled circuits have polynomial size). -/
def FunFamily.IsEfficient {m : ℕ → ℕ} (H : FunFamily m) : Prop :=
  (∃ q : Polynomial ℕ, ∀ n, H.coins n ≤ q.eval n) ∧
  (∀ (n : ℕ) (ρ : Fin (H.coins n) → Bool), (H.samp n ρ).outs.length = m n) ∧
  PolyTimeOn (ι := (n : ℕ) × (Fin (H.coins n) → Bool)) (fun i => [unary i.1, bits i.2])
    (fun i => (H.samp i.1 i.2).code)

end NearOptOWF


