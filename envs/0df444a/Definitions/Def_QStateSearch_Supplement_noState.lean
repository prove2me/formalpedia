-- Prove2me | Definitions.Def_QStateSearch_Supplement_noState
-- name    : QStateSearch_Supplement_noState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:23:17.534002+00:00
-- url     : https://prove2.me/theorems/c9e213bd-5a50-490a-bd1e-6c0378223ff9
-- title:
--   No-sampler state $|N_n\rangle$
-- statement:
--   $$|N_n\rangle=\frac1{\sqrt{N-K}}\sum_{x\notin L_n}|x\rangle|1\rangle\qquad\text{(Eq. (6))},$$
--   on $n+1$ qubits, with $N=2^n$ and $K=|L_n|$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Eq. (6), p.17

import Mathlib
import Definitions.Def_QStateSearch_Supplement_blockAt

set_option autoImplicit false

namespace QStateSearch.Supplement

open Classical in
/-- The **no-sampler state** `|N_n⟩ = (N − K)^{-1/2} Σ_{x ∉ L_n} |x⟩|1⟩` on `k = n + 1` qubits,
with `N = 2^n` and `K = |L_n|`: wires `0, …, n − 1` hold the label, wire `n` holds `|1⟩`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Eq. (6), p.17: "|N_n⟩ = (1/√(N − K)) Σ_{x∉L_n} |x⟩|1⟩." -/
noncomputable def noState (L : (n : ℕ) → Finset (Fin n → Bool)) (n k : ℕ) :
    (Fin k → Bool) → ℂ := fun z =>
  if blockAt z 0 n ∉ L n ∧ bitAt z n = true then
    (((Real.sqrt ((2 : ℝ) ^ n - (L n).card))⁻¹ : ℝ) : ℂ)
  else 0

end QStateSearch.Supplement


