-- Prove2me | Definitions.Def_QStateSearch_Supplement_yesState
-- name    : QStateSearch_Supplement_yesState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:22:50.192212+00:00
-- url     : https://prove2.me/theorems/84c4d03b-cfa5-4da6-aeb9-c72fdea2a5de
-- title:
--   Yes-sampler state $|Y_{n,t}\rangle$
-- statement:
--   For $t\ge1$,
--   $$|Y_{n,t}\rangle=\frac1{\sqrt K}\sum_{x\in L_n}|x\rangle|\psi_x\rangle^{\otimes t}|1\rangle\qquad\text{(Eq. (6))},$$
--   on $n(t+1)+1$ qubits, with $K=|L_n|$: the label, $t$ copies of $|\psi_x\rangle$, and a final $|1\rangle$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Eq. (6), p.17

import Mathlib
import Definitions.Def_QStateSearch_Supplement_qIdx
import Definitions.Def_QStateSearch_Supplement_blockAt

set_option autoImplicit false

namespace QStateSearch.Supplement

open Classical in
/-- The **yes-sampler state** `|Y_{n,t}⟩ = K^{-1/2} Σ_{x ∈ L_n} |x⟩|ψ_x⟩^{⊗t}|1⟩` on
`k = n(t + 1) + 1` qubits, with `K = |L_n|`: wires `0, …, n − 1` hold the label `x`, the next
`t` blocks of `n` wires hold the copies of `|ψ_x⟩`, and wire `n(t + 1)` holds `|1⟩`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Eq. (6), p.17: "For every integer t ≥ 1, define |Y_{n,t}⟩ = (1/√K) Σ_{x∈L_n} |x⟩|ψ_x⟩^{⊗t}|1⟩".

**Formalization Note.** The amplitude of a basis state `z` is `K^{-1/2} Π_j ψ_x(z_j)` when its
label `x` lies in `L_n` and its last wire is `1`, else `0` (bits beyond wire `n(t + 1)` do not
occur when `k = n(t + 1) + 1`). `K` is the size of `L_n`, which equals `⌊2^{n/2}⌋` in a
realization (`IsSec6Realization`). -/
noncomputable def yesState (L : (n : ℕ) → Finset (Fin n → Bool))
    (ψ : (n : ℕ) → (Fin n → Bool) → EuclideanSpace ℂ (Fin (2 ^ n))) (n t k : ℕ) :
    (Fin k → Bool) → ℂ := fun z =>
  if blockAt z 0 n ∈ L n ∧ bitAt z (n * (t + 1)) = true then
    (((Real.sqrt ((L n).card : ℝ))⁻¹ : ℝ) : ℂ) *
      ∏ j : Fin t, ψ n (blockAt z 0 n) (qIdx n (blockAt z (n + j.val * n) n))
  else 0

end QStateSearch.Supplement


