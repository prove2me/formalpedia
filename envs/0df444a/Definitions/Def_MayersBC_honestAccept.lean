-- Prove2me | Definitions.Def_MayersBC_honestAccept
-- name    : MayersBC_honestAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:05.374037+00:00
-- url     : https://prove2.me/theorems/c6385a1e-5dce-473a-a788-420db36db0f5
-- title:
--   Honest acceptance probability $\Pr(T_b(W^{(b)}) = ok)$
-- statement:
--   In a commitment where Alice commits to $b$ by sending the pure state $\psi_w$ with probability $p_b(w)$, Bob measures with a POVM $\{E_y\}$ and later accepts Alice's opening $w$ when a test $T_b(w, y)$ returns ok. In the honest protocol the probability that he accepts is
--
--   $$
--   \Pr\big(T_b(W^{(b)}) = ok\big) = \sum_{w} \sum_{y:\ T_b(w,y)} p_b(w)\, \operatorname{Tr}\big(E_y |\psi_w\rangle\langle\psi_w|\big) .
--   $$
--
--   **Formalization Note** The test is an arbitrary predicate on (bit, opening, Bob's outcome) and is decided classically. The shared information $(C, r)$ is suppressed, as in the paper.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, p.5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

namespace MayersBC

open Classical in
/-- Mayers, arXiv:quant-ph/9603015v3, section b, p.5: the probability `Pr(T_b(W^{(b)}) = ok)`
that Bob accepts the opening of `b` in the **honest** protocol. Alice draws `w` with probability
`p_b(w)` and sends the pure state `ψ_w`; Bob measures it with the POVM `E` and gets `y`; Alice
announces `w` and Bob accepts when the test `T_b(w, y)` returns ok:
`Σ_w Σ_y [T_b(w, y)] p_b(w) Tr(E_y |ψ_w⟩⟨ψ_w|)`.

**Formalization Note.** The test is any predicate `T : ZMod 2 → W → Y → Prop` (true = ok),
decided classically; `(C, r)` is suppressed as on p.4. Bits are `ZMod 2`. -/
noncomputable def honestAccept {W Y ι : Type} [Fintype W] [Fintype Y] [Fintype ι]
    (p : ZMod 2 → W → ℝ) (ψ : W → EuclideanSpace ℂ ι) (E : Y → Matrix ι ι ℂ)
    (T : ZMod 2 → W → Y → Prop) (b : ZMod 2) : ℝ :=
  ∑ w, ∑ y, if T b w y then p b w * effectProb (E y) (pureDensity (ψ w)) else 0

end MayersBC


