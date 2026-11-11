-- Prove2me | Definitions.Def_QNoiseStab_singleNoiseOp
-- name    : QNoiseStab_singleNoiseOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:00.273203+00:00
-- url     : https://prove2.me/theorems/7b4e428a-d699-47f1-a6e0-ef19ea94d5a0
-- title:
--   Single-coordinate noise operator $T_p=p\,|\hat0\rangle\langle\hat0|+(1-p)I$
-- statement:
--   For $p\in\mathbb R$, the single-coordinate noise operator on $\mathbb C^{\mathbb Z_m}$ is
--
--   $$
--   T_p=p\,|\hat0\rangle\langle\hat0|+(1-p)\,I,
--   $$
--
--   where $|\hat0\rangle=m^{-1/2}\sum_x|x\rangle$. It can be read as the Markov transition matrix of the noise $N_p$ (Proposition 3.1).
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, p.11 (T_p)

import Mathlib
import Definitions.Def_QNoiseStab_fourierKet
import Definitions.Def_QNoiseStab_ketBra

namespace QNoiseStab

/-- The single-coordinate noise operator `T_p = p |0̂⟩⟨0̂| + (1 − p) I` on `ℂ^{Z_m}`
(Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space
Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, p.11:
"Tp = p |0̂⟩⟨0̂| + (1 − p) I"), where `|0̂⟩ = m^{-1/2} Σ_x |x⟩` is the Fourier state of frequency `0`.

**Formalization Note** Defined for every real `p`. -/
noncomputable def singleNoiseOp {m : ℕ} [NeZero m] (p : ℝ) : Matrix (ZMod m) (ZMod m) ℂ :=
  (p : ℂ) • ketBra (fourierKet (0 : ZMod m)) + ((1 - p : ℝ) : ℂ) • (1 : Matrix (ZMod m) (ZMod m) ℂ)

end QNoiseStab


