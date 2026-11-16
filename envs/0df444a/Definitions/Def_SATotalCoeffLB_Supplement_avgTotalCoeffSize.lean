-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_avgTotalCoeffSize
-- name    : SATotalCoeffLB_Supplement_avgTotalCoeffSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:30:55.365882+00:00
-- url     : https://prove2.me/theorems/257b40e4-aa51-4952-a2fe-d8b319879ade
-- title:
--   Averaging total coefficient size $\mathbb E_q\bigl[\sum_{p\in P}\|C_p(W,q)\|_1\bigr]$
-- statement:
--   For a finite set $P$ of polynomials in the $W$-variables and multipliers $C_p \in \mathbb R[W, Q]/\langle y^2-1\rangle$, $p \in P$, the **averaging total coefficient size** (without extension variables) is
--
--   $$
--   \mathop{\mathbb E}_{q \leftarrow \{\pm1\}^Q}\Bigl[\,\sum_{p \in P} \|C_p(W, q)\|_1\Bigr] = 2^{-|Q|} \sum_{q \in \{\pm1\}^Q} \sum_{p \in P} \|C_p(W, q)\|_1 ,
--   $$
--
--   where $\|f\|_1$ is the sum of the absolute values of the coefficients of the multilinear polynomial $f$ in the $W$-variables.
--
--   **Formalization Note** The multipliers are a function $p \mapsto C_p$; its values outside $P$ do not matter. $\|\cdot\|_1$ is the published `SATotalCoeffLB.coeffNorm`.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), pp.6–7 (Averaging total coefficient size); Theorem 9, p.74

import Mathlib
import Definitions.Def_SATotalCoeffLB_coeffNorm
import Definitions.Def_SATotalCoeffLB_Supplement_substQ

namespace SATotalCoeffLB.Supplement

open SATotalCoeffLB

/-- **Averaging total coefficient size without extension variables** (p.6–7 and Theorem 9,
p.74, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)): for multipliers `(C_p)_{p ∈ P}` in `ℝ[W, Q]/⟨y² − 1⟩`,
`E_{q ← {±1}^Q} [∑_{p ∈ P} ‖C_p(W, q)‖₁]`, where `‖·‖₁` is the sum of the absolute values of
the coefficients of the multilinear polynomial `C_p(W, q)` in the `W`-variables.

**Formalization Note** The expectation is the uniform average over the `2^{|Q|}` bit vectors
`q`; multipliers are given as a function `C` of `p`. -/
noncomputable def avgTotalCoeffSize {W Q : Type*} [Fintype W] [DecidableEq W] [Fintype Q]
    [DecidableEq Q] (P : Finset (CubeFn W)) (C : CubeFn W → CubeFn (W ⊕ Q)) : ℝ :=
  ((2 : ℝ) ^ Fintype.card Q)⁻¹ * ∑ q : Q → ZMod 2, ∑ p ∈ P, coeffNorm (substQ (C p) q)

end SATotalCoeffLB.Supplement


