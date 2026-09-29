-- Prove2me | Definitions.Def_Zeta23_Assembly_Inputs
-- name    : Zeta23_Assembly_Inputs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:01:38.885692+00:00
-- url     : https://prove2.me/theorems/37be7587-1d1c-4130-bc3d-ac62c72ca86b
-- title:
--   Interfaces from prop:block and prop:tail consumed by the assembly
-- statement:
--   This bundle defines the interface between the producers of the two key matrix-level facts (`ZeroSide.lean` for the paper's prop:block, `Tail.lean` for prop:tail) and their consumer `Assembly.lean`, so the producing files can prove these statements without importing the whole assembly. It fixes an abstract zero configuration $Z$, parameters $P$, and a height $T$; matrices below are the zero-side matrices of `Defs.lean` in tilde units $\tilde A = A/L$ [eq:AE] and hat units $\hat A = A/(aL^2)$ [eq:hatunits].
--
--   **`NII`** is the natural number $N(I'\setminus I) := N(T - D_0, T) + N(2T, 2T + D_0)$, the zero count of the two fringe windows of $I' = (T - D_0, 2T + D_0]$ beyond $I = [T,2T]$ (paper prop:zeroside), with $D_0 = T^{1/2}$.
--
--   **`BlockInputs`** packages prop:block + [eq:Ncount]: (in hat units) there exist matrices $\hat A = P_m + Q_m$ with $P_m$ positive semidefinite of rank $\le s_1 + s_2$ and $\mathrm{tr}\, P_m \le N_{on}(I')$, $Q_m$ Hermitian with positive index $n_+(Q_m) \le p$, and $N_{on}(I') + 2p \le N(I')$; (in tilde units) $n_+(\tilde A) \le s_1 + s_2 + p$, $\mathrm{rank}(\tilde A) \le \#\mathcal{Z}(I')$, and $s_1 + 2s_2 + 2p \le N(I')$. The number $p$ of off-line zero pairs is existentially quantified, since only these displayed inequalities are consumed downstream.
--
--   **`TailInputs`** $(\theta_0)$ packages prop:tail: $\theta_0 \ge 0$; every eigenvalue of the Hermitian tail matrix $\tilde E$ is at most $\theta_0$ in absolute value (i.e. $\|\tilde E\| \le \theta_0$ in operator norm); and there is $B \ge 0$ (in practice the trace norm $\|\hat E\|_1$) with $|\mathrm{tr}\,\hat E| \le B$, $\|\hat E\|_F^2 \le B^2$, and $B \le \theta_0/(aL)$.
--
--   `ZeroSide.lean` proves $\forall^\infty T,\ \mathrm{BlockInputs}$ and `Tail.lean` proves `TailInputs`; `Main.lean` plugs both into `Assembly.thmA_abstract` to complete Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly/Inputs.lean, docstring tags [prop:block], [prop:tail], [eq:Ncount]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
  Bracketed labels ([prop:cross], [eq:Msplit], …) and section numbers (§5.4, …) refer to that paper.
-/

/-!
# Interfaces consumed by `Zeta23/Assembly.lean` from `ZeroSide.lean` (prop:block) and `Tail.lean` (prop:tail)
This small file exists so that `ZeroSide.lean` / `Tail.lean` can *prove*
`∀ᶠ T, BlockInputs Z P T` / `TailInputs Z P T (θ₀ T)` without importing all of `Assembly.lean`, and
`Main.lean`  can plug those proofs into `Assembly.thmA_abstract`.
Every field is a statement announced by the producing file; docstrings quote the paper labels.
-/

noncomputable section

open Matrix RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace Assembly

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

/-- `N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)` (the paper prop:zeroside), as a natural number. -/
def NII : ℕ := Z.N (T - D0 T) T + Z.N (2 * T) (2 * T + D0 T)

/-- **Inputs from prop:block + [eq:Ncount] at height `T`** (the paper `prop:block`:
"(i) `n₊(Ã) ≤ s₁+s₂+p` and `rank(Ã) ≤ s₁+s₂+2p = #𝒵(I′)`.
 (ii) `Â = P+Q` with `P,Q` real symmetric, `P ⪰ 0`, `rank P ≤ s₁+s₂`, `tr P ≤ N_on(I′)`, and `n₊(Q) ≤ p`";
[eq:Ncount]: "`N(I′) ≥ s₁+2s₂+2p`" and "`N(I′) ≥ N_on(I′)+2p`"), produced by `ZeroSide.lean`.
Units: `Ã = P.tilde T (Z.Az P T)` [eq:AE], `Â = P.hat T (Z.Az P T)` [eq:hatunits].
`p` (number of off-line pairs in `𝒵(I′)`) is existentially quantified since only the displayed
inequalities involving it are consumed downstream. -/
structure BlockInputs : Prop where
  /-- prop:block(ii) in hat units + "`N_on(I′) + 2p ≤ N(I′)`" -/
  hat : ∃ (Pm Qm : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ) (p : ℕ)
      (_ : Pm.PosSemidef) (hQm : Qm.IsHermitian),
      P.hat T (Z.Az P T) = Pm + Qm ∧ Pm.rank ≤ Z.s1 T + Z.s2 T ∧
      rtrace Pm ≤ (Z.NonIprime T : ℝ) ∧ posIndex hQm ≤ p ∧
      (Z.NonIprime T : ℝ) + 2 * p ≤ Z.NIprime T
  /-- prop:block(i) in tilde units + "`N(I′) ≥ s₁ + 2s₂ + 2p`" [eq:Ncount] -/
  tilde : ∃ (p : ℕ) (hAt : (P.tilde T (Z.Az P T)).IsHermitian),
      posIndex hAt ≤ Z.s1 T + Z.s2 T + p ∧ (P.tilde T (Z.Az P T)).rank ≤ (Z.ZIprime T).ncard ∧
      (Z.s1 T : ℝ) + 2 * Z.s2 T + 2 * p ≤ Z.NIprime T

/-- **Inputs from prop:tail at height `T`** (the paper `prop:tail`: "`‖Ẽ‖ ≤ θ₀ := 4A₀C₁²X^{1/2}
log(4T)/D₀²` … Moreover the trace norm satisfies `‖Ê‖₁ ≤ θ₀/(aL) ≤ 2θ₀/L`"), produced by
`Tail.lean` with `B = traceNorm Ê`.  Units: `Ẽ = P.tilde T (Z.Ez P T)`, `Ê = P.hat T (Z.Ez P T)`. -/
structure TailInputs (θ₀ : ℝ) : Prop where
  theta_nonneg : 0 ≤ θ₀
  /-- lem:weyl's hypothesis: every eigenvalue of `Ẽ` is at most `θ₀` in absolute value
  (this is `‖Ẽ‖ ≤ θ₀` for the operator norm of a Hermitian matrix) -/
  tilde : ∃ hEt : (P.tilde T (Z.Ez P T)).IsHermitian, ∀ i, |hEt.eigenvalues i| ≤ θ₀
  /-- `|tr Ê| ≤ ‖Ê‖₁`, `‖Ê‖_F ≤ ‖Ê‖₁`, `‖Ê‖₁ ≤ θ₀/(aL)` -/
  hat : ∃ B : ℝ, 0 ≤ B ∧ |rtrace (P.hat T (Z.Ez P T))| ≤ B ∧
      frobSq (P.hat T (Z.Ez P T)) ≤ B ^ 2 ∧ B ≤ θ₀ / (P.a T * P.L T)

end Assembly
end Zeta23

end


