-- Prove2me | Definitions.Def_HZTractability_Supplement_TwoSlopeInst
-- name    : HZTractability_Supplement_TwoSlopeInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:29:40.627055+00:00
-- url     : https://prove2.me/theorems/dd3b5d3f-b280-40b8-82f4-9bad02532026
-- title:
--   Two-slope HZ instances (display (1)), their input encoding and the output condition of Theorem 1.3
-- statement:
--   A **two-slope HZ instance** has $N\ge1$ buyers and $N$ goods, rational slopes $c^{(1)}_i\ge c^{(2)}_i\ge0$ for each buyer $i$ (common across goods for that buyer, possibly different between buyers) and rational breakpoints $\tau_{ij}\in[0,1]$ for each buyer–good pair. Buyer $i$'s utility is separable,
--   $$U_i(x_i)=\sum_j f_{ij}(x_{ij}),\qquad f_{ij}(t)=c^{(2)}_i t+\big(c^{(1)}_i-c^{(2)}_i\big)\min\{t,\tau_{ij}\},\quad 0\le t\le1.$$
--   Budgets, supplies and bundle quantities are one.
--
--   The module also fixes how such an instance is given to and returned by an arithmetic machine: the input is the list of numbers $N,\ c^{(1)}_1,\dots,c^{(1)}_N,\ c^{(2)}_1,\dots,c^{(2)}_N,\ \tau$ row-major; its binary length $L$ is the sum of the encoding lengths of these numbers; and the output condition says that the allocation $x$ (row-major, $x_{ij}$ in cell $iN+j$) followed by the prices $p$ (cells $N^2,\dots,N^2+N-1$) form an exact normalized HZ equilibrium with minimum-expenditure tie-breaking for the utilities $U_i$.
--
--   These are the instances and the output of Theorem 1.3.
--
--   **Formalization Note** The utilities are the input's own, not normalized. Encoding lengths are the published `SepQPTardos.Main.ratLen` / `vecLen` / `ratMatLen`; memory layout uses the published `vecList`, `matList`, `readVec`. Equal slopes and $c^{(2)}_i=0$ are allowed.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), display (1), p.2 (PDF p.4); Definition 6.1, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_SepQPTardos_Main_Encoding
import Definitions.Def_SepQPTardos_Main_Machine
import Definitions.Def_HZTractability_Supplement_IsMinExpEq

set_option autoImplicit false

namespace HZTractability.Supplement

/-- **A two-slope HZ instance** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held version,
sha256 74b7bf9f…, display (1), p.2 (PDF 4); Definition 6.1, p.24 (PDF 26)): `N` buyers and `N` goods;
for each buyer `i` slopes `c1 i = c^{(1)}_i`, `c2 i = c^{(2)}_i`, and for each buyer–good pair a
breakpoint `τ i j = τ_ij`. All data are rational. -/
structure TwoSlopeInst where
  N : ℕ
  c1 : Fin N → ℚ
  c2 : Fin N → ℚ
  τ : Fin N → Fin N → ℚ

namespace TwoSlopeInst

/-- The input conditions of (1) and Definition 6.1: `N ≥ 1` (§2.2, p.7), `c^{(1)}_i ≥ c^{(2)}_i ≥ 0`
for every buyer and `τ_ij ∈ [0, 1]` for every pair. Equal slopes and `c^{(2)}_i = 0` are allowed. -/
def Valid (I : TwoSlopeInst) : Prop :=
  1 ≤ I.N ∧ (∀ i, 0 ≤ I.c2 i ∧ I.c2 i ≤ I.c1 i) ∧ ∀ i j, 0 ≤ I.τ i j ∧ I.τ i j ≤ 1

/-- Buyer `i`'s separable utility (1): `U_i(y) = ∑_j f_ij(y_j)` with
`f_ij(t) = c^{(2)}_i t + (c^{(1)}_i − c^{(2)}_i) min{t, τ_ij}`, the input's own (unnormalized)
utility. On unit bundles every `y_j ∈ [0, 1]`, the domain `0 ≤ t ≤ 1` of (1). -/
noncomputable def util (I : TwoSlopeInst) (i : Fin I.N) (y : Fin I.N → ℝ) : ℝ :=
  ∑ j, ((I.c2 i : ℝ) * y j + ((I.c1 i : ℝ) - (I.c2 i : ℝ)) * min (y j) (I.τ i j : ℝ))

/-- The input as a list of numbers, in memory cells `0, 1, …`: `N`, then `c^{(1)}_1, …, c^{(1)}_N`,
then `c^{(2)}_1, …, c^{(2)}_N`, then the breakpoints `τ_ij` row-major (`N² + 2N + 1` numbers). -/
noncomputable def input (I : TwoSlopeInst) : List ℝ :=
  (I.N : ℝ) :: (SepQPTardos.Main.vecList (fun i => (I.c1 i : ℝ)) ++
    SepQPTardos.Main.vecList (fun i => (I.c2 i : ℝ)) ++
    SepQPTardos.Main.matList (fun i j => (I.τ i j : ℝ)))

/-- The binary input length `L`: the encoding length (published `SepQPTardos.Main.ratLen`) of `N`
plus the encoding lengths of all slopes and breakpoints. -/
def inputLen (I : TwoSlopeInst) : ℕ :=
  SepQPTardos.Main.ratLen (I.N : ℚ) + SepQPTardos.Main.vecLen I.c1 +
    SepQPTardos.Main.vecLen I.c2 + SepQPTardos.Main.ratMatLen I.τ

/-- The output condition: the memory holds the allocation `x` row-major in cells `0, …, N² − 1`
(`x_ij` in cell `iN + j`) and the prices `p` in cells `N², …, N² + N − 1`, and `(p, x)` is an exact
normalized HZ equilibrium with minimum-expenditure tie-breaking for the utilities `util`
(`IsMinExpEq`). -/
def Out (I : TwoSlopeInst) (mem : ℤ → ℝ) : Prop :=
  IsMinExpEq I.util (fun i => SepQPTardos.Main.readVec mem (i.val * I.N) I.N)
    (SepQPTardos.Main.readVec mem (I.N * I.N) I.N)

end TwoSlopeInst

end HZTractability.Supplement


