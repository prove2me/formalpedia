-- Prove2me | Definitions.Def_GEGIAMP_Relative_Algorithm
-- name    : GEGIAMP_Relative_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:53:42.406541+00:00
-- url     : https://prove2.me/theorems/8fd3a0d0-c4e2-45ac-b682-37a0219468ce
-- title:
--   Algorithm 1 (GEG-IAMP) as a program of the oracle machine, its runs and laws
-- statement:
--   `alg1 κ` writes Algorithm 1 of Appendix A line by line: the grid (6.1)–(6.2); the check $d>N\Rightarrow$ return $\mathbf 1$; the quadrature (6.5)–(6.6); drawing the leading $B\times B$ block of $J$; $Y=0$, $\widehat M=\sqrt\Delta\mathbf 1$, $\lambda=0$; for each group the residual, the zero-residual rule, the normalized query, the dense product $Aq_s$ and the corrected output (6.13), and per coordinate the Householder reconstruction from fresh Gaussian draws and the $m_f$ updates (6.14); then clipping, the rounding product $\ell=Av-\mathrm{diag}(A)v$ and sequential rounding (ties to $+1$). Input layout ($N$, $\varepsilon$, $A$), output array, the standalone rounding routine and grid+quadrature routine, the Parisi oracles, the choice of $K_R$ in (6.5), the run, the tape law and the joint law GOE$(N)\otimes$ i.i.d. $N(0,1)$, and the tape positions of $J$ and the side variables.
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Appendix A, Algorithm 1, p. 66; §6, pp. 16–20

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Machine
import Definitions.Def_GEGIAMP_Relative_Construction

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-!
# Algorithm 1 (GEG-IAMP) as a program of the oracle machine

Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1 (SHA-256 ea6508af…5658e),
Appendix A, Algorithm 1, p. 66, with the specification of §6 (pp. 16–20): grid (6.1)–(6.2),
point quadrature (6.5)–(6.6), the leading `B × B` block of `J` (5.7), queries (6.12) and the
zero-residual rule, corrected outputs (6.13), Householder reconstruction (6.9)–(6.10),
updates (6.14), `f = M̂ − √Δ 1` (6.15), clipping and sequential rounding.

`alg1 κ` is one concrete program of `Def_GEGIAMP_Relative_Machine`, written line by line from
Algorithm 1, with the fixed algorithmic constants `κ = (c_τ, c_h, c_B, c_q, K_R)` as real
literals. Its work, storage, product count and step count are those of the machine semantics.

**Input layout** (`initState`): `Z 0 = N`; `R 0 = ε` (internal accuracy);
`R (100 + iN + j) = A_ij`. All other cells are `0`; the tape is the i.i.d. `N(0,1)` tape.
**Output**: `R (100 + N² + i)`, `i < N` (`outVec`).

**Tape order.** First the upper triangle of the leading `B × B` block of `J`, row by row
(`r = 0, …, B−1`, `s = r, …, B−1`), scaled by `√(2/N)` on the diagonal and `√(1/N)` off it;
then, for each group `s` and each coordinate `i` in order, the `m_f − 1` side variables of
(6.10). `tapeJ` and `tapeSide` read these values off the tape (used to compare the program
with the mathematical construction of `Def_GEGIAMP_Relative_Construction`).

Integer registers: `Z 0` N, `Z 1` = 1, `Z 2` = 0, `Z 3` B, `Z 4` m_f, `Z 5` K, `Z 6` d,
`Z 7…19` loop counters and temporaries, `Z 20…33` array bases. Real registers `R 1…99` hold
constants and temporaries; arrays start at `R 100`.
-/

namespace GEGIAMP.Relative

noncomputable section

open Cmd

/-! ## Register map -/

section Regs
-- integer registers
def zN : ℕ := 0
def zOne : ℕ := 1
def zZero : ℕ := 2
def zB : ℕ := 3
def zMf : ℕ := 4
def zK : ℕ := 5
def zD : ℕ := 6
def zS : ℕ := 7
def zI : ℕ := 8
def zJ : ℕ := 9
def zK2 : ℕ := 10
def zR : ℕ := 11
def zJJ : ℕ := 12
def zStar : ℕ := 13
def zT1 : ℕ := 14
def zT2 : ℕ := 15
def zAddr : ℕ := 16
def zRq : ℕ := 17
def zJg : ℕ := 18
def zT3 : ℕ := 19
def zBaseA : ℕ := 20
def zOut : ℕ := 21
def zY : ℕ := 22
def zM : ℕ := 23
def zL : ℕ := 24
def zLam : ℕ := 25
def zF : ℕ := 26
def zRes : ℕ := 27
def zV : ℕ := 28
def zZ : ℕ := 29
def zQ : ℕ := 30
def zJm : ℕ := 31
def zGam : ℕ := 32
def zX : ℕ := 33
-- real registers
def rEps : ℕ := 0
def r0 : ℕ := 1
def r1 : ℕ := 2
def r2 : ℕ := 3
def rE : ℕ := 4
def rHalf : ℕ := 5
def rCt : ℕ := 6
def rCh : ℕ := 7
def rCB : ℕ := 8
def rCq : ℕ := 9
def rKR : ℕ := 10
def rLe : ℕ := 11
def rTau : ℕ := 12
def rT : ℕ := 13
def rLt : ℕ := 14
def rB : ℕ := 15
def rDel : ℕ := 16
def rHs : ℕ := 17
def rMf : ℕ := 18
def rH : ℕ := 19
def rN : ℕ := 20
def rSqD : ℕ := 21
def rRq : ℕ := 22
def rEtaq : ℕ := 23
def rSqN : ℕ := 24
def rS1 : ℕ := 25
def rS2 : ℕ := 26
def rSqH : ℕ := 27
def rM1 : ℕ := 28
def rLhs : ℕ := 29
def rRhs : ℕ := 30
def a1 : ℕ := 31
def a2 : ℕ := 32
def a3 : ℕ := 33
def a4 : ℕ := 34
def a5 : ℕ := 35
def a6 : ℕ := 36
def a7 : ℕ := 37
def a8 : ℕ := 38
def rNrm : ℕ := 39
def rAcc : ℕ := 40
def rC : ℕ := 41
def rInv : ℕ := 42
def rUx : ℕ := 43
def rUu : ℕ := 44
def rU : ℕ := 45
def rTk : ℕ := 46
def rTk1 : ℕ := 47
def rRr : ℕ := 48
def rSum : ℕ := 49
end Regs

/-! ## Program combinators -/

/-- `Z i := Z i + 1`. -/
def zinc (i : ℕ) : Cmd := op (.zadd i i zOne)

/-- `for Z i = 0, …, Z hi − 1 do body`. -/
def forUp (i hi : ℕ) (body : Cmd) : Cmd :=
  seqs [op (.zlit i 0), .while (.zlt i hi) (seqs [body, zinc i])]

/-- `R d := R (Z base + Z idx)`. -/
def ld (d base idx : ℕ) : Cmd := seqs [op (.zadd zAddr base idx), op (.load d zAddr)]

/-- `R (Z base + Z idx) := R src`. -/
def st (base idx src : ℕ) : Cmd := seqs [op (.zadd zAddr base idx), op (.store zAddr src)]

/-- `R d := R (Z base + Z row · Z stride + Z col)`. -/
def ld2 (d base row stride col : ℕ) : Cmd :=
  seqs [op (.zmul zAddr row stride), op (.zadd zAddr zAddr col), op (.zadd zAddr zAddr base),
    op (.load d zAddr)]

/-- `R (Z base + Z row · Z stride + Z col) := R src`. -/
def st2 (base row stride col src : ℕ) : Cmd :=
  seqs [op (.zmul zAddr row stride), op (.zadd zAddr zAddr col), op (.zadd zAddr zAddr base),
    op (.store zAddr src)]

/-- `R d := R s` (copy, as `R s + 0`). -/
def mov (d s : ℕ) : Cmd := op (.add d s r0)

/-! ## Phases of Algorithm 1 -/

/-- Constants and fixed algorithmic constants (literals). -/
noncomputable def setup (κ : AlgConsts) : Cmd :=
  seqs [op (.lit r0 0), op (.lit r1 1), op (.lit r2 2), op (.lit rE (Real.exp 1)),
    op (.lit rHalf (1 / 2)), op (.lit rM1 (-1)),
    op (.lit rCt κ.cτ), op (.lit rCh κ.ch), op (.lit rCB κ.cB), op (.lit rCq κ.cq),
    op (.lit rKR κ.KR), op (.zlit zOne 1), op (.zlit zZero 0), op (.cast rN zN),
    op (.zlit zBaseA 100)]

/-- `R a1 := τ³ L_ε`. -/
def tauLhs : Cmd :=
  seqs [op (.mul rLhs rTau rTau), op (.mul rLhs rLhs rTau), op (.mul rLhs rLhs rLe)]

/-- Line 1: the grid (6.1)–(6.2). -/
def grid : Cmd :=
  seqs [
    -- L_ε = log(e/ε)
    op (.div a1 rE rEps), op (.log rLe a1),
    -- c_τ³ ε²
    op (.mul rRhs rCt rCt), op (.mul rRhs rRhs rCt), op (.mul a1 rEps rEps),
    op (.mul rRhs rRhs a1),
    -- τ = 1/2, halve until τ³ L_ε ≤ c_τ³ ε²
    op (.lit rTau (1 / 2)), tauLhs,
    .while (.rlt rRhs rLhs) (seqs [op (.mul rTau rTau rHalf), tauLhs]),
    -- T = 1 − τ, L_τ = log(e/τ)
    op (.sub rT r1 rTau), op (.div a1 rE rTau), op (.log rLt a1),
    -- B = ⌈T/(c_B ε)⌉, Δ = T/B
    op (.mul a1 rCB rEps), op (.div a1 rT a1), op (.ceil zB a1), op (.cast rB zB),
    op (.div rDel rT rB),
    -- h* = c_h ε²/L_τ², m_f = ⌈Δ/h*⌉, h = Δ/m_f
    op (.mul a1 rEps rEps), op (.mul a1 rCh a1), op (.mul a2 rLt rLt), op (.div rHs a1 a2),
    op (.div a1 rDel rHs), op (.ceil zMf a1), op (.cast rMf zMf), op (.div rH rDel rMf),
    -- K = B m_f, d = B + 1
    op (.zmul zK zB zMf), op (.zadd zD zB zOne)]

/-- Array bases: output `v` at `100 + N²`, then `Y, M̂, ℓ, λ, F, r, v_s, z` (`N` cells each),
the queries (`B N`), `J` (`B²`), `Γ^q` (`K`), the reconstruction buffer (`m_f`). -/
def bases : Cmd :=
  seqs [op (.zmul zT1 zN zN), op (.zadd zOut zBaseA zT1), op (.zadd zY zOut zN),
    op (.zadd zM zY zN), op (.zadd zL zM zN), op (.zadd zLam zL zN), op (.zadd zF zLam zN),
    op (.zadd zRes zF zN), op (.zadd zV zRes zN), op (.zadd zZ zV zN), op (.zadd zQ zZ zN),
    op (.zmul zT1 zB zN), op (.zadd zJm zQ zT1), op (.zmul zT1 zB zB),
    op (.zadd zGam zJm zT1), op (.zadd zX zGam zK)]

/-- Line 5: `R = K_R Λ(T)`, `η_q = c_q ε²/R` (6.5) and the quadrature values `Γ^q_k` (6.6). -/
def quadrature : Cmd :=
  seqs [
    op (.sub a1 r1 rT), op (.div a2 rE a1), op (.log a2 a2), op (.div a2 a2 a1),
    op (.mul rRq rKR a2),
    op (.mul a1 rEps rEps), op (.mul a1 rCq a1), op (.div rEtaq a1 rRq),
    forUp zK2 zK (seqs [
      -- t_k, t_{k+1}
      op (.cast a1 zK2), op (.mul rTk a1 rH), op (.zadd zT2 zK2 zOne), op (.cast a1 zT2),
      op (.mul rTk1 a1 rH),
      -- r = max{1, ⌈(γ(t_{k+1}) − γ(t_k))/η_q⌉}
      op (.gam a2 rTk1), op (.gam a3 rTk), op (.sub a2 a2 a3), op (.div a2 a2 rEtaq),
      op (.ceil zRq a2), .ite (.zlt zRq zOne) (op (.zlit zRq 1)) .skip, op (.cast rRr zRq),
      -- trapezoid sum over the r subintervals
      op (.lit rSum 0),
      forUp zJ zRq (seqs [
        op (.cast a4 zJ), op (.mul a4 a4 rH), op (.div a4 a4 rRr), op (.add a4 rTk a4),
        op (.zadd zT2 zJ zOne), op (.cast a5 zT2), op (.mul a5 a5 rH), op (.div a5 a5 rRr),
        op (.add a5 rTk a5), op (.gam a6 a4), op (.gam a7 a5), op (.add a6 a6 a7),
        op (.add rSum rSum a6)]),
      -- Γ^q_k = h/(2r) · sum
      op (.mul a1 r2 rRr), op (.div a1 rH a1), op (.mul a1 a1 rSum), st zGam zK2 a1])]

/-- Line 6: draw the leading `B × B` block of `J` (5.7) and initialize `Y = 0`, `M̂ = √Δ 1`,
`λ = 0`. -/
def initDraw : Cmd :=
  seqs [
    op (.div a1 r1 rN), op (.sqrt rS1 a1), op (.div a1 r2 rN), op (.sqrt rS2 a1),
    forUp zR zB (seqs [
      op (.zadd zS zR zZero),
      .while (.zlt zS zB) (seqs [
        op (.gauss a2),
        .ite (.zlt zR zS) (op (.mul a2 a2 rS1)) (op (.mul a2 a2 rS2)),
        st2 zJm zR zB zS a2, st2 zJm zS zB zR a2,
        zinc zS])]),
    op (.sqrt rSqD rDel), op (.sqrt rSqN rN), op (.sqrt rSqH rH),
    forUp zI zN (seqs [st zY zI r0, st zM zI rSqD, st zLam zI r0])]

/-- `R rNrm := ‖r‖` for the residual array. -/
def resNorm : Cmd :=
  seqs [op (.lit rAcc 0),
    forUp zI zN (seqs [ld a1 zRes zI, op (.mul a1 a1 a1), op (.add rAcc rAcc a1)]),
    op (.sqrt rNrm rAcc)]

/-- Line 8: `F_s = M̂`, `r_s = F_s − ∑_{r<s} (q_rᵀF_s/N) q_r`. -/
def proposeResidual : Cmd :=
  seqs [
    forUp zI zN (seqs [ld a1 zM zI, st zF zI a1, st zRes zI a1]),
    forUp zR zS (seqs [
      op (.lit rAcc 0),
      forUp zI zN (seqs [ld2 a1 zQ zR zN zI, ld a2 zF zI, op (.mul a1 a1 a2),
        op (.add rAcc rAcc a1)]),
      op (.div rC rAcc rN),
      forUp zI zN (seqs [ld2 a1 zQ zR zN zI, op (.mul a1 rC a1), ld a2 zRes zI,
        op (.sub a2 a2 a1), st zRes zI a2])])]

/-- Lines 9–11: if `‖r_s‖ = 0`, `i* = min{j : λ_j < 1}` and
`r_s = e_{i*} − ∑_{r<s} (q_{r,i*}/N) q_r`. -/
def zeroResidual : Cmd :=
  seqs [
    op (.zlit zStar 0), op (.zlit zJ 0),
    .while (.zlt zJ zN) (seqs [
      ld a1 zLam zJ,
      .ite (.rlt a1 r1) (seqs [op (.zadd zStar zJ zZero), op (.zadd zJ zN zZero)]) (zinc zJ)]),
    forUp zI zN (st zRes zI r0), st zRes zStar r1,
    forUp zR zS (seqs [
      ld2 a1 zQ zR zN zStar, op (.div rC a1 rN),
      forUp zI zN (seqs [ld2 a1 zQ zR zN zI, op (.mul a1 rC a1), ld a2 zRes zI,
        op (.sub a2 a2 a1), st zRes zI a2])]),
    resNorm]

/-- Line 12: `q_s = √N r_s/‖r_s‖`, `λ_i ← λ_i + q_{s,i}²/N`. -/
def normalizeQuery : Cmd :=
  forUp zI zN (seqs [
    ld a1 zRes zI, op (.mul a1 a1 rSqN), op (.div a1 a1 rNrm), st2 zQ zS zN zI a1,
    op (.mul a2 a1 a1), op (.div a2 a2 rN), ld a3 zLam zI, op (.add a3 a3 a2), st zLam zI a3])

/-- Line 13: `v_s = A q_s` (one dense product, `N²` multiply–adds) and the corrected output
`z_s = v_s + ½(J_ss − q_sᵀv_s/N) q_s + ∑_{r<s} (J_rs − q_rᵀv_s/N) q_r` (6.13). -/
def queryProduct : Cmd :=
  seqs [
    .mark .queryProduct (forUp zI zN (seqs [
      op (.lit rAcc 0),
      forUp zJ zN (seqs [ld2 a1 zBaseA zI zN zJ, ld2 a2 zQ zS zN zJ, op (.mul a1 a1 a2),
        op (.add rAcc rAcc a1)]),
      st zV zI rAcc])),
    op (.lit rAcc 0),
    forUp zI zN (seqs [ld2 a1 zQ zS zN zI, ld a2 zV zI, op (.mul a1 a1 a2),
      op (.add rAcc rAcc a1)]),
    ld2 a3 zJm zS zB zS, op (.div rAcc rAcc rN), op (.sub rC a3 rAcc), op (.mul rC rC rHalf),
    forUp zI zN (seqs [ld a1 zV zI, ld2 a2 zQ zS zN zI, op (.mul a2 rC a2),
      op (.add a1 a1 a2), st zZ zI a1]),
    forUp zR zS (seqs [
      op (.lit rAcc 0),
      forUp zI zN (seqs [ld2 a1 zQ zR zN zI, ld a2 zV zI, op (.mul a1 a1 a2),
        op (.add rAcc rAcc a1)]),
      ld2 a3 zJm zR zB zS, op (.div rAcc rAcc rN), op (.sub rC a3 rAcc),
      forUp zI zN (seqs [ld2 a1 zQ zR zN zI, op (.mul a1 rC a1), ld a2 zZ zI,
        op (.add a2 a2 a1), st zZ zI a2])])]

/-- Line 15: in coordinate `i`, the buffer `x = (z_{s,i}, η_1, …, η_{m_f−1})` (fresh Gaussian
draws) and `G = √h H_rec x` (6.9)–(6.10), by one inner product and one rank-one update. -/
def reconstruct : Cmd :=
  seqs [
    forUp zK2 zMf (.ite (.zlt zZero zK2) (seqs [op (.gauss a1), st zX zK2 a1])
      (seqs [ld a1 zZ zI, st zX zK2 a1])),
    .ite (.zle zMf zOne)
      (seqs [ld a1 zX zZero, op (.mul a1 rSqH a1), st zX zZero a1])
      (seqs [
        op (.sqrt a1 rMf), op (.div rInv r1 a1),
        op (.lit rUx 0), op (.lit rUu 0),
        forUp zK2 zMf (seqs [
          .ite (.zlt zZero zK2) (op (.sub rU r0 rInv)) (op (.sub rU r1 rInv)),
          ld a2 zX zK2, op (.mul a3 rU a2), op (.add rUx rUx a3), op (.mul a3 rU rU),
          op (.add rUu rUu a3)]),
        op (.mul rC r2 rUx), op (.div rC rC rUu),
        forUp zK2 zMf (seqs [
          .ite (.zlt zZero zK2) (op (.sub rU r0 rInv)) (op (.sub rU r1 rInv)),
          ld a2 zX zK2, op (.mul a3 rC rU), op (.sub a2 a2 a3), op (.mul a2 rSqH a2),
          st zX zK2 a2])])]

/-- Lines 16–19: the `m_f` steps of group `s` in coordinate `i`:
`x ← Y_i; M̂_i ← M̂_i + a(t_j, x) G_{j,i}; Y_i ← x + Γ^q_j m(t_j, x) + G_{j,i}`. -/
def coordSteps : Cmd :=
  forUp zJJ zMf (.mark .step (seqs [
    op (.zmul zJg zS zMf), op (.zadd zJg zJg zJJ), op (.cast a1 zJg), op (.mul rTk a1 rH),
    ld a2 zY zI, ld a3 zM zI, ld a4 zX zJJ,
    op (.ao a5 rTk a2), op (.mul a5 a5 a4), op (.add a3 a3 a5), st zM zI a3,
    op (.mo a6 rTk a2), ld a7 zGam zJg, op (.mul a6 a7 a6), op (.add a6 a2 a6),
    op (.add a6 a6 a4), st zY zI a6]))

/-- Lines 7–21: the `B` groups. -/
def groups : Cmd :=
  forUp zS zB (seqs [
    proposeResidual, resNorm,
    .ite (.rle rNrm r0) zeroResidual .skip,
    normalizeQuery, queryProduct,
    forUp zI zN (seqs [reconstruct, coordSteps])])

/-- Line 22: `f = M̂ − √Δ 1`, `v = clip(f, [−1, 1]^N)` (stored in the output array). -/
def clipStep : Cmd :=
  forUp zI zN (seqs [
    ld a1 zM zI, op (.sub a1 a1 rSqD),
    .ite (.rlt r1 a1) (mov a1 r1) .skip, .ite (.rlt a1 rM1) (mov a1 rM1) .skip,
    st zOut zI a1])

/-- Lines 23–27: sequential rounding of the output array `v`: `ℓ = Av − diag(A)v` (one dense
product); for `i = 1, …, N`: `s_i = +1` if `ℓ_i ≥ 0` else `−1`, `δ_i = s_i − v_i`, `v_i = s_i`,
`ℓ ← ℓ + δ_i Ã_{:,i}`, `Ã = A − diag(A)` (the diagonal term is added and removed). -/
def rounding : Cmd :=
  seqs [
    .mark .roundProduct (forUp zI zN (seqs [
      op (.lit rAcc 0),
      forUp zJ zN (seqs [ld2 a1 zBaseA zI zN zJ, ld a2 zOut zJ, op (.mul a1 a1 a2),
        op (.add rAcc rAcc a1)]),
      ld2 a1 zBaseA zI zN zI, ld a2 zOut zI, op (.mul a1 a1 a2), op (.sub rAcc rAcc a1),
      st zL zI rAcc])),
    forUp zI zN (seqs [
      ld a1 zL zI, .ite (.rle r0 a1) (mov a2 r1) (mov a2 rM1),
      ld a3 zOut zI, op (.sub rC a2 a3), st zOut zI a2,
      forUp zJ zN (seqs [ld2 a4 zBaseA zJ zN zI, op (.mul a4 rC a4), ld a5 zL zJ,
        op (.add a5 a5 a4), st zL zJ a5]),
      ld2 a4 zBaseA zI zN zI, op (.mul a4 rC a4), ld a5 zL zI, op (.sub a5 a5 a4),
      st zL zI a5])]

/-- Lines 2–3: return the all-ones vector `1`. -/
def returnOnes : Cmd := forUp zI zN (st zOut zI r1)

/-- **Algorithm 1 (GEG-IAMP)**, Appendix A, p. 66, with fixed algorithmic constants `κ`. -/
noncomputable def alg1 (κ : AlgConsts) : Cmd :=
  seqs [setup κ, grid, bases,
    .ite (.zlt zN zD) returnOnes
      (seqs [quadrature, initDraw, groups, clipStep, rounding])]

/-- The sequential-rounding routine on its own (Lemma 8.17): input `Z 0 = N`, `A` at
`R (100 + iN + j)`, `v ∈ [−1,1]^N` at `R (100 + N² + i)`; output in place. -/
def roundingProgram : Cmd :=
  seqs [op (.lit r0 0), op (.lit r1 1), op (.lit rM1 (-1)), op (.zlit zOne 1),
    op (.zlit zZero 0), op (.zlit zBaseA 100), op (.zmul zT1 zN zN),
    op (.zadd zOut zBaseA zT1), op (.zadd zY zOut zN), op (.zadd zM zY zN),
    op (.zadd zL zM zN), rounding]

/-- Lines 1 and 5 on their own (Lemma 7.10's work and storage): the grid and the point
quadrature, run from `initState 0 _ ε _` (no matrix). The coefficients are left in the
`Γ^q` array, `R (100 + B² + k)`, `k < K`, when `N = 0`. -/
noncomputable def quadProgram (κ : AlgConsts) : Cmd :=
  seqs [setup κ, grid, bases, quadrature]

/-- The Parisi-data oracles of a fixed order parameter: `γ`, `m = Φₓ`, `a = Φₓₓ`. -/
noncomputable def parisiOracles {Ω : Type*} [MeasurableSpace Ω]
    (W : OAI.ZeroTemperatureSK.BrownianSystem Ω) (γ : OAI.ZeroTemperatureSK.OrderParameter) :
    Oracles :=
  { gam := gam γ, m := mF W γ, a := aF W γ }

/-- The choice of `K_R` in (6.5), p. 17: "a fixed constant large enough that
`a(t, x)² ≤ K_R Λ(t)`" for `0 ≤ t < 1`, `x ∈ ℝ`. -/
def KRValid {Ω : Type*} [MeasurableSpace Ω] (W : OAI.ZeroTemperatureSK.BrownianSystem Ω)
    (γ : OAI.ZeroTemperatureSK.OrderParameter) (κ : AlgConsts) : Prop :=
  ∀ t x : ℝ, 0 ≤ t → t < 1 → aF W γ t x ^ 2 ≤ κ.KR * Lam t

/-! ## Inputs, outputs and runs -/

/-- The input cells: `Z 0`, `R 0` and the `N²` cells of `A`. -/
def inputCells (N : ℕ) : Finset Cell :=
  {(true, 0), (false, 0)} ∪ (Finset.range (N * N)).image fun k => (false, 100 + k)

/-- The initial state on input `A` at internal accuracy `ε` with Gaussian tape `ω`. -/
noncomputable def initState (N : ℕ) (A : Fin N → Fin N → ℝ) (ε : ℝ) (ω : ℕ → ℝ) : State where
  R := fun k =>
    if k = 0 then ε
    else if h : 100 ≤ k ∧ k < 100 + N * N then
      A ⟨(k - 100) / N, by
          have hN : 0 < N := by
            rcases Nat.eq_zero_or_pos N with h0 | h0
            · simp [h0] at h; omega
            · exact h0
          exact Nat.div_lt_of_lt_mul (by omega)⟩
        ⟨(k - 100) % N, Nat.mod_lt _ (by
          rcases Nat.eq_zero_or_pos N with h0 | h0
          · simp [h0] at h; omega
          · exact h0)⟩
    else 0
  Z := fun k => if k = 0 then (N : ℤ) else 0
  tape := ω
  ptr := 0
  work := 0
  cells := inputCells N
  marks := fun _ => 0

/-- The real vector stored at `R (100 + N² + i)`, `i < N` (the output array). -/
def outVec (N : ℕ) (s : State) : Fin N → ℝ := fun i => s.R (100 + N * N + i)

/-- The initial state of `roundingProgram` on `(A, v)`. -/
noncomputable def roundInit (N : ℕ) (A : Fin N → Fin N → ℝ) (v : Fin N → ℝ) : State :=
  let s := initState N A 0 (fun _ => 0)
  { s with
    R := fun k => if h : 100 + N * N ≤ k ∧ k < 100 + N * N + N then v ⟨k - (100 + N * N), by omega⟩
      else s.R k
    cells := s.cells ∪ (Finset.range N).image fun k => (false, 100 + N * N + k) }

/-- The run of Algorithm 1 with oracles `O`, constants `κ`, at internal accuracy `ε` on
`(A, ω)`: its final state, if it terminates. -/
noncomputable def run (O : Oracles) (κ : AlgConsts) (N : ℕ) (ε : ℝ)
    (A : Fin N → Fin N → ℝ) (ω : ℕ → ℝ) : Option State :=
  finalState O (alg1 κ) (initState N A ε ω)

/-- The i.i.d. `N(0, 1)` tape of the algorithm's Gaussian draws. -/
noncomputable def tapeLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

/-- The joint law of the GOE input and the algorithm's randomness. -/
noncomputable def jointLaw (N : ℕ) : Measure ((Fin N → Fin N → ℝ) × (ℕ → ℝ)) :=
  (RandMatDisc.goe N).prod tapeLaw

/-- The tape position of the draw for `J_rs`, `r ≤ s < B` (row-major upper triangle). -/
def jIdx (B r s : ℕ) : ℕ := (∑ r' ∈ Finset.range r, (B - r')) + (s - r)

/-- The entries `J_rs` (`r, s < B`) that `alg1` draws, read off the tape: `√(1/N) ω_k` off
the diagonal, `√(2/N) ω_k` on it, symmetric; zero outside the leading `B × B` block. -/
noncomputable def tapeJ (N B : ℕ) (ω : ℕ → ℝ) : ℕ → ℕ → ℝ := fun r s =>
  if r < B ∧ s < B then
    if r = s then Real.sqrt (2 / N) * ω (jIdx B r r)
    else Real.sqrt (1 / N) * ω (jIdx B (min r s) (max r s))
  else 0

/-- The side variable `η_{s,i,j+1}` that `alg1` draws, read off the tape. -/
def tapeSide (N B mf : ℕ) (ω : ℕ → ℝ) : ℕ → Fin N → ℕ → ℝ := fun s i j =>
  ω (B * (B + 1) / 2 + (s * N + i) * (mf - 1) + j)

end

end GEGIAMP.Relative


