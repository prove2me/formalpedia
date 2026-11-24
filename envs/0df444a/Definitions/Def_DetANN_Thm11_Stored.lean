-- Prove2me | Definitions.Def_DetANN_Thm11_Stored
-- name    : DetANN_Thm11_Stored
-- status  : Definition
-- author  : @milia
-- created : 2026-11-23T21:57:32.100798+00:00
-- url     : https://prove2.me/theorems/1d6f37f4-92be-4cad-9a9c-31f24fc62b2b
-- title:
--   Theorem 1.1: projected databases, inner guarantees, and the stored state of the outer preprocessing
-- statement:
--   Interfaces between the outer programs of §7.4 (definition `DetANN_Thm11_OuterProg`) and the statement of Theorem 1.1. Fix $P:[n]\to\mathbb R^d$, $\varepsilon$, a padding exponent $k$, and $C_0>0$. Let $L=\mathrm{annReps}\,C_0\,k\,P\,\varepsilon$, $\ell=\mathrm{walkLen}\,\varepsilon$ and $m=16^\ell L$.
--   - $\mathrm{annSigns}\,C_0\,k\,P\,\varepsilon$ are the greedy signs of $\mathrm{annBlocks}\,C_0\,k\,P\,\varepsilon$.
--   - $\mathrm{superProj}\,C_0\,k\,P\,\varepsilon\,v\,z\in\mathbb R^m$ is the superblock projection $\mathcal A_vz$: coordinate $wL+r$ is $(A_{\mathrm{walkEnd}(v,w)}z)_r$.
--   - $\mathrm{projDB}\,C_0\,k\,P\,\varepsilon\,v:[n]\to\mathbb R^m$, $i\mapsto\mathcal A_v(\mathrm{pad}\,P_i)$, is the database of the inner structure for tuple $v$.
--   - $\mathrm{InnerSpec}(\mathrm{Pre}_3,\mathrm{Qry}_3,C,K,C')$ holds when, for all $m,N\ge1$, all injective $Y:[N]\to\mathbb R^m$ and all $\delta\in(0,1/2)$, the pair is a deterministic $(1+\delta)$-ANN structure for $Y$ with the bounds of Lemma 3.3:
--     - preprocessing time $C'(N+m)^K(C/\delta)^{Km}\log^K(N/\delta)$;
--     - space $C'N(C/\delta)^{Km}\log^K(N/\delta)$;
--     - query time $C'm^2\log^2(N/\delta)$.
--   - $\mathrm{innerQT}=C'm^2\log^2(n/\delta)$ with $\delta=\varepsilon/100$ is the inner query time on $\mathrm{projDB}$.
--   - $\mathrm{OuterStored}(\mathrm{Pre}_3,X_3,T_q,P,\varepsilon,C_0,k,s)$ describes the halted state $s$ of the outer preprocessing. It requires $d\le2^k<2d$ and the following:
--     1. the parameter cells $2,\dots,14$, the tables of row bases, walk endpoints and multiples $jL$, and the unchanged input;
--     2. separation: everything above lies below the window $W_T=b_T+[-R_T,R_T]$, which lies below the windows $W_v=b_0+v(2R_3+1)+[-R_3,R_3]$;
--     3. $W_T$ holds $L$, $2^k$, the signs $\mathrm{annSigns}$ and zero padding query cells, and its integer cells are bounded with room for one more run of $\mathrm{ev}$;
--     4. every $W_v$ agrees with a halted run of $\mathrm{Pre}_3$ on the input layout of $\mathrm{projDB}\,C_0\,k\,P\,\varepsilon\,v$ with parameter $\delta$, with room for any inner query of time at most $T_q$.
--
--   These are the interfaces between the preprocessing half (theorem `outer_pre_spec`) and the query half (theorem `outer_qry_spec`) of the machine part of Theorem 1.1.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' for the machine part of DetANN.theorem_1_1 (Feng, Indyk, STOC 2027 submission, Theorem 1.1, p.2; the construction of §7.4, p.19). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Supplement_EvProg

/-!
# Theorem 1.1: the projected databases and the stored state of the outer preprocessing

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.4, p.19.

* `annSigns C₀ k P ε` are the greedy signs of `annBlocks C₀ k P ε`, so `annBlocks` is
  `signedBlocks (sylvester k) L (annSigns …)` with `L = annReps C₀ k P ε`.
* `superProj C₀ k P ε v z ∈ ℝ^m` with `m = 16^ℓ · L` (`ℓ = walkLen ε`) is the superblock projection
  `𝒜_v z`: the concatenation over the walks `w < 16^ℓ` from `v` of `A_{walkEnd(v, w)} z ∈ ℝ^L`.
  Coordinate `c = w·L + r` is `(A_{walkEnd(v, w)} z) r`. Walk `w` takes the steps given by its
  base-16 digits, least significant digit first (`finFunctionFinEquiv`). The order does not matter
  for norms, but it is the order in which the outer program stores the projections.
* `projDB C₀ k P ε v i = 𝒜_v(pad P_i)` is the database of the inner structure of tuple `v`.
* `OuterStored …` describes the halted state of the outer preprocessing: parameter cells, tables,
  the window `W_T` (signs and counts read by the evaluation program `ev`), and the windows `W_v`,
  each agreeing with a halted run of the inner preprocessing on `projDB … v`, with room for one
  inner query.
-/

namespace DetANN.Thm11

open PNormReg PNormRegLib

/-- The greedy signs of `annBlocks C₀ k P ε`. -/
noncomputable def annSigns {d n : ℕ} (C₀ : ℝ) (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    Fin (annReps C₀ k P ε) → Fin (2 ^ k) → Bool :=
  greedySigns (lemma62Expr (sylvester k) (annReps C₀ k P ε) (annTau ε)
    (momentOrder (diffSet k P).card (2 ^ k)) (diffSet k P)) (annReps C₀ k P ε * 2 ^ k)

/-- The superblock projection `𝒜_v z`, flattened as `w·L + r`. -/
noncomputable def superProj {d n : ℕ} (C₀ : ℝ) (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (v : Fin (2 ^ k)) (z : EuclideanSpace ℝ (Fin (2 ^ k))) :
    EuclideanSpace ℝ (Fin (16 ^ walkLen ε * annReps C₀ k P ε)) :=
  WithLp.toLp 2 fun c =>
    annBlocks C₀ k P ε (annTuples k ε v (finFunctionFinEquiv.symm (finProdFinEquiv.symm c).1)) z
      (finProdFinEquiv.symm c).2

/-- The database of the inner structure of tuple `v`: `i ↦ 𝒜_v(pad P_i)`. -/
noncomputable def projDB {d n : ℕ} (C₀ : ℝ) (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (v : Fin (2 ^ k)) : Fin n → EuclideanSpace ℝ (Fin (16 ^ walkLen ε * annReps C₀ k P ε)) :=
  fun i => superProj C₀ k P ε v (padVec (2 ^ k) (P i))

/-- The guarantees of Lemma 3.3 for the inner pair, with constants `C, K, C'`. -/
def InnerSpec (Pre₃ Qry₃ : Program) (C : ℝ) (K C' : ℕ) : Prop :=
  ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
    ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        IsDetANNStructure Pre₃ Qry₃ Y δ (1 + δ)
          ((C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
          ((C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
          ((C' : ℝ) * (m : ℝ) ^ 2 * Real.log (N / δ) ^ 2)

/-- The inner query time bound for the database `projDB … v`: `C' m² log²(n/δ)` with `m = 16^ℓ L`,
`δ = ε/100`. -/
noncomputable def innerQT {d n : ℕ} (C' : ℕ) (C₀ : ℝ) (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d))
    (ε : ℝ) : ℝ :=
  (C' : ℝ) * ((16 ^ walkLen ε * annReps C₀ k P ε : ℕ) : ℝ) ^ 2 * Real.log (n / (ε / 100)) ^ 2

/-- **The stored state of the outer preprocessing.** For the instance `P`, `ε`, padding exponent `k`
and constant `C₀`, with `L = annReps C₀ k P ε`, `ℓ = walkLen ε`, `m = 16^ℓ L`, `δ = ε/100`.
`X3` bounds the literals of the inner programs, and `Tq` bounds the inner query time.
1. Integer cells `0, 1` still hold `n, d`. Cells `2 … 14` hold `n, d, 2^k, L, m, 16^ℓ, ℓ, b_T, b_0,
   2R₃ + 1, w_B, w_{LB}, r_B`. The tables hold the row bases `r_B + i ↦ 1 + i d`, the walk
   endpoints `w_B + v·16^ℓ + w ↦ walkEnd(v, w)` and the multiples `w_{LB} + j ↦ j L`. The input
   points are unchanged.
2. Separation: the input, the parameter cells and the tables lie below `W_T = b_T + [−R_T, R_T]`,
   which lies below the windows `W_v = b_0 + v(2R₃ + 1) + [−R₃, R₃]`.
3. `W_T` (seen from `b_T`) holds `L` and `2^k` in integer cells `0, 1`, the signs `annSigns` in the
   sign cells of `ev`, and zeros in the padding query cells `−1 − r`, `d ≤ r < 2^k`. Its integer cells
   are bounded by some `X ≥` the literals of `ev`, with `X·2^{82 L 2^k (1+k)} ≤ R_T` (room for one run
   of `ev`).
4. Every `W_v` agrees with a halted run of `Pre₃` on `inputState (projDB … v) δ`, and the radius
   leaves room for any inner query of time at most `Tq`. -/
def OuterStored (Pre₃ : Program) (X3 : ℕ) (Tq : ℝ) {d n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin d))
    (ε C₀ : ℝ) (k : ℕ) (s : State) : Prop :=
  d ≤ 2 ^ k ∧ 2 ^ k < 2 * d ∧
  ∃ (bT RT b0 R3 wB wLB rbB : ℤ),
    -- 1. parameters, tables, input
    s.integerMemory 0 = n ∧ s.integerMemory 1 = d ∧
    s.integerMemory 2 = n ∧ s.integerMemory 3 = d ∧ s.integerMemory 4 = ((2 ^ k : ℕ) : ℤ) ∧
    s.integerMemory 5 = (annReps C₀ k P ε : ℤ) ∧
    s.integerMemory 6 = ((16 ^ walkLen ε * annReps C₀ k P ε : ℕ) : ℤ) ∧
    s.integerMemory 7 = ((16 ^ walkLen ε : ℕ) : ℤ) ∧ s.integerMemory 8 = (walkLen ε : ℤ) ∧
    s.integerMemory 9 = bT ∧ s.integerMemory 10 = b0 ∧ s.integerMemory 11 = 2 * R3 + 1 ∧
    s.integerMemory 12 = wB ∧ s.integerMemory 13 = wLB ∧ s.integerMemory 14 = rbB ∧
    (∀ i : Fin n, s.integerMemory (rbB + (i : ℕ)) = 1 + (i : ℤ) * d) ∧
    (∀ (v : Fin (2 ^ k)) (w : Fin (16 ^ walkLen ε)),
      s.integerMemory (wB + ((v : ℕ) * 16 ^ walkLen ε + w : ℕ)) =
        ((annTuples k ε v (finFunctionFinEquiv.symm w) : ℕ) : ℤ)) ∧
    (∀ j : Fin (2 ^ k), s.integerMemory (wLB + (j : ℕ)) = (j : ℤ) * annReps C₀ k P ε) ∧
    (∀ (i : Fin n) (c : Fin d), s.core.mem (1 + ((i : ℕ) * d + c : ℕ)) = P i c) ∧
    -- 2. separation
    15 ≤ rbB ∧ rbB + n ≤ bT - RT ∧ 15 ≤ wB ∧ wB + ((2 ^ k * 16 ^ walkLen ε : ℕ) : ℤ) ≤ bT - RT ∧
    15 ≤ wLB ∧ wLB + ((2 ^ k : ℕ) : ℤ) ≤ bT - RT ∧ 1 + ((n * d : ℕ) : ℤ) ≤ bT - RT ∧ 15 ≤ bT - RT ∧
    0 ≤ RT ∧ 0 ≤ R3 ∧ bT + RT < b0 - R3 ∧
    -- 3. the window W_T
    s.integerMemory bT = (annReps C₀ k P ε : ℤ) ∧ s.integerMemory (bT + 1) = ((2 ^ k : ℕ) : ℤ) ∧
    (∀ (ℓ : Fin (annReps C₀ k P ε)) (r : Fin (2 ^ k)),
      s.core.mem (bT + (-(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r))) =
        signOf (annSigns C₀ k P ε ℓ r)) ∧
    (∀ r : ℕ, d ≤ r → r < 2 ^ k → s.core.mem (bT + (-1 - (r : ℤ))) = 0) ∧
    (∃ X : ℤ, LitBound (Supplement.Thm32.ev 0) X ∧ 1 ≤ X ∧
      (∀ z : ℤ, |z| ≤ RT → |s.integerMemory (bT + z)| ≤ X) ∧
      X * 2 ^ (82 * (annReps C₀ k P ε * 2 ^ k * (1 + k))) ≤ RT) ∧
    -- 4. the windows W_v
    ∀ v : Fin (2 ^ k), ∃ t : ℕ,
      (run Pre₃ (inputState (projDB C₀ k P ε v) (ε / 100)) detTape t).halted = true ∧
      (∀ z : ℤ, |z| ≤ R3 →
        s.core.mem (b0 + (v : ℤ) * (2 * R3 + 1) + z) =
          (run Pre₃ (inputState (projDB C₀ k P ε v) (ε / 100)) detTape t).core.mem z ∧
        s.integerMemory (b0 + (v : ℤ) * (2 * R3 + 1) + z) =
          (run Pre₃ (inputState (projDB C₀ k P ε v) (ε / 100)) detTape t).integerMemory z) ∧
      ∀ t' : ℕ, (t' : ℝ) ≤ Tq →
        ((n + 16 ^ walkLen ε * annReps C₀ k P ε + 1 + X3 : ℕ) : ℤ) * 2 ^ (t + t') ≤ R3

end DetANN.Thm11


