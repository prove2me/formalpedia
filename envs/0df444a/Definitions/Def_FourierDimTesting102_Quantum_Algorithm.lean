-- Prove2me | Definitions.Def_FourierDimTesting102_Quantum_Algorithm
-- name    : FourierDimTesting102_Quantum_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:02:06.235547+00:00
-- url     : https://prove2.me/theorems/5c142fd8-b6f0-4091-980e-55b35f2351b8
-- title:
--   Algorithm 1 as a frozen adaptive quantum query algorithm, with its one-query state preparation
-- statement:
--   Quantum access to $f$ is the oracle $O_f:|x\rangle|b\rangle\mapsto|x\rangle|b\oplus b_f(x)\rangle$. This file builds, without reference to $f$, the query algorithms of the paper's Section 3.
--
--   1. The preparation $A_f=H\,O_f\,H$ applied to $|0^n\rangle|1\rangle$, where $H$ is the Hadamard transform on all $n+1$ qubits. It uses one query.
--   2. The iterate $G=A_f R_0 A_f^\dagger R_{\mathrm{mark}}$, where $R_0=2|0^n,1\rangle\langle0^n,1|-I$ and $R_{\mathrm{mark}}$ negates the strings $s\notin W$. The amplified algorithm with $j$ iterates is a literal $(2j+1)$-query algorithm with query-free gates between the oracle calls.
--   3. Algorithm 1 itself. Set $W=\{0\}$. For $m=64(k+1)$ rounds: draw a number of iterates $j$, run the amplified algorithm, measure a string $s$, set $W=\operatorname{span}(W,s)$, and reject if $\dim W>k$. Accept after the last round. Here $j=0$ with a fair coin, and otherwise $j$ is uniform on $\{0,\dots,L\}$, with $L=\lceil2/\sqrt\epsilon\rceil$. For $\epsilon>1/2$ the algorithm accepts at once with no queries.
--
--   The tree of rounds is fixed by $n$, $k$ and $\epsilon$ before any input. The final definition is the largest number of queries on any branch of a tree.
--
--   **Formalization Note** The algorithm is a published `AdaptiveQueryAlg`, whose evaluation inserts the XOR oracle of the input and takes the actual Born probabilities. The classical coin and index are a zero-query round measuring a uniform workspace. The constants $64(k+1)$ and $\lceil2/\sqrt\epsilon\rceil$ and the coin are this formalization's instantiation of the source's $m=O(k)$ and its $O(1/\sqrt\epsilon)$ cap; they are not printed in the paper. The number of iterates is random because the Fourier mass outside $W$ is unknown to the algorithm. Target bit $1$ gives the phase kickback of the source's phase query, and $A_f$ is its own inverse, so an uncomputation costs one more query.
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.12 §2.2 oracle; p.13 Lemma 3.1; p.14 Algorithm 1

import Definitions.Def_QAlgorithms_Defs_AdaptiveQuery
import Definitions.Def_QAlgorithms_Defs_Search
import Definitions.Def_FourierDimTesting102_Quantum_Model

/-!
# Algorithm 1 as a frozen adaptive quantum query algorithm

Kenny Chen, *Exponential Quantum Advantage in Testing Fourier Dimensionality*, September 2026
STOC 2027 submission #102 preprint, §2.2 (p.12), Lemma 3.1 (p.13), Algorithm 1 (p.14).

Nothing in this file takes the function `f` as an argument: `f` enters only through the published
evaluation of `AdaptiveQueryAlg`, as the XOR oracle `|x,b⟩ ↦ |x, b ⊕ b_f(x)⟩`. The constants
`ampCap`, `roundCount` and the coin of `coinAlg` instantiate the source's unspecified `O(·)`.
-/

namespace FourierDimTesting102.Quantum

open QAlgorithms

/-- The register of an oracle round: query input `x`, target bit `b`, one-point workspace. -/
abbrev Reg (n : ℕ) := (V n × Bool) × Fin 1

/-- The `n`-fold Hadamard transform on `F₂ⁿ`, with entry `2^{-n/2} χ_s(x)`. -/
noncomputable def hadV (n : ℕ) : Matrix (V n) (V n) ℂ :=
  Matrix.of fun s x => (((Real.sqrt (2 ^ n))⁻¹ * chi s x : ℝ) : ℂ)

theorem hadV_star (n : ℕ) : star (hadV n) = hadV n := by
  ext s x
  simp [hadV, Matrix.star_apply, chi_comm x s]

theorem hadV_mul_self (n : ℕ) : hadV n * hadV n = 1 := by
  ext s t
  have hsq : ((Real.sqrt (2 ^ n))⁻¹ * (Real.sqrt (2 ^ n))⁻¹ : ℝ) = (2 ^ n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have hrow : ∀ x : V n, hadV n s x * hadV n x t =
      (((2 ^ n : ℝ)⁻¹ * chi (s + t) x : ℝ) : ℂ) := by
    intro x
    simp only [hadV, Matrix.of_apply]
    rw [← Complex.ofReal_mul, chi_comm x t, chi_add_left, ← hsq]
    congr 1
    ring
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun x _ => hrow x, ← Complex.ofReal_sum,
    ← Finset.mul_sum]
  by_cases hst : s = t
  · subst hst
    have h0 : s + s = 0 := by
      ext i
      exact CharTwo.add_self_eq_zero (s i)
    have hc : ∑ x : V n, chi (s + s) x = 2 ^ n := by
      simp [h0, chi, ZMod.card]
    rw [hc]
    simp
  · have h0 : s + t ≠ 0 := by
      intro h
      apply hst
      ext i
      have hi : s i + t i = 0 := congrFun h i
      exact (CharTwo.add_eq_zero).mp hi
    rw [sum_chi_eq_zero h0]
    simp [hst]

theorem hadamard_star : star hadamard = hadamard := by
  ext a b
  cases a <;> cases b <;> simp [hadamard, Matrix.star_apply]

/-- The Hadamard layer: `H^{⊗n}` on the input register, `H` on the target bit. -/
noncomputable def hadAll (n : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.kronecker (Matrix.kronecker (hadV n) hadamard) (1 : Matrix (Fin 1) (Fin 1) ℂ)

theorem hadAll_star (n : ℕ) : star (hadAll n) = hadAll n := by
  have h1 : star (hadV n) = hadV n := hadV_star n
  have h2 : star hadamard = hadamard := hadamard_star
  rw [Matrix.star_eq_conjTranspose] at h1 h2 ⊢
  simp [hadAll, Matrix.conjTranspose_kronecker, h1, h2]

theorem hadAll_mul_self (n : ℕ) : hadAll n * hadAll n = 1 := by
  simp [hadAll, ← Matrix.mul_kronecker_mul, hadV_mul_self, hadamard_mul_self]

/-- The Hadamard layer as a unitary. -/
noncomputable def hadU (n : ℕ) : Matrix.unitaryGroup (Reg n) ℂ :=
  ⟨hadAll n, Matrix.mem_unitaryGroup_iff.mpr (by rw [hadAll_star, hadAll_mul_self])⟩

theorem diagonal_sign_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop)
    [DecidablePred P] :
    Matrix.diagonal (fun i => if P i then (1 : ℂ) else -1) ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  by_cases h : P i <;> simp [h]

open Classical in
/-- Step 3 of Algorithm 1: the marking `|s,b⟩ ↦ -|s,b⟩` for `s ∉ W`, identity for `s ∈ W`.
This is a query-free gate, computed from `W` alone. -/
noncomputable def markOp {n : ℕ} (W : Submodule (ZMod 2) (V n)) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun p => if p.1.1 ∈ W then 1 else -1

/-- The marking as a unitary. -/
noncomputable def markU {n : ℕ} (W : Submodule (ZMod 2) (V n)) : Matrix.unitaryGroup (Reg n) ℂ :=
  ⟨markOp W, by classical exact diagonal_sign_mem _⟩

/-- The start index `|0ⁿ⟩|1⟩`: input register `0`, target bit `1`. -/
def initIndex (n : ℕ) : Reg n := ((0, true), 0)

/-- The query-free reflection `2|0ⁿ,1⟩⟨0ⁿ,1| - I`. -/
noncomputable def reflU (n : ℕ) : Matrix.unitaryGroup (Reg n) ℂ :=
  ⟨reflAt (initIndex n), by unfold reflAt; exact diagonal_sign_mem _⟩

/-- Lemma 3.1, p.13: the one-query preparation `H O_f H |0ⁿ,1⟩`, frozen before `f`. -/
noncomputable def prepAlg (n : ℕ) : QueryAlg (V n) Bool (Fin 1) 1 where
  start := ket (initIndex n)
  start_unit := by simp [ket]
  U := fun _ => hadU n

/-- Lemma 3.1, p.13: the vector `|ψ_f⟩ = ∑_s f̂(s)|s⟩`, real amplitudes embedded into `ℂ`. -/
noncomputable def fourierState {n : ℕ} (f : BoolFn n) : EuclideanSpace ℂ (V n) :=
  WithLp.toLp 2 fun s => (coeff f s : ℂ)

/-- The preparation operator `A_f = H O_f H`, which contains one XOR query. It is its own inverse,
so the uncomputation `A_f†` in a reflection about the prepared state is one further query. -/
noncomputable def prepOp {n : ℕ} (f : BoolFn n) : Matrix (Reg n) (Reg n) ℂ :=
  hadAll n * Matrix.kronecker (xorOracle f) (1 : Matrix (Fin 1) (Fin 1) ℂ) * hadAll n

/-- Step 3 of Algorithm 1: the amplitude-amplification iterate `G = A_f R_0 A_f† R_mark`, the
published `ampAmpIterate`, for the prepared state and the strings outside `W`. -/
noncomputable def groverOp {n : ℕ} (f : BoolFn n) (W : Submodule (ZMod 2) (V n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  ampAmpIterate (prepOp f) (markOp W) (initIndex n)

/-- The gate schedule of `amplifiedAlg`: with `T = 2j+1` queries, the gate `U_i` following the
`i`-th query is `H` at both ends, `H R_mark H` at odd `i < T`, and `H R_0 H` at even `0 < i < T`,
so that `U_T O ⋯ O U_0 = G^j A_f` (each `H O H` is a copy of `A_f` or of `A_f†`). -/
noncomputable def ampGate {n : ℕ} (W : Submodule (ZMod 2) (V n)) (T i : ℕ) :
    Matrix.unitaryGroup (Reg n) ℂ :=
  if i = 0 ∨ i = T then hadU n
  else if i % 2 = 1 then hadU n * markU W * hadU n
  else hadU n * reflU n * hadU n

/-- Step 3 of Algorithm 1 with `j` amplification iterates, as a literal `(2j+1)`-query algorithm:
one query prepares the state, and each iterate costs two more (`A_f†` and `A_f`). -/
noncomputable def amplifiedAlg {n : ℕ} (W : Submodule (ZMod 2) (V n)) (j : ℕ) :
    QueryAlg (V n) Bool (Fin 1) (2 * j + 1) where
  start := ket (initIndex n)
  start_unit := by simp [ket]
  U := fun i => ampGate W (2 * j + 1) i

/-- A zero-query round whose measured workspace is uniform on `Fin (2(L+1))`: the classical coin
and index of Algorithm 1's schedule, which consult no oracle. -/
noncomputable def coinAlg (n L : ℕ) : QueryAlg (V n) Bool (Fin (2 * (L + 1))) 0 where
  start := tensorVec (ket ((0, false) : V n × Bool)) (uniformState (Fin (2 * (L + 1))))
  start_unit := by
    have hw : (0 : ℝ) < ((2 * (L + 1) : ℕ) : ℝ) := by positivity
    have hsq : (‖tensorVec (ket ((0, false) : V n × Bool))
        (uniformState (Fin (2 * (L + 1))))‖) ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_eq_single (0, false)]
      · simp only [tensorVec, uniformState, ket, Fintype.card_fin, PiLp.single_apply]
        simp only [if_true, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          inv_pow, Real.sq_sqrt hw.le]
        exact mul_inv_cancel₀ hw.ne'
      · intro p _ hp
        simp [tensorVec, ket, hp]
      · simp
    have hnn := norm_nonneg (tensorVec (ket ((0, false) : V n × Bool))
      (uniformState (Fin (2 * (L + 1)))))
    nlinarith [sq_nonneg (‖tensorVec (ket ((0, false) : V n × Bool))
      (uniformState (Fin (2 * (L + 1))))‖ - 1)]
  U := fun _ => 1

/-- The iteration count read from the coin round: the first half of the workspace is the coin's
"no amplification" outcome, and the second half is the uniform index `j ∈ {0,…,L}`. -/
def iterCount (L : ℕ) (t : Fin (2 * (L + 1))) : ℕ :=
  if t.val < L + 1 then 0 else t.val - (L + 1)

/-- Lines 2–7 of Algorithm 1, for `r` remaining rounds and current span `W`: draw the iteration
count, run the amplified preparation, measure a string `s`, set `W := span(W, s)`, reject if
`dim W > k`, and accept when no rounds remain. Output `true` is accept, `false` is reject. -/
noncomputable def testerLoop (n k L : ℕ) :
    ℕ → Submodule (ZMod 2) (V n) → AdaptiveQueryAlg (V n) Bool
  | 0, _ => .halt true
  | r + 1, W =>
      .round 0 (2 * (L + 1)) (coinAlg n L) fun c =>
        .round (2 * iterCount L c.2 + 1) 1 (amplifiedAlg W (iterCount L c.2)) fun z =>
          if k < Module.finrank (ZMod 2)
              (W ⊔ Submodule.span (ZMod 2) {z.1.1} : Submodule (ZMod 2) (V n))
          then .halt false
          else testerLoop n k L r (W ⊔ Submodule.span (ZMod 2) {z.1.1})

/-- The amplification cap `L = ⌈2/√ε⌉`, instantiating the source's `O(1/√ε)`. -/
noncomputable def ampCap (ε : ℝ) : ℕ := ⌈2 / Real.sqrt ε⌉₊

/-- The round count `m = 64(k+1)`, instantiating the source's `m = O(k)`. -/
def roundCount (k : ℕ) : ℕ := 64 * (k + 1)

open Classical in
/-- Algorithm 1, p.14, fixed from `n`, `k`, `ε` alone. For `ε > 1/2` no function is `ε`-far (a
constant function is within `1/2`), and the algorithm accepts with zero queries. -/
noncomputable def tester (n k : ℕ) (ε : ℝ) : AdaptiveQueryAlg (V n) Bool :=
  if 1 / 2 < ε then .halt true else testerLoop n k (ampCap ε) (roundCount k) ⊥

/-- The largest total number of oracle queries on any branch of the tree, of positive probability
or not. It does not depend on the input. -/
noncomputable def worstCaseQueries {ι α : Type} [Fintype ι] [DecidableEq ι] :
    AdaptiveQueryAlg ι α → ℕ
  | .halt _ => 0
  | .round T _ _ next => T + Finset.univ.sup fun z => worstCaseQueries (next z)

end FourierDimTesting102.Quantum


