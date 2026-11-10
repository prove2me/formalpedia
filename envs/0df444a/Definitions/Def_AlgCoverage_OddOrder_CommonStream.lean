-- Prove2me | Definitions.Def_AlgCoverage_OddOrder_CommonStream
-- name    : AlgCoverage_OddOrder_CommonStream
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:45:28.539991+00:00
-- url     : https://prove2.me/theorems/a9e9a06e-7336-4b09-8f7e-7ebdf725fc46
-- title:
--   Common-stream block matrices $T_{j,n}$, left kernels, the full-support and nononto events over fair selector bits, and the constants (5.2), (5.7)
-- statement:
--   Fix a field $F$, a dimension $d$, and a **common stream** $U_1,\dots,U_n\in GL_d(F)$ chosen before any selector bits. For a selector row $v_a\in\{0,1\}^n$, its block in column $i$ is (5.1)
--   $$v_{ai}\,U_1^{v_{a1}}\cdots U_{i-1}^{v_{a,i-1}}=v_{ai}P_{a,i-1},\qquad P_{a,i-1}=\prod_{h<i}U_h^{v_{ah}}.$$
--   For a selector array of $j$ rows the block map is $T_{j,n}:(F^d)^n\to(F^d)^j$, $(T_{j,n}x)_a=\sum_i v_{ai}P_{a,i-1}x_i$. Its **left kernel** $\mathcal W_j(n)=\ker T^*_{j,n}$ consists of the row covectors $\alpha=(\alpha_1,\dots,\alpha_j)$, $\alpha_a\in F^d$, with $\sum_a\alpha_a\,v_{ai}P_{a,i-1}=0$ for every column $i$. The **full-support event** $F^{\rm fs}_{j,d}(n)$ says that $\mathcal W_j(n)$ contains some $\alpha$ with every $\alpha_a\ne0$; the **nononto event** says that $T_{j,n}$ is not surjective. Probabilities are over independent fair selector bits: the uniform law on all raw $j\times n$ binary arrays, empty and repeated rows allowed.
--
--   For a maximum arity $T\ge3$ and a dimension bound $D$ the constants (5.2) are
--   $$L=\lceil\ln(T+2)\rceil,\ P=24L,\ \tau=4\lceil\log_2(T+2)\rceil+16,\ a=\tfrac{29}{64},\ b=\tfrac{31}{64},\ C_L=2^{99L}((3L)!)^2,$$
--   $$B(T,D)=3(TD)^PC_Le^{64T}b^{-\tau},\qquad A(T,D)=2T^2+2TB(T,D),$$
--   and the scalar envelopes (5.7) are $B_{\rm sc}(T)=(40/7)^{T-1}$, $A_{\rm sc}(T)=2T^2+2TB_{\rm sc}(T)$.
--
--   **Formalization Note.** The stream is `Fin n → Matrix.GeneralLinearGroup (Fin d) F`; selector arrays are `Fin j → Fin n → Bool`; covectors act by `Matrix.vecMul`. `probBits j n A` is the counting ratio over the $2^{jn}$ arrays. $L$ and $\tau$ are natural-number ceilings (`Nat.ceil`) of positive reals, and $b^{-\tau}$, $(40/7)^{T-1}$ are integer powers.
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 18 (PDF 19), §5, Eqs. (5.1)–(5.2); p. 19 (PDF 20), Eq. (5.7)

import Mathlib

namespace AlgCoverage.OddOrder

/-! Common-stream block matrices of §5 (Lin, printed p. 18 / PDF 19). A field `F`, a block dimension
`d`, a common stream `U₁, …, U_n ∈ GL_d(F)` fixed before the selector bits, and a selector array
`v : Fin j → Fin n → Bool` (`j` rows, each in `{0,1}^n`). -/

/-- The prefix product `P_{a,i−1} = ∏_{h<i} U_h^{v_{ah}}` of row `v_a`, multiplied in increasing `h`. -/
def streamPrefix {F : Type*} [Field F] {d n : ℕ} (U : Fin n → Matrix.GeneralLinearGroup (Fin d) F)
    (row : Fin n → Bool) (i : Fin n) : Matrix (Fin d) (Fin d) F :=
  (List.ofFn fun h : Fin n => if h < i ∧ row h = true then (U h : Matrix (Fin d) (Fin d) F) else 1).prod

/-- The block (5.1) of row `a` in column `i`: `v_{ai} U_1^{v_{a1}} ⋯ U_{i−1}^{v_{a,i−1}}`. -/
def streamBlock {F : Type*} [Field F] {d n : ℕ} (U : Fin n → Matrix.GeneralLinearGroup (Fin d) F)
    (row : Fin n → Bool) (i : Fin n) : Matrix (Fin d) (Fin d) F :=
  if row i = true then streamPrefix U row i else 0

/-- The block map `T_{j,n} : (F^d)^n → (F^d)^j`, `(T x)_a = ∑_{i} v_{ai} P_{a,i−1} x_i`. -/
def blockMap {F : Type*} [Field F] {d n j : ℕ} (U : Fin n → Matrix.GeneralLinearGroup (Fin d) F)
    (v : Fin j → Fin n → Bool) (x : Fin n → Fin d → F) : Fin j → Fin d → F :=
  fun a => ∑ i : Fin n, (streamBlock U (v a) i).mulVec (x i)

/-- The left kernel `W_j(n) = ker T*_{j,n}`: row covectors `α = (α₁, …, α_j)`, `α_a ∈ F^d`, with
`∑_a α_a · (block of row a in column i) = 0` for every column `i`. -/
def leftKernel {F : Type*} [Field F] {d n j : ℕ} (U : Fin n → Matrix.GeneralLinearGroup (Fin d) F)
    (v : Fin j → Fin n → Bool) : Set (Fin j → Fin d → F) :=
  {α | ∀ i : Fin n, ∑ a : Fin j, Matrix.vecMul (α a) (streamBlock U (v a) i) = 0}

/-- The full-support event `F^fs_{j,d}(n)`: the left kernel contains `(α₁, …, α_j)` with every
`α_a ≠ 0`. -/
def FullSupport {F : Type*} [Field F] {d n j : ℕ} (U : Fin n → Matrix.GeneralLinearGroup (Fin d) F)
    (v : Fin j → Fin n → Bool) : Prop :=
  ∃ α ∈ leftKernel U v, ∀ a : Fin j, α a ≠ 0

/-- The nononto event: `T_{j,n}` is not surjective. -/
def NotOnto {F : Type*} [Field F] {d n j : ℕ} (U : Fin n → Matrix.GeneralLinearGroup (Fin d) F)
    (v : Fin j → Fin n → Bool) : Prop :=
  ¬ Function.Surjective (blockMap U v)

/-- Probability over independent fair selector bits: the counting ratio `#{v : A v} / 2^{jn}` over all
raw `j × n` binary arrays (empty and repeated rows allowed). -/
noncomputable def probBits (j n : ℕ) (A : (Fin j → Fin n → Bool) → Prop) : ℝ :=
  (Nat.card {v : Fin j → Fin n → Bool // A v} : ℝ) / (2 : ℝ) ^ (j * n)

/-! The constants (5.2), for a maximum arity `T ≥ 3` and a dimension bound `D`. -/

/-- `L = ⌈ln(T + 2)⌉`. -/
noncomputable def constL (T : ℕ) : ℕ := ⌈Real.log ((T : ℝ) + 2)⌉₊

/-- `P = 24 L`. -/
noncomputable def constP (T : ℕ) : ℕ := 24 * constL T

/-- `τ = 4⌈log₂(T + 2)⌉ + 16`. -/
noncomputable def constTau (T : ℕ) : ℕ := 4 * ⌈Real.logb 2 ((T : ℝ) + 2)⌉₊ + 16

/-- `a = 29/64`. -/
noncomputable def constA_small : ℝ := 29 / 64

/-- `b = 31/64`. -/
noncomputable def constB_small : ℝ := 31 / 64

/-- `C_L = 2^{99L} ((3L)!)²`. -/
noncomputable def constCL (T : ℕ) : ℝ :=
  (2 : ℝ) ^ (99 * constL T) * ((Nat.factorial (3 * constL T) : ℕ) : ℝ) ^ 2

/-- `B(T, D) = 3 (TD)^P C_L e^{64T} b^{−τ}`. -/
noncomputable def envB (T D : ℕ) : ℝ :=
  3 * ((T : ℝ) * D) ^ constP T * constCL T * Real.exp (64 * T) * constB_small ^ (-(constTau T : ℤ))

/-- `A(T, D) = 2T² + 2T B(T, D)`. -/
noncomputable def envA (T D : ℕ) : ℝ :=
  2 * (T : ℝ) ^ 2 + 2 * T * envB T D

/-- The scalar envelope (5.7): `B_sc(T) = (40/7)^{T−1}`. -/
noncomputable def envBsc (T : ℕ) : ℝ := (40 / 7 : ℝ) ^ ((T : ℤ) - 1)

/-- The scalar envelope (5.7): `A_sc(T) = 2T² + 2T B_sc(T)`. -/
noncomputable def envAsc (T : ℕ) : ℝ := 2 * (T : ℝ) ^ 2 + 2 * T * envBsc T

end AlgCoverage.OddOrder


