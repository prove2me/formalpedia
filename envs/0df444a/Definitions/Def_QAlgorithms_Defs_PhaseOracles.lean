-- Prove2me | Definitions.Def_QAlgorithms_Defs_PhaseOracles
-- name    : QAlgorithms_Defs_PhaseOracles
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:29.576835+00:00
-- url     : https://prove2.me/theorems/560e7604-fc1d-48bb-84ca-d319898fcd34
-- title:
--   Euclidean norms, Fourier phase states, phase / probability / fractional oracles, oracle
-- statement:
--   # Euclidean norms, Fourier phase states, phase / probability / fractional oracles, oracle
--   circuits with adjoint, controlled and fractional queries, directional derivatives
--   (shared definition layer)
--
--   * A. Gilyén, S. Arunachalam, N. Wiebe, *Optimizing quantum optimization algorithms via faster
--     quantum gradient computation* (arXiv:1711.00465v3), cited "GAW p.N" (PDF pages), §§2–5.
--   * G. Brassard, P. Høyer, M. Mosca, A. Tapp, *Quantum amplitude amplification and estimation*
--     (arXiv:quant-ph/0005055v1), cited "BHMT p.N", Definition 8.
--   * Y. T. Lee, A. Sidford, S. C. Wong, *A faster cutting plane method* (arXiv:1508.04874v2), cited
--     "LSW p.N", for the Euclidean norm of Definition 2.
--
--   GAW's oracles act on `H ⊗ H_aux`, `H` with orthonormal basis `{|x⟩ : x ∈ X}` (`X` any finite set),
--   `H_aux` an auxiliary qubit register whose all-zero state is `fun _ => false`.
--   -/
--
--   namespace QAlgorithms
--
--   /-- The Euclidean norm `‖x‖₂ = (Σ_i x_i²)^{1/2}` of a real vector (GAW p.11; LSW p.9, Definitions
--   1–2). Mathlib's default norm on `Fin n → ℝ` is the sup norm, hence this separate definition.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\PhaseOracles.lean

import Definitions.Def_QAlgorithms_Defs_CircuitResources
/-!
# Euclidean norms, Fourier phase states, phase / probability / fractional oracles, oracle
circuits with adjoint, controlled and fractional queries, directional derivatives
(shared definition layer)

* A. Gilyén, S. Arunachalam, N. Wiebe, *Optimizing quantum optimization algorithms via faster
  quantum gradient computation* (arXiv:1711.00465v3), cited "GAW p.N" (PDF pages), §§2–5.
* G. Brassard, P. Høyer, M. Mosca, A. Tapp, *Quantum amplitude amplification and estimation*
  (arXiv:quant-ph/0005055v1), cited "BHMT p.N", Definition 8.
* Y. T. Lee, A. Sidford, S. C. Wong, *A faster cutting plane method* (arXiv:1508.04874v2), cited
  "LSW p.N", for the Euclidean norm of Definition 2.

GAW's oracles act on `H ⊗ H_aux`, `H` with orthonormal basis `{|x⟩ : x ∈ X}` (`X` any finite set),
`H_aux` an auxiliary qubit register whose all-zero state is `fun _ => false`.
-/

namespace QAlgorithms

/-- The Euclidean norm `‖x‖₂ = (Σ_i x_i²)^{1/2}` of a real vector (GAW p.11; LSW p.9, Definitions
1–2). Mathlib's default norm on `Fin n → ℝ` is the sup norm, hence this separate definition. -/
noncomputable def euclidNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- BHMT Definition 8 (p.16): `|S_M(ω)⟩ = M^{−1/2} Σ_{y=0}^{M−1} e^{2πiωy} |y⟩` on `Fin M`
(sign `+`, normalization `1/√M`; the source's `M > 0` and `0 ≤ ω < 1` are hypotheses of the
statements). With the frozen `qftMatrix`, `F_M |x⟩ = |S_M(x/M)⟩` (sanity test below). -/
noncomputable def bhmtPhaseState (M : ℕ) (ω : ℝ) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 fun y =>
    Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ) * ((y : ℕ) : ℂ)) / (Real.sqrt M : ℂ)

/-- GAW Definition 10 (p.17): `O` is a phase oracle for `f`, i.e. `O` is unitary and
`O |x⟩|0⟩ = e^{i f(x)} |x⟩|0⟩` for every `x ∈ X`, `w0` the auxiliary all-zero state. Its action
off `|0⟩_aux` is unconstrained. The source's range `f : X → [−1, 1]` is a hypothesis of the
statements. -/
def IsGAWPhaseOracle {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    (w0 : W) (O : Matrix (X × W) (X × W) ℂ) (f : X → ℝ) : Prop :=
  O ∈ Matrix.unitaryGroup (X × W) ℂ ∧
    ∀ x, act O (ket (x, w0)) = Complex.exp (Complex.I * (f x : ℂ)) • ket (x, w0)

/-- GAW Definition 11 (p.17): a family of fractional query phase oracles `O^r_f`,
`r ∈ [−1, 1]`, with `O^r |x⟩|0⟩ = e^{i r f(x)} |x⟩|0⟩`. -/
def IsGAWFractionalOracle {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    (w0 : W) (O : Set.Icc (-1 : ℝ) 1 → Matrix (X × W) (X × W) ℂ) (f : X → ℝ) : Prop :=
  ∀ r : Set.Icc (-1 : ℝ) 1, IsGAWPhaseOracle w0 (O r) (fun x => (r : ℝ) * f x)

/-- The vector `φ ⊗ |b⟩` with the qubit `|b⟩` **last** (GAW Definition 8 and eq. (9), pp.16–17:
the flag is the last auxiliary qubit). -/
noncomputable def snocQubit {m : ℕ} (φ : EuclideanSpace ℂ (Qubits m)) (b : Bool) :
    EuclideanSpace ℂ (Qubits (m + 1)) :=
  WithLp.toLp 2 fun z => if z (Fin.last m) = b then φ (Fin.init z) else 0

/-- GAW Definition 8 (p.16): `U` is a probability oracle for `p : X → [0, 1]` with the
`(m + 1)`-qubit auxiliary register: `U` is unitary and
`U |x⟩|0⟩ = |x⟩ ⊗ (√p(x) |ψ_good(x)⟩|1⟩ + √(1 − p(x)) |ψ_bad(x)⟩|0⟩)` for normalized
`ψ_good(x), ψ_bad(x)`, flag last. -/
def IsGAWProbabilityOracle {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (U : Matrix (X × Qubits (m + 1)) (X × Qubits (m + 1)) ℂ) (p : X → ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (X × Qubits (m + 1)) ℂ ∧ (∀ x, 0 ≤ p x ∧ p x ≤ 1) ∧
    ∀ x, ∃ ψg ψb : EuclideanSpace ℂ (Qubits m), ‖ψg‖ = 1 ∧ ‖ψb‖ = 1 ∧
      act U (ket (x, fun _ => false)) =
        tensorVec (ket x) ((Real.sqrt (p x) : ℂ) • snocQubit ψg true +
          (Real.sqrt (1 - p x) : ℂ) • snocQubit ψb false)

/-- An oracle `M` on `X × Qubits w` lifted to `X × Qubits (w + a)` (GAW Theorem 14, p.18, and
Lemma 16, p.21, use extra auxiliary qubits and controlled queries): `M` acts on `X` and the first
`w` auxiliary qubits, the identity on the last `a`; with `control = some c`, `M` is applied only
when extra qubit `c` is `1`. -/
def liftAuxOracle {X : Type*} [DecidableEq X] {w : ℕ} (M : Matrix (X × Qubits w) (X × Qubits w) ℂ)
    (a : ℕ) (control : Option (Fin a)) : Matrix (X × Qubits (w + a)) (X × Qubits (w + a)) ℂ :=
  Matrix.of fun p q =>
    if (qubitsAppendEquiv w a p.2).2 = (qubitsAppendEquiv w a q.2).2 then
      match control with
      | none => M (p.1, (qubitsAppendEquiv w a p.2).1) (q.1, (qubitsAppendEquiv w a q.2).1)
      | some c =>
          if (qubitsAppendEquiv w a q.2).2 c = true then
            M (p.1, (qubitsAppendEquiv w a p.2).1) (q.1, (qubitsAppendEquiv w a q.2).1)
          else if p.1 = q.1 ∧ (qubitsAppendEquiv w a p.2).1 = (qubitsAppendEquiv w a q.2).1 then 1
          else 0
    else 0

/-- One step of a GAW oracle algorithm (Theorem 14, p.18; Lemma 16, p.21; Theorem 23, p.28) on
`X × Qubits (w + a)`, for an oracle family `O : R → Matrix (X × Qubits w) (X × Qubits w) ℂ`
(`R = Unit` for one oracle, `R = Set.Icc (-1) 1` for fractional queries): an oracle-independent
unitary, or one query `O r` (possibly its adjoint, possibly controlled by extra qubit `c`). -/
inductive PhaseQueryStep (X : Type*) [Fintype X] [DecidableEq X] (R : Type*) (w a : ℕ) where
  | unitary (U : Matrix.unitaryGroup (X × Qubits (w + a)) ℂ)
  | query (r : R) (adjoint : Bool) (control : Option (Fin a))

/-- A GAW oracle algorithm: a list of steps applied head first (GAW Theorem 14, p.18). The steps
are data fixed before the oracle (trap Q2). -/
abbrev PhaseQueryCircuit (X : Type*) [Fintype X] [DecidableEq X] (R : Type*) (w a : ℕ) :=
  List (PhaseQueryStep X R w a)

/-- The matrix of one step for the oracle family `O` (GAW Theorem 14, p.18). -/
def PhaseQueryStep.mat {X : Type*} [Fintype X] [DecidableEq X] {R : Type*} {w a : ℕ}
    (O : R → Matrix (X × Qubits w) (X × Qubits w) ℂ) :
    PhaseQueryStep X R w a → Matrix (X × Qubits (w + a)) (X × Qubits (w + a)) ℂ
  | .unitary U => (U : Matrix _ _ ℂ)
  | .query r adj ctl => liftAuxOracle (if adj then star (O r) else O r) a ctl

/-- The overall matrix of a GAW oracle algorithm, first step rightmost (GAW Theorem 14, p.18). -/
def PhaseQueryCircuit.unitary {X : Type*} [Fintype X] [DecidableEq X] {R : Type*} {w a : ℕ}
    (c : PhaseQueryCircuit X R w a) (O : R → Matrix (X × Qubits w) (X × Qubits w) ℂ) :
    Matrix (X × Qubits (w + a)) (X × Qubits (w + a)) ℂ :=
  (c.map (PhaseQueryStep.mat O)).reverse.prod

/-- The number of oracle applications (each `O^r` or `(O^r)†`, controlled or not, counts one:
GAW Theorem 14, p.18, and eq. (25), p.30). -/
def PhaseQueryCircuit.queryCount {X : Type*} [Fintype X] [DecidableEq X] {R : Type*} {w a : ℕ}
    (c : PhaseQueryCircuit X R w a) : ℕ :=
  c.countP fun s => match s with
    | .query _ _ _ => true
    | .unitary _ => false

/-- GAW Definition 6 (p.12): the `k`-th directional derivative `∂_r^k f(x) = d^k/dτ^k f(x + τr)`
at `τ = 0`, taken within the parameters `τ` with `x + τr ∈ K` (`K = Set.univ` gives the source's
plain derivative; `K` a box covers its boundary points). -/
noncomputable def rayDeriv {d : ℕ} (k : ℕ) (f : (Fin d → ℝ) → ℝ) (K : Set (Fin d → ℝ))
    (x r : Fin d → ℝ) : ℝ :=
  iteratedDerivWithin k (fun τ : ℝ => f (x + τ • r)) {τ | x + τ • r ∈ K} 0

/-! ### Sanity tests -/

example : euclidNorm (![3, 4] : Fin 2 → ℝ) = 5 := by
  rw [euclidNorm, show (∑ i, (![3, 4] : Fin 2 → ℝ) i ^ 2) = 5 ^ 2 by simp [Fin.sum_univ_two]; norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem qftMatrix_eq_bhmtPhaseState (M : ℕ) (x y : Fin M) :
    qftMatrix M y x = bhmtPhaseState M ((x : ℕ) / (M : ℝ)) y := by
  simp only [qftMatrix, bhmtPhaseState, Matrix.of_apply]
  congr 2
  push_cast
  ring

example {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] (w0 : W) :
    IsGAWPhaseOracle w0 (1 : Matrix (X × W) (X × W) ℂ) (fun _ => 0) :=
  ⟨one_mem _, fun x => by simp [act]⟩

example {X : Type*} [DecidableEq X] {w : ℕ} (a : ℕ) :
    liftAuxOracle (1 : Matrix (X × Qubits w) (X × Qubits w) ℂ) a none = 1 := by
  ext p q
  rcases p with ⟨x, y⟩; rcases q with ⟨x', y'⟩
  simp only [liftAuxOracle, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
  by_cases hx : x = x' <;> by_cases hy : y = y'
  · subst hx; subst hy; simp
  · have : ¬ ((qubitsAppendEquiv w a y).1 = (qubitsAppendEquiv w a y').1 ∧
        (qubitsAppendEquiv w a y).2 = (qubitsAppendEquiv w a y').2) := fun h =>
      hy ((qubitsAppendEquiv w a).injective (Prod.ext h.1 h.2))
    by_cases h2 : (qubitsAppendEquiv w a y).2 = (qubitsAppendEquiv w a y').2
    · simp [hy, h2, show ¬ (qubitsAppendEquiv w a y).1 = (qubitsAppendEquiv w a y').1 from
        fun h1 => this ⟨h1, h2⟩]
    · simp [hy, h2]
  · simp [hx]
  · simp [hx, hy]

example {X : Type*} [Fintype X] [DecidableEq X] {w a : ℕ}
    (O : Unit → Matrix (X × Qubits w) (X × Qubits w) ℂ) :
    PhaseQueryCircuit.unitary ([] : PhaseQueryCircuit X Unit w a) O = 1 := rfl

example {X : Type*} [Fintype X] [DecidableEq X] {w a : ℕ}
    (U : Matrix.unitaryGroup (X × Qubits (w + a)) ℂ) :
    PhaseQueryCircuit.queryCount ([.unitary U, .query () false none] :
      PhaseQueryCircuit X Unit w a) = 1 := rfl

example {d : ℕ} (f : (Fin d → ℝ) → ℝ) (K : Set (Fin d → ℝ)) (x r : Fin d → ℝ) :
    rayDeriv 0 f K x r = f x := by
  simp [rayDeriv]

end QAlgorithms


