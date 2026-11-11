-- Prove2me | Definitions.Def_QuantumXoP_Security_Compressed
-- name    : QuantumXoP_Security_Compressed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:31.846184+00:00
-- url     : https://prove2.me/theorems/1cc88d57-9374-4f77-937e-af4d7fb0cf64
-- title:
--   Compressed oracle, $|\hat v\rangle$, $\mathrm{Col}_{xy}$, $B$, and the counts $D_{\mathrm{cnt}}$, $\mathrm{Col}_{\mathrm{cnt}}$
-- statement:
--   The database has one register per input $x\in\{0,1\}^n$, with basis $\{|\bot\rangle\}\cup\{|v\rangle:v\in\{0,1\}^n\}$; a computational database basis state is $D\in(\{0,1\}^n\cup\{\bot\})^{\{0,1\}^n}$ and $|\emptyset\rangle=|\bot\rangle^{\otimes N}$. $\mathrm{Comp}$ swaps $|\bot\rangle$ and $|+\rangle=N^{-1/2}\sum_v|v\rangle$ and fixes their orthogonal complement.
--
--   1. $|\hat v\rangle=\mathrm{Comp}|v\rangle=|v\rangle-|+\rangle/\sqrt N+|\bot\rangle/\sqrt N$ and $|\hat f\rangle=\bigotimes_x|\widehat{f(x)}\rangle$.
--   2. The **compressed query** $O$ applies $\mathrm{Comp}$ to the register indexed by the query input, performs the usual query $|x,y\rangle|D\rangle\mapsto|x,y+D(x)\rangle|D\rangle$, and applies $\mathrm{Comp}$ again.
--   3. A compressed execution starts from $|\mathrm{start}\rangle\otimes|\emptyset\rangle$ and alternates operations on the algorithm registers with compressed queries.
--   4. $D_{\mathrm{cnt}}|D\rangle=|\{x:D(x)\ne\bot\}|\,|D\rangle$ and $\mathrm{Col}_{\mathrm{cnt}}|D\rangle=\sum_{x<y}[\![D(x)=D(y)\ne\bot]\!]\,|D\rangle$.
--   5. $\mathrm{Col}_{xy}=\sum_v(|\hat v\rangle\langle\hat v|)_x\otimes(|\hat v\rangle\langle\hat v|)_y$, $Q=I-|\bot\rangle\langle\bot|$, $B_x=|\bot\rangle\langle\bot|_x\sum_{y\ne x}Q_y\mathrm{Col}_{xy}$ and $B=\sum_x|x\rangle\langle x|\otimes B_x$, with $|x\rangle\langle x|$ on the query input register.
--
--   These operators carry the compressed-oracle proof of Lemma 7.2.
--
--   **Formalization Note** $\mathrm{Comp}$ is the published `compressionUnitary`. The usual query acts as the identity when $D(x)=\bot$; on states reached from $|\emptyset\rangle$ the queried register has no $|\bot\rangle$ component at that moment, so the convention is never used. Expectations of the diagonal operators are written as $\sum|\Xi(a,D)|^2\,c(D)$.
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), §7.1 pp. 36–37 (PDF pp. 38–39), Eq. (30); §7.2 p. 37 (PDF p. 39); §7.3 p. 38 (PDF p. 40)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_CompressedOracle
import Definitions.Def_QuantumXoP_Security_Fourier

noncomputable section

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-!
# The compressed oracle, collision operators and counts (Choi–Hhan–Jang, §7.1–7.3 pp. 36–39)

The database has one register for each input `x ∈ {0,1}^n`, with basis
`{|⊥⟩} ∪ {|v⟩ : v ∈ {0,1}^n}` (`Option (Qubits n)`, `none = ⊥`); a computational database basis
state is `D ∈ ({0,1}^n ∪ {⊥})^{{0,1}^n}` (`DB n`). The algorithm registers are the query input,
the query answer and an arbitrary finite workspace `W` (`Reg n W`). `Comp` is the published
`QAlgorithms.compressionUnitary n`: it swaps `|⊥⟩` and `|+⟩ = N^{−1/2} Σ_v |v⟩` and fixes their
orthogonal complement.
-/

/-- §7.2 (p. 37): the computational database basis `({0,1}^n ∪ {⊥})^{{0,1}^n}`. -/
abbrev DB (n : ℕ) := Qubits n → Option (Qubits n)

/-- The algorithm registers: query input `x`, query answer `y`, workspace `W`. -/
abbrev Reg (n : ℕ) (W : Type*) := (Qubits n × Qubits n) × W

/-- §7.1 (p. 36): `|v^⟩ := Comp |v⟩ = |v⟩ − |+⟩/√N + |⊥⟩/√N`, as a vector of one database
register. -/
def vhat (n : ℕ) (v : Qubits n) : Option (Qubits n) → ℂ :=
  fun o => compressionUnitary n o (some v)

/-- The operator `A` acting on database register `x` (identity on the other registers). -/
def onReg {n : ℕ} (x : Qubits n) (A : Matrix (Option (Qubits n)) (Option (Qubits n)) ℂ) :
    Matrix (DB n) (DB n) ℂ :=
  Matrix.of fun D D' => A (D x) (D' x) * if (∀ z, z ≠ x → D z = D' z) then 1 else 0

/-- §7.1 (p. 36): `Comp` applied to the database register indexed by the query input. -/
def compAtQuery (n : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (Reg n W × DB n) (Reg n W × DB n) ℂ :=
  Matrix.of fun p p' => if p.1 = p'.1 then onReg p.1.1.1 (compressionUnitary n) p.2 p'.2 else 0

/-- §7.1 (p. 36): the usual query `|x, y⟩|D⟩ ↦ |x, y + D(x)⟩|D⟩` on the database, the identity when
`D(x) = ⊥` (as in the published `QAlgorithms.lookupUnitary`; on the states reached from `|∅⟩`
the register `x` holds no `|⊥⟩` component at this point, so this convention is never used). -/
def dbLookup (n : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (Reg n W × DB n) (Reg n W × DB n) ℂ :=
  Matrix.of fun p p' =>
    if p.1.1.1 = p'.1.1.1 ∧ p.1.2 = p'.1.2 ∧ p.2 = p'.2 ∧
        p.1.1.2 = (match p'.2 p'.1.1.1 with
          | some v => p'.1.1.2 + v
          | none => p'.1.1.2)
    then 1 else 0

/-- §7.1 (p. 36): the compressed query `O`: apply `Comp` to the database register indexed by the
query input, perform the usual query, and apply `Comp` again. -/
def compQuery (n : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (Reg n W × DB n) (Reg n W × DB n) ℂ :=
  compAtQuery n W * dbLookup n W * compAtQuery n W

/-- `V` is a contraction: `‖V ψ‖ ≤ ‖ψ‖` for every vector (unitaries and orthogonal projections are
contractions). -/
def IsContraction {ι : Type*} [Fintype ι] (V : Matrix ι ι ℂ) : Prop :=
  ∀ ψ : EuclideanSpace ℂ ι, ‖act V ψ‖ ≤ ‖ψ‖

/-- §7.2 (p. 37, Lemma 7.4) and App. C (p. 46): the joint algorithm–database state after an
algorithm that starts from `|start⟩ ⊗ |∅⟩` (`|∅⟩ = |⊥⟩^{⊗N}`), applies the operations
`V_0, …, V_t` on its own registers and makes one compressed query between consecutive operations:
`(V_t ⊗ I) O (V_{t−1} ⊗ I) ⋯ O (V_0 ⊗ I) (|start⟩ ⊗ |∅⟩)`. -/
def compExec {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (start : EuclideanSpace ℂ (Reg n W)) (V : Fin (t + 1) → Matrix (Reg n W) (Reg n W) ℂ) :
    EuclideanSpace ℂ (Reg n W × DB n) :=
  (Fin.induction (motive := fun _ => EuclideanSpace ℂ (Reg n W × DB n))
    (act (Matrix.kronecker (V 0) (1 : Matrix (DB n) (DB n) ℂ)) (tensorVec start (ket fun _ => none)))
    (fun i ψ => act (Matrix.kronecker (V i.succ) (1 : Matrix (DB n) (DB n) ℂ))
      (act (compQuery n W) ψ))) (Fin.last t)

/-- §7.2 (p. 37): the eigenvalue of `D_cnt` on `|D⟩`: `|{x : D(x) ≠ ⊥}|`. -/
def dcnt {n : ℕ} (D : DB n) : ℕ :=
  (Finset.univ.filter fun x => D x ≠ none).card

/-- §7.2 (p. 37): the eigenvalue of `Col_cnt` on `|D⟩`: `Σ_{x<y} ⟦D(x) = D(y) ≠ ⊥⟧`, the number of
unordered pairs `{x, y}` of distinct inputs with `D(x) = D(y) ≠ ⊥`. -/
def colcnt {n : ℕ} (D : DB n) : ℕ :=
  (((Finset.univ : Finset (Qubits n)).powersetCard 2).filter
    fun s => ∃ v : Qubits n, ∀ x ∈ s, D x = some v).card

/-- The expectation `⟨Ξ| (I ⊗ K) |Ξ⟩` of a database operator `K` that is diagonal in the
computational database basis with eigenvalue `c(D)` on `|D⟩` (used for `D_cnt` and `Col_cnt`). -/
def expectDiag {n : ℕ} {α : Type*} [Fintype α] (Ξ : EuclideanSpace ℂ (α × DB n))
    (c : DB n → ℕ) : ℝ :=
  ∑ p : α × DB n, ‖Ξ p‖ ^ 2 * (c p.2 : ℝ)

/-- `|v^⟩⟨v^|` on one database register. -/
def projHat (n : ℕ) (v : Qubits n) : Matrix (Option (Qubits n)) (Option (Qubits n)) ℂ :=
  Matrix.of fun o o' => vhat n v o * conj (vhat n v o')

/-- `|⊥⟩⟨⊥|` on one database register. -/
def projBot (n : ℕ) : Matrix (Option (Qubits n)) (Option (Qubits n)) ℂ :=
  Matrix.of fun o o' => if o = none ∧ o' = none then 1 else 0

/-- §7.3 (p. 37): `Q := I − |⊥⟩⟨⊥|` on one database register. -/
def qOp (n : ℕ) : Matrix (Option (Qubits n)) (Option (Qubits n)) ℂ :=
  1 - projBot n

/-- §7.1, Eq. (30) (p. 36): `Col_xy = Σ_v (|v^⟩⟨v^|)_x ⊗ (|v^⟩⟨v^|)_y` (for `x ≠ y`). -/
def colOp {n : ℕ} (x y : Qubits n) : Matrix (DB n) (DB n) ℂ :=
  ∑ v : Qubits n, onReg x (projHat n v) * onReg y (projHat n v)

/-- §7.3 (p. 38): `B_x = |⊥⟩⟨⊥|_x Σ_{y ≠ x} Q_y Col_xy`. -/
def bAt {n : ℕ} (x : Qubits n) : Matrix (DB n) (DB n) ℂ :=
  onReg x (projBot n) * ∑ y ∈ Finset.univ.filter (fun y => y ≠ x), onReg y (qOp n) * colOp x y

/-- §7.3 (p. 38): `B = Σ_x |x⟩⟨x| ⊗ B_x`, where the first register is the query input register
(identity on the query answer and the workspace). -/
def bOp (n : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (Reg n W × DB n) (Reg n W × DB n) ℂ :=
  Matrix.of fun p p' => if p.1 = p'.1 then bAt p.1.1.1 p.2 p'.2 else 0

/-- §7.1 (p. 36): `|f^⟩ = ⊗_x |f(x)^⟩`, as a database vector. -/
def fhat {n : ℕ} (f : Fn n) : DB n → ℂ :=
  fun D => ∏ x : Qubits n, vhat n (f x) (D x)

/-- §7.3, Eq. (36) (p. 39): the database registers of the joint state `Ξ` are supported on
`span{|f^⟩ : f ∈ F}`, i.e. `Ξ = Σ_f |φ_f⟩ ⊗ |f^⟩` for some algorithm-register vectors `φ_f`. -/
def InFhatSpan {n : ℕ} {α : Type*} (Ξ : EuclideanSpace ℂ (α × DB n)) : Prop :=
  ∃ φ : Fn n → α → ℂ, ∀ p : α × DB n, Ξ p = ∑ f : Fn n, φ f p.1 * fhat f p.2

/-! ### Sanity checks -/

example {n : ℕ} : dcnt (fun _ : Qubits n => (none : Option (Qubits n))) = 0 := by
  simp [dcnt]

example {n : ℕ} : colcnt (fun _ : Qubits n => (none : Option (Qubits n))) = 0 := by
  simp only [colcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s hs ⟨v, hv⟩
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hs).2]; norm_num)
  simpa using hv x hx

/-- `⟨⊥|v^⟩ = 1/√N`. -/
example (n : ℕ) (v : Qubits n) : vhat n v none = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := rfl

end QuantumXoP.Security


