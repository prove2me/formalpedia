-- Prove2me | Definitions.Def_CliffordTApprox_Ancilla_Setting
-- name    : CliffordTApprox_Ancilla_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:56.079886+00:00
-- url     : https://prove2.me/theorems/951cc518-306a-42ea-87a7-c0a0062c577c
-- title:
--   §2–§2.2, pp. 2–3 — the phase gate Λ(e^{iφ}), the rounding γ, the four-square vector |v⟩ and controlled preparation
-- statement:
--   This file fixes the objects of the single-qubit approximation algorithm of Kliuchnikov, Maslov and Mosca.
--
--   **Registers.** A register of $n$ qubits has computational basis indexed by bit strings $z \in \{0,1\}^n$. The circuits of the paper act on three qubits: the data qubit (wire $0$) and two ancillas (wires $1$ and $2$), so a basis state is written $|x\rangle \otimes |y_1 y_2\rangle$ with $x$ the data bit.
--
--   **The phase gate.** For $\varphi \in \mathbb R$, the gate $\Lambda(e^{i\varphi})$ acts on one qubit by
--   $$\Lambda(e^{i\varphi}) : \alpha|0\rangle + \beta|1\rangle \mapsto \alpha|0\rangle + \beta e^{i\varphi}|1\rangle,$$
--   i.e. it is the matrix $\mathrm{diag}(1, e^{i\varphi})$. The map $M \mapsto M_1$ reads a $2\times 2$ matrix indexed by $\{0,1\}$ as an operator on a one-qubit register.
--
--   **Roundings.** For $k \in \mathbb N$ and $\varphi \in \mathbb R$ put $x_k(\varphi) = \lfloor 2^k\cos\varphi\rfloor$ and $y_k(\varphi) = \lfloor 2^k\sin\varphi\rfloor$ (integer floors), and
--   $$\gamma = \frac{\lfloor 2^k\cos\varphi\rfloor + i\lfloor 2^k\sin\varphi\rfloor}{2^k}, \qquad D_k(\varphi) = 4^k - \lfloor 2^k\cos\varphi\rfloor^2 - \lfloor 2^k\sin\varphi\rfloor^2 .$$
--   The integer $D_k(\varphi)$ is the right-hand side of the four-square equation $a^2+b^2+c^2+d^2 = D_k(\varphi)$.
--
--   **The vector $|v\rangle$.** For integers $a, b, c, d$, the two-qubit vector
--   $$|v\rangle = \frac{1}{2^k}\big(\lfloor 2^k\cos\varphi\rfloor + i\lfloor 2^k\sin\varphi\rfloor,\ 0,\ a+ib,\ c+id\big)$$
--   in the basis $|00\rangle, |01\rangle, |10\rangle, |11\rangle$ of the two ancillas; thus $|v\rangle = \gamma|00\rangle + |1\rangle\otimes|g\rangle$ with $|g\rangle = \big((a+ib)|0\rangle + (c+id)|1\rangle\big)/2^k$.
--
--   **Controlled preparation.** For a two-qubit vector $v$, the vector $|x\rangle\otimes v$ places the data bit $x$ on wire $0$ and $v$ on the ancilla wires. A $3$-qubit operator $W$ is a *controlled preparation of $v$* if
--   $$W\,|0\rangle|w\rangle = |0\rangle|w\rangle\quad\text{for every two-qubit }|w\rangle,\qquad W\,|1\rangle|00\rangle = |1\rangle|v\rangle .$$
--   Thus $W$ fixes the entire data-$0$ branch, as a circuit controlled on the data qubit does, and prepares $v$ from the initialized ancillas on the data-$1$ branch.
--
--   These definitions carry every milestone of the mission; the goal theorem uses the published circuit layer only.
--
--   **Formalization Note.** Registers are `Qubits n = Fin n → Bool` with `false` = $|0\rangle$. The ancilla register `Qubits 2` has index $0$ for the first ancilla (wire 1). $\Lambda(e^{i\varphi})$ is an exact complex matrix, with no quotient by the global phase. Floors are `Int.floor`, which rounds toward $-\infty$; for $0\le\varphi\le\pi/4$ both floors are nonnegative, which is why the theorems carry that hypothesis. The error of a 3-qubit operator $W$ against a one-qubit $U$ is measured elsewhere through the published `initializedMap W` (the map $\psi \mapsto W(\psi\otimes|00\rangle)$) and `idealMap U 2` (the map $\psi\mapsto (U\psi)\otimes|00\rangle$).
-- source:
--   Kliuchnikov, Maslov, Mosca, Asymptotically optimal approximation of single qubit unitaries by Clifford and T circuits using a constant number of ancillary qubits, arXiv:1212.0822v2, pp. 2–3, §2 (Λ(e^{iφ}), the two-step algorithm), §2.1 (|v⟩ and the four-square equation), §2.2 (γ, |v⟩ = γ|00⟩ + |1⟩ ⊗ |g⟩)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12

namespace CliffordTApprox.Ancilla

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

/-!
Kliuchnikov, Maslov, Mosca, arXiv:1212.0822v2, §2–§2.2, pp. 2–3.

Register conventions: a register of `n` qubits is `Qubits n = Fin n → Bool` (`false` = `|0⟩`).
The data qubit is wire `0`; the two ancillas are the trailing wires `1, 2` of `Qubits (1 + 2)`,
matching `|data⟩ ⊗ |00⟩` and the `Fin.append` convention of `initializedMap` / `idealMap`.
On the ancilla register `Qubits 2`, index `0` is the first ancilla (wire 1), index `1` the second.
-/

/-- A `Bool`-indexed one-qubit matrix as a matrix on `Qubits 1`; this is `(Gate.ofMatrix1 M).mat`. -/
def oneQubit (M : Matrix Bool Bool ℂ) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  M.submatrix (fun b => b 0) (fun b => b 0)

/-- §2, p. 2: the phase gate `Λ(e^{iφ}) : α|0⟩ + β|1⟩ ↦ α|0⟩ + β e^{iφ}|1⟩`, i.e. `diag(1, e^{iφ})`,
as an exact complex matrix (no phase quotient). -/
noncomputable def phaseGate (φ : ℝ) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  oneQubit (Matrix.diagonal fun a => if a then Complex.exp (φ * Complex.I) else 1)

/-- §2.1, p. 3: the rounding `⌊2^k cos φ⌋`. -/
noncomputable def roundX (k : ℕ) (φ : ℝ) : ℤ := ⌊(2 : ℝ) ^ k * Real.cos φ⌋

/-- §2.1, p. 3: the rounding `⌊2^k sin φ⌋`. -/
noncomputable def roundY (k : ℕ) (φ : ℝ) : ℤ := ⌊(2 : ℝ) ^ k * Real.sin φ⌋

/-- §2.2, p. 3: `γ = (⌊2^k cos φ⌋ + i ⌊2^k sin φ⌋) / 2^k`. -/
noncomputable def gammaApprox (k : ℕ) (φ : ℝ) : ℂ :=
  ((roundX k φ : ℂ) + (roundY k φ : ℂ) * Complex.I) / (2 : ℂ) ^ k

/-- §2.1, p. 3: the right-hand side `4^k − ⌊2^k cos φ⌋² − ⌊2^k sin φ⌋²` of the four-square
equation. -/
noncomputable def deficit (k : ℕ) (φ : ℝ) : ℤ := 4 ^ k - roundX k φ ^ 2 - roundY k φ ^ 2

/-- §2.1, p. 3: the vector
`|v⟩ = (1/2^k) (⌊2^k cos φ⌋ + i⌊2^k sin φ⌋, 0, a + ib, c + id)` in the basis
`|00⟩, |01⟩, |10⟩, |11⟩` of the two ancillas (index `0` of `Qubits 2` is the first ancilla). -/
noncomputable def vecV (k : ℕ) (φ : ℝ) (a b c d : ℤ) : EuclideanSpace ℂ (Qubits 2) :=
  WithLp.toLp 2 fun z =>
    if z 0 then
      (if z 1 then ((c : ℂ) + (d : ℂ) * Complex.I) / (2 : ℂ) ^ k
       else ((a : ℂ) + (b : ℂ) * Complex.I) / (2 : ℂ) ^ k)
    else (if z 1 then 0 else gammaApprox k φ)

/-- The vector `|x⟩ ⊗ v` on `Qubits (1 + 2)`: the data bit `x` on wire `0`, the ancilla vector `v`
on wires `1, 2`. -/
noncomputable def dataTensor (x : Bool) (v : EuclideanSpace ℂ (Qubits 2)) :
    EuclideanSpace ℂ (Qubits (1 + 2)) :=
  WithLp.toLp 2 fun z =>
    if (qubitsAppendEquiv 1 2 z).1 0 = x then v (qubitsAppendEquiv 1 2 z).2 else 0

/-- §2, p. 2, step 2: `W` prepares `v` controlled on the data qubit (wire `0`).
It fixes every input in the data-`0` branch, and maps `|1⟩|00⟩` to `|1⟩|v⟩`.
For a unitary `W`, fixing the entire data-`0` branch also preserves its orthogonal
data-`1` branch, as a controlled circuit does. -/
def PreparesControlled (W : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ)
    (v : EuclideanSpace ℂ (Qubits 2)) : Prop :=
  (∀ w : EuclideanSpace ℂ (Qubits 2), act W (dataTensor false w) = dataTensor false w) ∧
  act W (dataTensor true (ket fun _ => false)) = dataTensor true v

/-! Definitional sanity checks. -/

example : phaseGate 0 = 1 := by
  ext x y
  simp only [phaseGate, oneQubit, Matrix.submatrix_apply, Matrix.diagonal_apply,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, ite_self, Matrix.one_apply]
  have h : (x 0 = y 0) ↔ x = y :=
    ⟨fun h => funext fun i => by fin_cases i; exact h, fun h => congrFun h 0⟩
  simp only [h]

example (k : ℕ) (φ : ℝ) : (vecV k φ 0 0 0 0) (fun _ => false) = gammaApprox k φ := rfl

end CliffordTApprox.Ancilla


