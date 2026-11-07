-- Prove2me | Definitions.Def_F3SubsetSum_QutritCircuit
-- name    : F3SubsetSum_QutritCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:38.593193+00:00
-- url     : https://prove2.me/theorems/42ba174d-6409-43b7-b183-9d48ecff03a4
-- title:
--   Qutrit circuits over the gate set $G_3$, their code, and the success probability on Problem 1.1
-- statement:
--   Let $\omega=e^{2\pi i/3}$. A **qutrit circuit** on $W$ wires is a list of gates from the finite gate set $G_3$, each acting on one, two or three distinct wires:
--
--   1. $X:|a\rangle\mapsto|a+1\rangle$; $\mathrm{CSUM}:|a,b\rangle\mapsto|a,b+a\rangle$; $\mathrm{CCMUL}:|a,b,c\rangle\mapsto|a,b,c+ab\rangle$ (arithmetic in $\mathbb F_3$);
--   2. $F|a\rangle=3^{-1/2}\sum_b\omega^{ab}|b\rangle$;
--   3. $P|0\rangle=(|1\rangle-|2\rangle)/\sqrt2$, $P|1\rangle=|0\rangle$, $P|2\rangle=(|1\rangle+|2\rangle)/\sqrt2$;
--   4. $U|0\rangle=3^{-1/2}(|0\rangle+|1\rangle+|2\rangle)$, $U|1\rangle=\tfrac{\sqrt2}{3}\sum_a\omega^{-a}|\mathrm{not}\,a\rangle$, $U|2\rangle=\tfrac{\sqrt2}{3}\sum_a\omega^{a}|\mathrm{not}\,a\rangle$, where $|\mathrm{not}\,a\rangle=(|a+1\rangle-|a-1\rangle)/\sqrt2$;
--
--   and the inverse (conjugate transpose) of each. The gate $U$ maps the trine states $|\tau_a\rangle=(\omega^a|1\rangle+\omega^{-a}|2\rangle)/\sqrt2$ of §3 to $|\mathrm{not}\,a\rangle$.
--
--   On an instance $h=(h_1,\dots,h_m)\in(\mathbb F_3^n)^m$ the circuit starts in the basis state with wire $n i+j$ holding $(h_{i+1})_{j+1}$ ($0\le i<m$, $0\le j<n$) and every other wire $0$; at the end every wire is measured in the computational basis, and the output is $S=\{i\in[m]: \text{wire } nm+i-1 \text{ reads } \neq 0\}$. The **success probability** is
--
--   $$
--   \mathrm{succ}(C)=\frac{1}{3^{nm}}\sum_{h}\ \sum_{y}\ \bigl|\langle y|C|h,0\rangle\bigr|^2\,\mathbf 1\bigl[S(y)\neq\emptyset,\ \textstyle\sum_{i\in S(y)}h_i=0\bigr].
--   $$
--
--   A circuit is written for a machine as its wire count $1^W0$ followed by each gate as a 4-bit tag and its wire indices $1^w0$; this code is injective.
--
--   **Formalization Note** The paper names no gate set. $G_3$ is a fixed finite qutrit gate set with no parameters; it computes every function $\mathbb F_3^k\to\mathbb F_3$ reversibly and contains the amplitudes $3^{-1/2}$, $2^{-1/2}$, $\omega$ that the exact bound of Theorem 3.1 uses (the paper: $U$ "is efficient to apply to each qutrit", p.14).
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, §3, pp.13–16 (ω, trine states, |not a⟩, U on p.14); Problem 1.1, p.4

import Mathlib
import Definitions.Def_F3SubsetSum_SubsetSum

namespace F3SubsetSum

/-- `ω = e^{2πi/3}` (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, §3, p.14:
"Let ω = e^{2πi/3}"). -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- A computational-basis label of `W` qutrits: wire `w` holds `y w ∈ F₃ = {0, 1, 2}`. -/
abbrev QBasis (W : ℕ) := Fin W → ZMod 3

/-- A (not necessarily normalised) state of `W` qutrits, i.e. a vector of `(ℂ³)^{⊗W}`, given by
its amplitudes on the computational basis. -/
abbrev Ket (W : ℕ) := QBasis W → ℂ

/-- The computational basis state `|y⟩`. -/
def basisKet {W : ℕ} (y : QBasis W) : Ket W := fun x => if x = y then 1 else 0

/-- **The qutrit Fourier gate** `F|a⟩ = 3^{−1/2} Σ_b ω^{ab} |b⟩`, as the matrix with entry
`⟨b|F|a⟩` at `(b, a)`. -/
noncomputable def fourierMat : Matrix (ZMod 3) (ZMod 3) ℂ :=
  fun b a => omega ^ (a * b).val / (Real.sqrt 3 : ℂ)

/-- **The gate `P`**: `P|0⟩ = (|1⟩ − |2⟩)/√2`, `P|1⟩ = |0⟩`, `P|2⟩ = (|1⟩ + |2⟩)/√2`. It prepares
`|not 0⟩ = (|1⟩ − |2⟩)/√2` (§3, p.14) from `|0⟩`. Entry `⟨b|P|a⟩` at `(b, a)`. -/
noncomputable def pMat : Matrix (ZMod 3) (ZMod 3) ℂ :=
  fun b a =>
    if a = 0 then (if b = 1 then 1 / (Real.sqrt 2 : ℂ) else if b = 2 then -1 / (Real.sqrt 2 : ℂ)
      else 0)
    else if a = 1 then (if b = 0 then 1 else 0)
    else (if b = 0 then 0 else 1 / (Real.sqrt 2 : ℂ))

/-- **The gate `U`** of §3, p.14, which maps the trine states
`τ_a = (ω^a|1⟩ + ω^{−a}|2⟩)/√2` (with `|+1⟩ = |1⟩`, `|−1⟩ = |2⟩`) to
`|not a⟩ = (|a+1⟩ − |a−1⟩)/√2`, completed by `U|0⟩ = 3^{−1/2}(|0⟩ + |1⟩ + |2⟩)`. On the basis,
`U|1⟩ = (√2/3) Σ_a ω^{−a} |not a⟩` and `U|2⟩ = (√2/3) Σ_a ω^{a} |not a⟩`, so the entries are
`⟨b|U|1⟩ = (ω^{−(b−1)} − ω^{−(b+1)})/3` and `⟨b|U|2⟩ = (ω^{b−1} − ω^{b+1})/3`.

**Formalization Note** The paper says only that "there exists a unitary U on ℂ³" with
`|not a⟩ = U|τ_a⟩` (p.14); `U` is fixed here on the third vector `|0⟩`, orthogonal to the trine
states, by sending it to the vector orthogonal to all `|not a⟩`. -/
noncomputable def uMat : Matrix (ZMod 3) (ZMod 3) ℂ :=
  fun b a =>
    if a = 0 then 1 / (Real.sqrt 3 : ℂ)
    else if a = 1 then (omega ^ (-(b - 1)).val - omega ^ (-(b + 1)).val) / 3
    else (omega ^ (b - 1).val - omega ^ (b + 1).val) / 3

/-- **The gate set `G₃`** on `W` qutrit wires. Every gate acts on one, two or three pairwise
distinct wires; no gate carries a parameter.

* `x i`: `|a⟩ ↦ |a + 1⟩` on wire `i`; `xInv i` its inverse.
* `csum i j`: `|a⟩_i |b⟩_j ↦ |a⟩_i |b + a⟩_j`; `csumInv i j` its inverse.
* `ccmul i j k`: `|a⟩_i |b⟩_j |c⟩_k ↦ |a⟩_i |b⟩_j |c + ab⟩_k`; `ccmulInv` its inverse.
* `fourier i`, `p i`, `u i`: the matrices `fourierMat`, `pMat`, `uMat` on wire `i`;
  `fourierInv i`, `pInv i`, `uInv i` their conjugate transposes.

**Formalization Note** The paper names no gate set (it says the unitary `U` "is efficient to
apply to each qutrit", §3, p.14). This finite qutrit gate set computes every function
`F₃^k → F₃` reversibly (with `x`, `csum`, `ccmul`) and contains the amplitudes `3^{−1/2}`,
`2^{−1/2}` and `ω` that the exact bound of Theorem 3.1 needs. -/
inductive Gate (W : ℕ) where
  | x (i : Fin W)
  | xInv (i : Fin W)
  | csum (i j : Fin W) (hij : i ≠ j)
  | csumInv (i j : Fin W) (hij : i ≠ j)
  | ccmul (i j k : Fin W) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
  | ccmulInv (i j k : Fin W) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
  | fourier (i : Fin W)
  | fourierInv (i : Fin W)
  | p (i : Fin W)
  | pInv (i : Fin W)
  | u (i : Fin W)
  | uInv (i : Fin W)

/-- A one-qutrit matrix `M` applied to wire `i`:
`(Mψ)(y) = Σ_a ⟨y_i|M|a⟩ ψ(y with y_i := a)`. -/
def applySingle {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (i : Fin W) (ψ : Ket W) : Ket W :=
  fun y => ∑ a : ZMod 3, M (y i) a * ψ (Function.update y i a)

/-- The action of a gate of `G₃` on a state. The permutation gates map `|y⟩` to `|σ y⟩`, so the
new amplitude at `y` is the old amplitude at `σ⁻¹ y`. -/
noncomputable def applyGate {W : ℕ} : Gate W → Ket W → Ket W
  | .x i, ψ => fun y => ψ (Function.update y i (y i - 1))
  | .xInv i, ψ => fun y => ψ (Function.update y i (y i + 1))
  | .csum i j _, ψ => fun y => ψ (Function.update y j (y j - y i))
  | .csumInv i j _, ψ => fun y => ψ (Function.update y j (y j + y i))
  | .ccmul i j k _ _ _, ψ => fun y => ψ (Function.update y k (y k - y i * y j))
  | .ccmulInv i j k _ _ _, ψ => fun y => ψ (Function.update y k (y k + y i * y j))
  | .fourier i, ψ => applySingle fourierMat i ψ
  | .fourierInv i, ψ => applySingle fourierMat.conjTranspose i ψ
  | .p i, ψ => applySingle pMat i ψ
  | .pInv i, ψ => applySingle pMat.conjTranspose i ψ
  | .u i, ψ => applySingle uMat i ψ
  | .uInv i, ψ => applySingle uMat.conjTranspose i ψ

/-- **A qutrit circuit**: a number of wires and a list of gates of `G₃` on them, applied in
order. -/
structure Circuit where
  /-- The number of qutrit wires (input, output and ancilla wires together). -/
  wires : ℕ
  /-- The gates, applied first to last. -/
  gates : List (Gate wires)

/-- The state after running the circuit on `ψ`. -/
noncomputable def Circuit.run (C : Circuit) (ψ : Ket C.wires) : Ket C.wires :=
  C.gates.foldl (fun φ g => applyGate g φ) ψ

/-- **Input layout** of an instance `h = (h₁, …, h_m)`, `h_i ∈ F₃ⁿ` (Problem 1.1, p.4), on `W`
wires: wire `n·i + j` holds `(h_{i+1})_{j+1}` for `i < m`, `j < n` (0-based), and every other
wire holds `0`. -/
def inputBasis (n m W : ℕ) (h : Fin m → Fin n → ZMod 3) : QBasis W := fun w =>
  if hw : w.val < n * m then
    h ⟨w.val / n, Nat.div_lt_of_lt_mul hw⟩
      ⟨w.val % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hw))⟩
  else 0

/-- **Output convention**: after the final measurement with outcome `y`, the output set is
`S = {i ∈ [m] : y_{n·m + i} ≠ 0}`, read off the `m` wires following the input wires. -/
def outSet (n m : ℕ) {W : ℕ} (y : QBasis W) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i : Fin m =>
    ∃ hw : n * m + i.val < W, y ⟨n * m + i.val, hw⟩ ≠ 0

open Classical in
/-- **Success probability of a circuit on Problem 1.1** (p.4): the circuit is run on the basis
state `|h⟩ ⊗ |0…0⟩` (layout `inputBasis`), every wire is measured in the computational basis,
and the run succeeds when the output set `outSet` is a nonempty `S ⊆ [m]` with
`Σ_{i∈S} h_i = 0`. The probability is over `h₁, …, h_m` independent and uniform in `F₃ⁿ` and over
the measurement outcome `y` (Born rule, weight `|⟨y|C|h,0⟩|²`). -/
noncomputable def successProb (n m : ℕ) (C : Circuit) : ℝ :=
  (∑ h : Fin m → Fin n → ZMod 3, ∑ y : QBasis C.wires,
      if IsZeroSubsetSum h (outSet n m y) then
        Complex.normSq (C.run (basisKet (inputBasis n m C.wires h)) y) else 0) /
    (3 : ℝ) ^ (n * m)

/-- The code of a gate: a 4-bit tag naming the gate kind, then each of its wire indices in the
self-delimiting unary code `1^w 0`. -/
def encodeGate {W : ℕ} : Gate W → List Bool
  | .x i => [false, false, false, false] ++ (List.replicate i.val true ++ [false])
  | .xInv i => [false, false, false, true] ++ (List.replicate i.val true ++ [false])
  | .csum i j _ => [false, false, true, false] ++ (List.replicate i.val true ++ [false]) ++
      (List.replicate j.val true ++ [false])
  | .csumInv i j _ => [false, false, true, true] ++ (List.replicate i.val true ++ [false]) ++
      (List.replicate j.val true ++ [false])
  | .ccmul i j k _ _ _ => [false, true, false, false] ++ (List.replicate i.val true ++ [false]) ++
      (List.replicate j.val true ++ [false]) ++ (List.replicate k.val true ++ [false])
  | .ccmulInv i j k _ _ _ => [false, true, false, true] ++
      (List.replicate i.val true ++ [false]) ++ (List.replicate j.val true ++ [false]) ++
      (List.replicate k.val true ++ [false])
  | .fourier i => [false, true, true, false] ++ (List.replicate i.val true ++ [false])
  | .fourierInv i => [false, true, true, true] ++ (List.replicate i.val true ++ [false])
  | .p i => [true, false, false, false] ++ (List.replicate i.val true ++ [false])
  | .pInv i => [true, false, false, true] ++ (List.replicate i.val true ++ [false])
  | .u i => [true, false, true, false] ++ (List.replicate i.val true ++ [false])
  | .uInv i => [true, false, true, true] ++ (List.replicate i.val true ++ [false])

/-- **The code of a circuit**: the number of wires in unary `1^W 0`, then the codes of the gates
in order. The code is injective (a verification file proves it), so "the machine writes the
code of `C`" determines `C`. Unary wire counts and indices make the code length at least the
number of wires and of gates. -/
def encodeCircuit (C : Circuit) : List Bool :=
  List.replicate C.wires true ++ [false] ++ C.gates.flatMap encodeGate

end F3SubsetSum


