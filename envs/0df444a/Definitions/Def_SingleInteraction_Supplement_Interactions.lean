-- Prove2me | Definitions.Def_SingleInteraction_Supplement_Interactions
-- name    : SingleInteraction_Supplement_Interactions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:02:23.056205+00:00
-- url     : https://prove2.me/theorems/4f239250-6457-409f-9d67-18abf26a7100
-- title:
--   The explicit interactions $h_{\alpha,\beta}$, $g_H$, $g_S$, $S(h)$ and the 8-local $h$ of eq. (45)
-- statement:
--   The explicit interactions of the supplement, with the Pauli matrices $X,Y,Z$ and the first tensor factor on the first qubit of the ordered tuple.
--
--   1. $h_{\alpha,\beta}=\alpha\,Z\otimes Z+\beta\,(X\otimes Y-Y\otimes X)$ (eq. (40)).
--   2. $h_H=X\otimes X+Y\otimes Y+Z\otimes Z$ and $g_H=h_H\otimes\Pi_{|1\rangle}+2I\otimes\Pi_{|0\rangle}$ on $(v_1,v_2,v_3)$ (Theorem 64).
--   3. $h_S=-X\otimes X+Y\otimes Y+2Z\otimes Z$ and $g_S=h_S\otimes\Pi_{|1\rangle}+5I\otimes\Pi_{|0\rangle}$ (Theorem 73).
--   4. The realification $\Phi(M)=\mathrm{Re}(M)\otimes I_L+\mathrm{Im}(M)\otimes J_L$ with $J_L=|1\rangle\langle0|-|0\rangle\langle1|$ (eq. (20)); for a real matrix $R=R^-+R^+$ ($R^-$: diagonal and non-positive off-diagonal entries, $R^+$: strictly positive off-diagonal entries) the sign embedding $R^-\otimes I_c-R^+\otimes X_c$ (eq. (24)); and $S(h)$, the sign embedding of $R(h)=\Phi(h)$ (eq. (57)), acting on $(v_1,\dots,v_k,b,c)$.
--   5. The Barenco gate $B=B(\pi/2,\pi/4,\pi\sqrt2)$ with
--   $$B(\phi,\alpha,\theta)=\begin{pmatrix}1&0&0&0\\0&1&0&0\\0&0&e^{i\alpha}\cos\theta&-ie^{i(\alpha-\phi)}\sin\theta\\0&0&-ie^{i(\alpha+\phi)}\sin\theta&e^{i\alpha}\cos\theta\end{pmatrix},$$
--   the propagation checks $h_{\mathrm{prop}}(U)=\tfrac12(I\otimes|1\rangle\langle1|+I\otimes|0\rangle\langle0|-U\otimes|1\rangle\langle0|-U^\dagger\otimes|0\rangle\langle1|)$ for $U=B$, $\mathrm{SWAP}$ and the one-qubit identity (eqs. (46)–(48)), and the 8-local interaction of eq. (45),
--   $$h=\tfrac14\big(h_{\mathrm{prop1}}\otimes\Pi^{0}_{v_4}\Pi^{1}_{v_5}\Pi^{1}_{v_6}+h_{\mathrm{prop2}}\otimes\Pi^{1}_{v_4}\Pi^{1}_{v_5}\Pi^{0}_{v_6}+h_{\mathrm{prop3}}\otimes\Pi^{1}_{v_3}\Pi^{0}_{v_4}\Pi^{0}_{v_5}\Pi^{0}_{v_6}+\Pi^{1}_{v_1}\Pi^{0}_{v_2}\Pi^{0}_{v_3}\Pi^{0}_{v_4}\Pi^{1}_{v_5}\Pi^{0}_{v_6}\big)\otimes I_{v_7v_8}+I_{v_1\ldots v_6}\otimes h_{\mathrm{check}}(v_7,v_8).$$
--
--   These are the interactions named in Theorems 63, 64, 73, 74 and 81.
--
--   **Formalization Note** Two-qubit gates are written in the basis $|00\rangle,|01\rangle,|10\rangle,|11\rangle$ with the first qubit most significant. The realification qubit $L=b$ and the sign qubit $c$ are the last two qubits of $S(h)$; the clock-transition qubit is the last qubit of each propagation check.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), eq. (40), p.67; Theorem 64, p.70; §7.1, Theorem 73, pp.84–85; eqs. (20), (24), pp.27–28; eq. (57), p.85; §5.4.1, pp.71–72 (Barenco gate); eqs. (45)–(49), pp.72–73

import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_SingleInteraction_twoQubit
import Definitions.Def_SingleInteraction_Supplement_Linalg

open Matrix

namespace SingleInteraction

namespace Supplement

/-!
# The explicit interactions of the supplement

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…):
* `h_{α,β} = α Z⊗Z + β(X⊗Y − Y⊗X)`, eq. (40), p.67;
* `h_H = X⊗X + Y⊗Y + Z⊗Z` and `g_H = h_H ⊗ Π|1⟩ + 2I ⊗ Π|0⟩`, §5.3 and Theorem 64, p.70;
* `h_S = −X⊗X + Y⊗Y + 2Z⊗Z` and `g_S = h_S ⊗ Π|1⟩ + 5I ⊗ Π|0⟩`, §7.1 and Theorem 73, pp.84–85;
* the realification `Φ(M) = Re(M) ⊗ I_L + Im(M) ⊗ J_L`, `J_L = |1⟩⟨0| − |0⟩⟨1|`, eq. (20), p.27,
  and the sign embedding `S(h) = R(h)⁻ ⊗ I_c − R(h)⁺ ⊗ X_c` with `R(h) = Φ(h)`, eqs. (24), (57),
  pp.28 and 85;
* the Barenco gate `B(ϕ, α, θ)` with `ϕ = π/2, α = π/4, θ = π/√2` (pp.71–72), the propagation checks
  (46)–(48), `h_check` (49) and the 8-local interaction `h` of eq. (45), pp.72–73.

**Formalization Note**
* The Pauli matrices are the published `MIPRE.LCS.Pauli.X`, `Y`, `Z`; `twoQubit A B` is `A ⊗ B` with
  `A` on the first qubit (base convention). `tensorQ` puts its first factor on the first qubits, so the
  qubit order of every interaction is the order `(v1, v2, …)` of the paper's argument notation.
* Realification: the extra qubit `L` is the last qubit of `Φ(h)`; the sign qubit `c` is the last
  qubit of `S(h)`. So `S(h)` acts on `(v1, …, vk, b, c)`, as in the proof of Theorem 74 ("append `b`
  and `c`"). `R⁻` keeps the diagonal and the non-positive off-diagonal entries of the real matrix `R`;
  `R⁺` keeps the strictly positive off-diagonal entries.
* Barenco gate: in the basis `|v1 v2⟩ = |00⟩, |01⟩, |10⟩, |11⟩` (first qubit most significant) its
  matrix is the one printed on p.71. `B†` is the conjugate transpose.
* `propagation U` is `½(I⊗|1⟩⟨1| + I⊗|0⟩⟨0| − U⊗|1⟩⟨0| − U†⊗|0⟩⟨1|)` with the clock-transition qubit
  last, as in (46)–(48). Branch selectors of (45) are basis projectors `Π|z⟩` on the listed qubits. -/

open MIPRE.LCS.Pauli

/-- `h_{α,β} = α Z⊗Z + β(X⊗Y − Y⊗X)` (eq. (40)). -/
noncomputable def hAB (α β : ℝ) : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  (α : ℂ) • twoQubit Z Z + (β : ℂ) • (twoQubit X Y - twoQubit Y X)

/-- The antiferromagnetic Heisenberg interaction `h_H = X⊗X + Y⊗Y + Z⊗Z`. -/
noncomputable def hHeis : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  twoQubit X X + twoQubit Y Y + twoQubit Z Z

/-- `g_H = h_H ⊗ Π|1⟩ + 2 I ⊗ Π|0⟩` on `(v1, v2, v3)`. -/
noncomputable def gH : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  tensorQ hHeis (basisProj ![1]) + (2 : ℂ) • tensorQ (1 : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ)
    (basisProj ![0])

/-- `h_S = −X⊗X + Y⊗Y + 2Z⊗Z`. -/
noncomputable def hS : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  -twoQubit X X + twoQubit Y Y + (2 : ℂ) • twoQubit Z Z

/-- `g_S = h_S ⊗ Π|1⟩ + 5 I ⊗ Π|0⟩` on `(v1, v2, v3)`. -/
noncomputable def gS : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  tensorQ hS (basisProj ![1]) + (5 : ℂ) • tensorQ (1 : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ)
    (basisProj ![0])

/-- `J_L = |1⟩⟨0| − |0⟩⟨1|`. -/
def jL : Matrix (Fin 2) (Fin 2) ℂ := ketBra 1 0 - ketBra 0 1

/-- The realification `Φ(M) = Re(M) ⊗ I_L + Im(M) ⊗ J_L` (eq. (20)), `L` the last qubit. -/
noncomputable def realify {k : ℕ} (M : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) :
    Matrix (Fin (k + 1) → Fin 2) (Fin (k + 1) → Fin 2) ℂ :=
  tensorQ (M.map fun z => ((z.re : ℝ) : ℂ)) (oneQ 1) +
    tensorQ (M.map fun z => ((z.im : ℝ) : ℂ)) (oneQ jL)

/-- `R⁻`: the diagonal and the non-positive off-diagonal entries of a real matrix `R`. -/
noncomputable def negPart {q : ℕ} (R : Matrix (Fin q → Fin 2) (Fin q → Fin 2) ℂ) :
    Matrix (Fin q → Fin 2) (Fin q → Fin 2) ℂ :=
  fun s t => if s = t ∨ (R s t).re ≤ 0 then (((R s t).re : ℝ) : ℂ) else 0

/-- `R⁺`: the strictly positive off-diagonal entries of a real matrix `R`. -/
noncomputable def posPart {q : ℕ} (R : Matrix (Fin q → Fin 2) (Fin q → Fin 2) ℂ) :
    Matrix (Fin q → Fin 2) (Fin q → Fin 2) ℂ :=
  fun s t => if s ≠ t ∧ 0 < (R s t).re then (((R s t).re : ℝ) : ℂ) else 0

/-- The sign embedding `R⁻ ⊗ I_c − R⁺ ⊗ X_c` of a real matrix (eq. (24)), `c` the last qubit. -/
noncomputable def signEmbed {q : ℕ} (R : Matrix (Fin q → Fin 2) (Fin q → Fin 2) ℂ) :
    Matrix (Fin (q + 1) → Fin 2) (Fin (q + 1) → Fin 2) ℂ :=
  tensorQ (negPart R) (oneQ 1) - tensorQ (posPart R) (oneQ X)

/-- `S(h) = R(h)⁻ ⊗ I_c − R(h)⁺ ⊗ X_c` with `R(h) = Φ(h)` (eq. (57)), acting on
`(v1, …, vk, b, c)`. -/
noncomputable def stoqEmbed {k : ℕ} (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) :
    Matrix (Fin (k + 1 + 1) → Fin 2) (Fin (k + 1 + 1) → Fin 2) ℂ :=
  signEmbed (realify h)

/-- The index `2 s₁ + s₂` of a two-qubit basis state (first qubit most significant). -/
def idx2 (s : Fin 2 → Fin 2) : Fin 4 :=
  ⟨2 * (s 0 : ℕ) + (s 1 : ℕ), by have := (s 0).isLt; have := (s 1).isLt; omega⟩

/-- The Barenco gate `B(ϕ, α, θ)` (p.71). -/
noncomputable def barenco (ϕ α θ : ℝ) : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  fun s t =>
    (!![1, 0, 0, 0;
        0, 1, 0, 0;
        0, 0, Complex.exp (α * Complex.I) * Real.cos θ,
          -Complex.I * Complex.exp ((α - ϕ) * Complex.I) * Real.sin θ;
        0, 0, -Complex.I * Complex.exp ((α + ϕ) * Complex.I) * Real.sin θ,
          Complex.exp (α * Complex.I) * Real.cos θ] : Matrix (Fin 4) (Fin 4) ℂ) (idx2 s) (idx2 t)

/-- The fixed gate `B = B(π/2, π/4, π/√2)` (p.72; `θ/π = 1/√2`). -/
noncomputable def gateB : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  barenco (Real.pi / 2) (Real.pi / 4) (Real.pi / Real.sqrt 2)

/-- The SWAP gate on two qubits. -/
def swapGate : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  fun s t => if s 0 = t 1 ∧ s 1 = t 0 then 1 else 0

/-- The propagation check `½(I⊗|1⟩⟨1| + I⊗|0⟩⟨0| − U⊗|1⟩⟨0| − U†⊗|0⟩⟨1|)` for a gate `U` on `a`
qubits, with the clock-transition qubit last (eqs. (46)–(48)). -/
noncomputable def propagation {a : ℕ} (U : Matrix (Fin a → Fin 2) (Fin a → Fin 2) ℂ) :
    Matrix (Fin (a + 1) → Fin 2) (Fin (a + 1) → Fin 2) ℂ :=
  (1 / 2 : ℂ) • (tensorQ (1 : Matrix (Fin a → Fin 2) (Fin a → Fin 2) ℂ) (oneQ (ketBra 1 1)) +
    tensorQ (1 : Matrix (Fin a → Fin 2) (Fin a → Fin 2) ℂ) (oneQ (ketBra 0 0)) -
    tensorQ U (oneQ (ketBra 1 0)) - tensorQ Uᴴ (oneQ (ketBra 0 1)))

/-- `hprop1` (46): Barenco propagation on `(v1, v2)` with clock qubit `v3`. -/
noncomputable def hprop1 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := propagation gateB

/-- `hprop2` (47): SWAP propagation on `(v1, v2)` with clock qubit `v3`. -/
noncomputable def hprop2 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := propagation swapGate

/-- `hprop3` (48): identity propagation on `v1` with clock qubit `v2`. -/
noncomputable def hprop3 : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  propagation (1 : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ)

/-- The four computational branches of eq. (45) on `(v1, …, v6)`. -/
noncomputable def branches45 : Matrix (Fin 6 → Fin 2) (Fin 6 → Fin 2) ℂ :=
  tensorQ hprop1 (basisProj ![0, 1, 1]) + tensorQ hprop2 (basisProj ![1, 1, 0]) +
    tensorQ hprop3 (basisProj ![1, 0, 0, 0]) + basisProj ![1, 0, 0, 0, 1, 0]

/-- The fixed 8-local interaction `h` of eq. (45):
`¼(branches) ⊗ I_{v7,v8} + I_{v1..v6} ⊗ h_check(v7, v8)`. -/
noncomputable def h45 : Matrix (Fin 8 → Fin 2) (Fin 8 → Fin 2) ℂ :=
  (1 / 4 : ℂ) • tensorQ branches45 (1 : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ) +
    tensorQ (1 : Matrix (Fin 6 → Fin 2) (Fin 6 → Fin 2) ℂ) hCheck

end Supplement

end SingleInteraction


