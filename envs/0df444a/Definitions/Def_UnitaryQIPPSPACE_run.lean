-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_run
-- name    : UnitaryQIPPSPACE_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:18.710057+00:00
-- url     : https://prove2.me/theorems/31421468-0cac-44ad-9dc6-528761e7a468
-- title:
--   The interaction $V(|\psi\rangle)\leftrightarrows P$, acceptance probability and conditioned output
-- statement:
--   The interaction of a $k$-round verifier $V$ with a prover $P$ on an input $|\psi\rangle$ (on at most as many qubits as $Z_{\mathrm{work}}$) starts in
--   $$\rho_0=|\psi,0\cdots0\rangle\langle\psi,0\cdots0|_{Z_{\mathrm{work}}}\otimes|0\cdots0\rangle\langle0\cdots0|_{Z_{\mathrm{flag}}Z_{\mathrm{out}}MY},$$
--   after which the prover and the verifier alternate, the prover first: $\rho_i=(I_Z\otimes P)(\rho_{i-1})$ for odd $i$ and $\rho_i=(V_{i/2}\otimes I_Y)(\rho_{i-1})$ for even $i$, $i=1,\dots,2k$.
--
--   The verifier **accepts** with probability $\operatorname{tr}[|1\rangle\langle1|_{Z_{\mathrm{flag}}}\rho_{2k}]$. The **unnormalized accepted map** keeps $Z_{\mathrm{out}}$ and $Y$: $\operatorname{tr}_{Z\setminus Z_{\mathrm{out}},M}(|1\rangle\langle1|_{Z_{\mathrm{flag}}}\rho_{2k})$. The **output conditioned on accepting** is
--   $$\frac{\operatorname{tr}_{ZMY\setminus Z_{\mathrm{out}}}(|1\rangle\langle1|_{Z_{\mathrm{flag}}}\rho_{2k})}{\operatorname{tr}[|1\rangle\langle1|_{Z_{\mathrm{flag}}}\rho_{2k}]}.$$
--
--   **Formalization Note** The initial state $\sigma$ of the prover's private register is a parameter: the classes use $\sigma=|0\cdots0\rangle\langle0\cdots0|$, as in the paper, and Lemmas 4.16 and 4.18 "regard its initial private state as an input". When the acceptance probability is $0$ the conditioned output, "left undefined" in the paper, is the zero matrix; it is used only when the acceptance probability exceeds $s\ge0$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2, Quantum interactive proof systems, eq. (1), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_Verifier
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open Matrix

namespace UnitaryQIPPSPACE

open Classical in
/-- The input vector `|ψ, 0⋯0⟩` on `(Z, M)`: `|ψ⟩` (on `n` qubits) on the first `n` qubits of
`Z_work`, every other qubit in `|0⟩`. -/
noncomputable def inputVec (V : Verifier) (n : ℕ) (ψ : Bits n → ℂ) : Bits V.dim → ℂ :=
  fun u => if ∀ j : Fin V.dim, n ≤ j.val → u j = false then
    ψ (fun i => if h : i.val < V.dim then u ⟨i.val, h⟩ else false) else 0

/-- `V_i ⊗ I_Y`: a map on the operators of `(Z, M)` applied to the first factor of
`(Z, M) ⊗ Y`, `(Φ ⊗ id)(ρ)` with entries `(Φ(ρ^{(b, b')}))(a, a')` where
`ρ^{(b,b')}(a, a') = ρ((a, b), (a', b'))`. -/
def liftLeft {α β : Type} (Φ : Matrix α α ℂ → Matrix α α ℂ)
    (ρ : Matrix (α × β) (α × β) ℂ) : Matrix (α × β) (α × β) ℂ :=
  fun x x' => Φ (fun a a' => ρ (a, x.2) (a', x'.2)) x.1 x'.1

open Classical in
/-- `I_Z ⊗ P` on `(Z, M) ⊗ Y`, for an operator `P` on `M ⊗ Y`. -/
noncomputable def proverOn (V : Verifier) {y : ℕ}
    (P : Matrix (Bits V.m × Bits y) (Bits V.m × Bits y) ℂ) :
    Matrix (Bits V.dim × Bits y) (Bits V.dim × Bits y) ℂ :=
  fun x x' =>
    let s := Bits.splitEquiv (V.w + 1 + V.o) V.m x.1
    let s' := Bits.splitEquiv (V.w + 1 + V.o) V.m x'.1
    if s.1 = s'.1 then P (s.2, x.2) (s'.2, x'.2) else 0

/-- **The interaction `V(|ψ⟩) ⇆ P`** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819,
held version sha256 9e357a00…, §2, p. 11 (PDF p. 13)): "Let `|ψ⟩` be a quantum state on at most as
many qubits as `Z_work`. … The system is initialized in the state
`ρ₀ = |ψ, 0⋯0⟩⟨ψ, 0⋯0|_{Z_work} ⊗ |0⋯0⟩⟨0⋯0|_{Z_flag Z_out M Y}`, after which the prover and the
verifier act alternately, starting with the prover: for `i = 1, …, 2k`,
`ρ_i = (I_Z ⊗ P)(ρ_{i−1})` for odd `i`, `ρ_i = (V_{i/2} ⊗ I_Y)(ρ_{i−1})` for even `i`."

`run V P n ψ σ` is `ρ_{2k}` on `(Z, M) ⊗ Y`, for an `n`-qubit input vector `ψ`, the prover's
operator `P` on `M ⊗ Y` (applied by conjugation), and the initial state `σ` of `Y`.

**Formalization Note** The initial private state `σ` is a parameter. The paper's interaction is
`σ = |0⋯0⟩⟨0⋯0|` (`zeroState`), which every class definition uses; the proofs of Lemmas 4.16 and
4.18 "regard its initial private state on P as an input" (p. 31), which needs general `σ`. -/
noncomputable def run (V : Verifier) {y : ℕ} (P : Matrix (Bits V.m × Bits y) (Bits V.m × Bits y) ℂ)
    (n : ℕ) (ψ : Bits n → ℂ) (σ : Matrix (Bits y) (Bits y) ℂ) :
    Matrix (Bits V.dim × Bits y) (Bits V.dim × Bits y) ℂ :=
  V.rounds.foldl
    (fun ρ c => liftLeft (c.chan V.dim V.dim) (conjBy (proverOn V P) ρ))
    (fun x x' => inputVec V n ψ x.1 * star (inputVec V n ψ x'.1) * σ x.2 x'.2)

/-- **Acceptance probability** `tr[|1⟩⟨1|_{Z_flag} · ρ_{2k}]` (p. 11): "The interaction
`V(|ψ⟩) ⇆ P` accepts (resp. rejects) if measuring the register `Z_flag` of `ρ_{2k}` in the
computational basis yields the outcome 1 (resp. 0)." -/
noncomputable def acceptProb (V : Verifier) {y : ℕ}
    (P : Matrix (Bits V.m × Bits y) (Bits V.m × Bits y) ℂ)
    (n : ℕ) (ψ : Bits n → ℂ) (σ : Matrix (Bits y) (Bits y) ℂ) : ℝ :=
  (∑ x : Bits V.dim × Bits y,
    if x.1 V.flagIdx = true then run V P n ψ σ x x else 0).re

open Classical in
/-- **The unnormalized accepted map** `tr_{Z∖Z_out, M}(|1⟩⟨1|_{Z_flag} · ρ_{2k})`, kept on
`Z_out ⊗ Y`: entry `((a, b), (a', b'))` sums `ρ_{2k}((u, b), (u', b'))` over the labels `u, u'` of
`(Z, M)` with flag `1` that agree off `Z_out` and read `a`, `a'` on `Z_out`. As a function of the
prover's initial private state `σ` (p. 31, Lemma 4.16: "regard its initial private state on `P` as
an input, and let `A : L(H_P) → L(H_B ⊗ H_P)` be the unnormalized accepted map"). -/
noncomputable def acceptedMap (V : Verifier) {y : ℕ}
    (P : Matrix (Bits V.m × Bits y) (Bits V.m × Bits y) ℂ)
    (n : ℕ) (ψ : Bits n → ℂ) (σ : Matrix (Bits y) (Bits y) ℂ) :
    Matrix (Bits V.o × Bits y) (Bits V.o × Bits y) ℂ :=
  fun x x' => ∑ u : Bits V.dim, ∑ u' : Bits V.dim,
    if u V.flagIdx = true ∧
        (∀ j : Fin V.dim, ¬ (V.w + 1 ≤ j.val ∧ j.val < V.w + 1 + V.o) → u j = u' j) ∧
        (fun i => u (V.outIdx i)) = x.1 ∧ (fun i => u' (V.outIdx i)) = x'.1
    then run V P n ψ σ (u, x.2) (u', x'.2) else 0

/-- **The output conditioned on accepting**, eq. (1), p. 11:
`tr_{ZMY∖Z_out}(|1⟩⟨1|_{Z_flag} · ρ_{2k}) / tr[|1⟩⟨1|_{Z_flag} · ρ_{2k}]`, "the reduced state of
`ρ_{2k}` on `Z_out` after post-selecting on acceptance in the flag register `Z_flag`".

**Formalization Note** "If the acceptance probability is 0, the output is left undefined"; here it
is then the zero matrix (Lean's `0⁻¹ = 0`). Every use is under acceptance probability `> s ≥ 0`. -/
noncomputable def condOutput (V : Verifier) {y : ℕ}
    (P : Matrix (Bits V.m × Bits y) (Bits V.m × Bits y) ℂ)
    (n : ℕ) (ψ : Bits n → ℂ) (σ : Matrix (Bits y) (Bits y) ℂ) : Matrix (Bits V.o) (Bits V.o) ℂ :=
  ((acceptProb V P n ψ σ : ℂ))⁻¹ • fun a a' => ∑ b : Bits y, acceptedMap V P n ψ σ (a, b) (a', b)

/-- An operator on `Z_out` read as an operator on `n` qubits when `Z_out` has `n` qubits (`0`
otherwise). -/
def outTo (V : Verifier) (n : ℕ) (X : Matrix (Bits V.o) (Bits V.o) ℂ) :
    Matrix (Bits n) (Bits n) ℂ :=
  fun a a' => if h : V.o = n then X (fun i => a (Fin.cast h i)) (fun i => a' (Fin.cast h i)) else 0

end UnitaryQIPPSPACE


