-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_RegSyndromeLindbladian
-- name    : AutoQMem_Lindblad_Supplement_RegSyndromeLindbladian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:44:57.63659+00:00
-- url     : https://prove2.me/theorems/e92d6d55-fb0c-4be8-b61a-aa92d26ab034
-- title:
--   Register-extended syndrome-based Lindbladian
-- statement:
--   A **register-extended syndrome-based Lindbladian** on $\mathcal H^{\mathrm{ext}}$ has the form
--   $$\mathcal L(t)(\rho)=-i[H(t),\rho]+\sum_\alpha\mathcal D\big[P_{i}\,\Theta_\alpha\,f_\alpha(t)\big](\rho),$$
--   where $H(t)$ is a Hermitian element of $\mathcal A^{\mathrm{ext}}$, each jump has a single-qubit data Pauli $P_i$ ($P\in\{I,X,Y,Z\}$, $i$ its site label), a register Pauli string $\Theta_\alpha=X^{v}Z^{w}$ and a syndrome function $f_\alpha(t)\in\mathcal A^{\mathrm{ext}}$. The **$\sigma$-flip** of the jump is $(u,v_\sigma)$, where $u=\hat e_i$ if $P$ flips qubit $i$ in sector $\sigma$ ($P\in\{Z,Y\}$ for $\sigma=X$, $P\in\{X,Y\}$ for $\sigma=Z$) and $u=0$ otherwise, and $v_\sigma$ is $v$ restricted to $\mathrm{Reg}_\sigma$. The flip-rate operators must satisfy the **extended rate condition**
--   $$\Gamma^{(\sigma)}_{u,v}(t)=\sum_{\alpha:\ \sigma\text{-flip}(\alpha)=(u,v)}f_\alpha(t)^\dagger f_\alpha(t)\ \in\ \mathcal A^{\mathrm{ext}}_\sigma\qquad\text{for all }(u,v)\neq(0,0),\ t\ge0 .$$
--
--   This is the class of Lindbladians, acting on data and classical registers, in which Theorem 4 constructs its Floquet memory.
--
--   **Formalization Note** The phase of $\Theta$ does not affect $\mathcal D[\cdot]$ and is omitted. As in the base mission (Reading R1), $H(t)$ and $f_\alpha(t)$ are required to be measurable on $[0,\infty)$ and bounded on bounded intervals.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 7.1, eqs. (178)–(179), p. 52 (PDF p. 54); §7.1, p. 52 (PDF p. 54)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Supplement_Registers
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Data part of the σ-flip of a jump `P_i Θ f`** (Drechsler, Oreg, Aharonov, *Autonomous Quantum
Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), §7.1, p. 52,
PDF 54): "u = ê_i if P ∈ {Z, Y} for σ = X, or if P ∈ {X, Y} for σ = Z, and u = 0 otherwise"
(`σ = true` is X). -/
noncomputable def dataFlip {n : ℕ} (σ : Bool) (P : Pauli1) (i : Fin n) : Fin n → ZMod 2 :=
  if (σ = true ∧ (P = .Z ∨ P = .Y)) ∨ (σ = false ∧ (P = .X ∨ P = .Y)) then Pi.single i 1 else 0

/-- **Register part `v_σ` of the σ-flip** of a register Pauli string `Θ = i^k X^v Z^w`: the
restriction of `v` to `Reg_σ` (§7.1, p. 52: "The σ-flip of P_iΘ is the pair (u, v_σ)"), written as a
vector on all registers that vanishes off `Reg_σ`. -/
def regFlip {n : ℕ} (R : Registers n) (σ : Bool) (v : R.Reg → ZMod 2) : R.Reg → ZMod 2 :=
  fun j => if R.isX j = σ then v j else 0

/-- **Register-extended syndrome-based Lindbladian (its representation data).** Drechsler, Oreg,
Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of
2026-11-03), Definition 7.1, eqs. (178)–(179), p. 52 (PDF 54): "A Lindbladian on H^ext is a
register-extended syndrome-based Lindbladian if it has the form of Definition 2.22 with the following
changes. (i) The Hamiltonian H(t) is a Hermitian element of A^ext. (ii) Each jump P_i f_{P,i,α}(t)
becomes P_i Θ_{P,i,α} f_{P,i,α}(t), where Θ_{P,i,α} is a Pauli string on the registers and the
syndrome function f_{P,i,α}(t) lies in A^ext. … (iii) The flip-rate operators are indexed by the
sector flip, Γ^{(σ)}_{u,v}(t) := Σ_{(P,i,α)∈J^{(σ)}_{u,v}} f_{P,i,α}(t)† f_{P,i,α}(t), (u, v) ≠ (0, 0)
… (iv) … Γ^{(σ)}_{u,v}(t) ∈ A^ext_σ for all (u, v) ≠ (0, 0) and t ≥ 0."

**Formalization Note.**
* The jumps are indexed by one finite type `ι`; jump `α` carries its data Pauli `pauli α` at
  qubit `site α` (the label `i`), the register string `Θ_α = X^{regX α} Z^{regZ α}` (the phase
  `i^k` does not change `D[·]`) and the syndrome function `f t α`. The jump operator is
  `RegSyndromeLindbladian.jump`, the generator `RegSyndromeLindbladian.gen`.
* The rate condition is imposed for every sector, every `(u, v) ≠ (0, 0)` and `t ≥ 0`.
* Reading R1 of the base mission (time regularity): `H(t)` and `f(t)` are measurable on `[0, ∞)`
  (entrywise) and bounded on every `[0, T]`. -/
structure RegSyndromeLindbladian {n mX mZ : ℕ} (C : CSSCode n mX mZ) (R : Registers n) :
    Type 1 where
  /-- The finite jump index set. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The Hamiltonian `H(t)`. -/
  ham : ℝ → R.Op
  /-- The data Pauli type `P` of each jump. -/
  pauli : ι → Pauli1
  /-- The data qubit label `i` of each jump. -/
  site : ι → Fin n
  /-- The X part `v` of the register string `Θ = X^v Z^w`. -/
  regX : ι → R.Reg → ZMod 2
  /-- The Z part `w` of the register string `Θ = X^v Z^w`. -/
  regZ : ι → R.Reg → ZMod 2
  /-- The syndrome functions `f_{P,i,α}(t)`. -/
  f : ℝ → ι → R.Op
  /-- (i) `H(t)` is a Hermitian element of `A^ext`. -/
  ham_mem : ∀ t : ℝ, 0 ≤ t → ham t ∈ R.algExt C ∧ (ham t).IsHermitian
  /-- (ii) every syndrome function lies in `A^ext`. -/
  f_mem : ∀ t : ℝ, 0 ≤ t → ∀ α, f t α ∈ R.algExt C
  /-- (iii)–(iv) the extended rate condition (179). -/
  rate_mem : ∀ t : ℝ, 0 ≤ t → ∀ (σ : Bool) (u : Fin n → ZMod 2) (v : R.Reg → ZMod 2),
    (u, v) ≠ (0, 0) →
      ∑ α ∈ Finset.univ.filter
          (fun α => dataFlip σ (pauli α) (site α) = u ∧ regFlip R σ (regX α) = v),
        (f t α)ᴴ * f t α ∈ R.algExtSec C σ
  /-- R1: `t ↦ H(t)` is measurable on `[0, ∞)`, entrywise. -/
  ham_meas : ∀ x y, Measurable fun t : Set.Ici (0 : ℝ) => ham t x y
  /-- R1: `t ↦ f(t)` is measurable on `[0, ∞)`, entrywise. -/
  f_meas : ∀ α x y, Measurable fun t : Set.Ici (0 : ℝ) => f t α x y
  /-- R1: `H(t)` is bounded on every `[0, T]`. -/
  ham_bdd : ∀ T : ℝ, ∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x y, ‖ham t x y‖ ≤ B
  /-- R1: the syndrome functions are bounded on every `[0, T]`. -/
  f_bdd : ∀ T : ℝ, ∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α x y, ‖f t α x y‖ ≤ B

attribute [instance] RegSyndromeLindbladian.fintype

namespace RegSyndromeLindbladian

variable {n mX mZ : ℕ} {C : CSSCode n mX mZ} {R : Registers n}

/-- The jump operator `P_i Θ_{P,i,α} f_{P,i,α}(t)` (Definition 7.1 (ii)). -/
noncomputable def jump (L : RegSyndromeLindbladian C R) (t : ℝ) (α : L.ι) : R.Op :=
  R.extData (pauliAt (L.pauli α) (L.site α)) * R.regXstr (L.regX α) * R.regZstr (L.regZ α) *
    L.f t α

/-- The generator `L(t)(ρ) = −i[H(t), ρ] + Σ_α D[P_i Θ f](ρ)` (Definition 7.1 with eq. (31)),
Schrödinger picture. -/
noncomputable def gen (L : RegSyndromeLindbladian C R) (t : ℝ) (ρ : R.Op) : R.Op :=
  -Complex.I • (L.ham t * ρ - ρ * L.ham t) + ∑ α, dissG (L.jump t α) ρ

end RegSyndromeLindbladian

end AutoQMem.Lindblad.Supplement


