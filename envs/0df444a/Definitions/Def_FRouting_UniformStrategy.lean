-- Prove2me | Definitions.Def_FRouting_UniformStrategy
-- name    : FRouting_UniformStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:03.526618+00:00
-- url     : https://prove2.me/theorems/b9b96196-d0a0-4112-9727-64ba1e8d45ea
-- title:
--   $T$-uniform $f$-routing strategies
-- statement:
--   A **$T$-uniform strategy** with dimension function $d$ has three fixed machines. For every $n$: $\mathrm{Gen}_{\rm res}(1^n)$ prints a circuit on $2q(n)$ wires, the first $q(n)$ being $L$ and the last $q(n)$ being $R$, with $q(n)\le T(n)$. For all $x,y\in\{0,1\}^n$: $\mathrm{Gen}^{\rm pre}_A(1^n,x)$ prints the circuit of $\mathcal U^x$, whose inputs are $Q$ and $L$ and whose outputs are split into $A_1,B_2$, and $\mathrm{Gen}^{\rm pre}_B(1^n,y)$ prints the circuit of $\mathcal V^y$, whose input is $R$ and whose outputs are split into $B_1,A_2$. Each machine runs in time at most $T(n)$, and each printed circuit has size and width at most $T(n)$. The post-communication channels are arbitrary. `toRouting n` is the routing strategy at length $n$, with resource state $\mathcal I^n(|0^{2q}\rangle\langle 0^{2q}|)$.
--
--   The machines are fixed, not functions of $x$: that is the uniformity.
--
--   **Formalization Note** The post-communication generators of Definition 3.6 are unrestricted and the proof never runs them, so no machine is asked of them; this also covers uncomputable decoders. Size and width are explicit because a `FinTM2` step may push several symbols. Time, size and width use `budget T n`, equal to $T(n)$ unless $T(n)=0$.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 1.2, p.4; Definition 3.6, pp.15–16; §3.4, p.16

import Definitions.Def_FRouting_RoutingStrategy
import Definitions.Def_FRouting_encCircuit
import Definitions.Def_FRouting_StrMachine

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace FRouting

open WildeQIT QAlgorithms.Complexity

/-- The registers of `k` qudits of dimension `D`. -/
def quditReg (D k : ℕ) : Reg := ⟨Fin k → Fin D⟩

/-- A channel preserves density matrices. -/
theorem QChannel_apply_isDensity {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) {ρ : Matrix a a ℂ} (h : PeresTerno.IsDensityMatrix ρ) :
    PeresTerno.IsDensityMatrix (N.apply ρ) := by
  refine ⟨?_, ?_⟩
  · refine Matrix.posSemidef_sum _ fun i _ => ?_
    exact h.1.mul_mul_conjTranspose_same (N.K i)
  · unfold QChannel.apply
    rw [Matrix.trace_sum]
    have : ∀ i, (N.K i * ρ * (N.K i)ᴴ).trace = ((N.K i)ᴴ * N.K i * ρ).trace := by
      intro i
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp only [this]
    rw [← Matrix.trace_sum, ← Matrix.sum_mul, N.complete, Matrix.one_mul]
    exact h.2

theorem single_zero_isDensity {a : Type} [Fintype a] [DecidableEq a] (z : a) :
    PeresTerno.IsDensityMatrix (Matrix.single z z (1 : ℂ)) := by
  refine ⟨?_, by simp⟩
  have : Matrix.single z z (1 : ℂ)
      = Matrix.vecMulVec (Pi.single z (1 : ℂ)) (star (Pi.single z (1 : ℂ))) := by
    ext i j
    simp only [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.star_apply, Pi.single_apply]
    by_cases hi : z = i <;> by_cases hj : z = j <;> simp [hi, hj, eq_comm]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem isDensity_submatrix {a b : Type} [Fintype a] [Fintype b] (e : b ≃ a) {ρ : Matrix a a ℂ}
    (h : PeresTerno.IsDensityMatrix ρ) : PeresTerno.IsDensityMatrix (ρ.submatrix e e) := by
  refine ⟨h.1.submatrix _, ?_⟩
  have : (ρ.submatrix e e).trace = ρ.trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
    exact e.sum_comp fun i => ρ i i
  rw [this]
  exact h.2

/-- **A `T`-uniform routing-strategy family.** Renard, *Computational Bounds for f-Routing*,
arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 1.2, p.4 and Definition 3.6, pp.15–16.
One machine `genRes`, one `genA`, one `genB` for all `n`, `x`, `y`:
- `genRes(1ⁿ)` prints the resource circuit, on `2q` wires, the first `q` being `L`, the last `q`
  being `R`;
- `genA(1ⁿ, x)` prints `𝒰ˣ`: the input wires are `Q` (wire `0`) and `L`, the first `a₁` output wires are
  `A₁` and the next `b₂` are `B₂`;
- `genB(1ⁿ, y)` prints `𝒱ʸ`: the input wires are `R`, the first `b₁` output wires are `B₁` and the next
  `a₂` are `A₂`;
- each runs within the budget of `T(n)`, and each printed circuit has size and width at most that
  budget, with `q ≤ T(n)` ("the circuit printed by each generator has size at most T(n), and acts on
  that many qubits", p.4).

**Formalization Note** "All registers are `d(n)`-dimensional qudits": each register is a tuple of
wires. The post-communication channels are arbitrary and need no machine (`Gen^post` is
"unrestricted", p.16, and the proof never runs it), which covers uncomputable ones and is a
generalization. Size and width are explicit clauses, since a `FinTM2` step may push several symbols.
`budget` differs from `T` only where `T n = 0`. -/
structure UniformStrategy (d T : ℕ → ℕ) where
  /-- The machine `Gen_res`. -/
  genRes : StrMachine
  /-- The machine `Gen^pre_A`. -/
  genA : StrMachine
  /-- The machine `Gen^pre_B`. -/
  genB : StrMachine
  /-- The number `q(n)` of qudits per adversary of the resource. -/
  q : ℕ → ℕ
  /-- The resource circuit `ℐⁿ_{LR→LR}`. -/
  res : ∀ n, Circuit (d n) (q n + q n) (q n + q n)
  /-- The width of `A₁`. -/
  a₁ : ∀ n, (Fin n → Bool) → ℕ
  /-- The width of `B₂`. -/
  b₂ : ∀ n, (Fin n → Bool) → ℕ
  /-- The width of `B₁`. -/
  b₁ : ∀ n, (Fin n → Bool) → ℕ
  /-- The width of `A₂`. -/
  a₂ : ∀ n, (Fin n → Bool) → ℕ
  /-- The circuit of `𝒰ˣ_{QL→A₁B₂}`. -/
  preA : ∀ n x, Circuit (d n) (q n + 1) (a₁ n x + b₂ n x)
  /-- The circuit of `𝒱ʸ_{R→B₁A₂}`. -/
  preB : ∀ n y, Circuit (d n) (q n) (b₁ n y + a₂ n y)
  /-- The channel `𝒰ˣʸᵇ_{A₁A₂→Q₀}`. -/
  decA : ∀ n x y, Bool → QChannel (quditReg (d n) (a₁ n x) × quditReg (d n) (a₂ n y)) (Fin (d n))
  /-- The channel `𝒱ˣʸᵇ_{B₁B₂→Q₁}`. -/
  decB : ∀ n x y, Bool → QChannel (quditReg (d n) (b₁ n y) × quditReg (d n) (b₂ n x)) (Fin (d n))
  res_prints : ∀ n, PrintsInTime genRes (List.replicate n true) (encCircuit (res n)) (budget T n)
  preA_prints : ∀ n x, PrintsInTime genA (encNat n ++ List.ofFn x)
    (encNat (a₁ n x) ++ encNat (b₂ n x) ++ encCircuit (preA n x)) (budget T n)
  preB_prints : ∀ n y, PrintsInTime genB (encNat n ++ List.ofFn y)
    (encNat (b₁ n y) ++ encNat (a₂ n y) ++ encCircuit (preB n y)) (budget T n)
  q_le : ∀ n, q n ≤ T n
  res_size : ∀ n, (res n).size ≤ budget T n ∧ (res n).width ≤ budget T n
  preA_size : ∀ n x, (preA n x).size ≤ budget T n ∧ (preA n x).width ≤ budget T n
  preB_size : ∀ n y, (preB n y).size ≤ budget T n ∧ (preB n y).width ≤ budget T n

namespace UniformStrategy

variable {d T : ℕ → ℕ} (S : UniformStrategy d T)

/-- **The strategy at length `n`**: the channels of the printed circuits, and the resource
`ℐⁿ(|0^{2q}⟩⟨0^{2q}|)` (p.16, step 1), with the wires read as the registers of Definition 3.6. -/
noncomputable def toRouting (n : ℕ) : RoutingStrategy n (d n) where
  L := quditReg (d n) (S.q n)
  R := quditReg (d n) (S.q n)
  A₁ x := quditReg (d n) (S.a₁ n x)
  B₂ x := quditReg (d n) (S.b₂ n x)
  B₁ y := quditReg (d n) (S.b₁ n y)
  A₂ y := quditReg (d n) (S.a₂ n y)
  resource :=
    let e : (quditReg (d n) (S.q n) × quditReg (d n) (S.q n)) ≃ (Fin (S.q n + S.q n) → Fin (d n)) :=
      Fin.appendEquiv (S.q n) (S.q n)
    ((S.res n).outputState).submatrix e e
  resource_density :=
    isDensity_submatrix _ (QChannel_apply_isDensity _ (single_zero_isDensity _))
  U x := chanReindex
    (Fin.consEquiv fun _ => Fin (d n)).symm
    (Fin.appendEquiv (S.a₁ n x) (S.b₂ n x)).symm (S.preA n x).channel
  V y := chanReindex (Equiv.refl _)
    (Fin.appendEquiv (S.b₁ n y) (S.a₂ n y)).symm (S.preB n y).channel
  Uₚ x y b := S.decA n x y b
  Vₚ x y b := S.decB n x y b

end UniformStrategy

end FRouting


