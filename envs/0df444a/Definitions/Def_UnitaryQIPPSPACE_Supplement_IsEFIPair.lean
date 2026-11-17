-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_Supplement_IsEFIPair
-- name    : UnitaryQIPPSPACE_Supplement_IsEFIPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:45:49.32835+00:00
-- url     : https://prove2.me/theorems/2830f9ca-3930-43b0-8adf-50f0e967479b
-- title:
--   EFI pairs (Definition 5.5)
-- statement:
--   An **EFI pair** is a family $\{\rho_{0,n},\rho_{1,n}\}_{n\in\mathbb N}$ of pairs of mixed states on $k(n)$ qubits satisfying:
--
--   1. **Efficient (E) generation.** A uniform quantum polynomial-time algorithm $G$, on input $(1^n,b)$, outputs $\rho_{b,n}$ for each $b\in\{0,1\}$.
--   2. **Statistical farness (F).** There is a polynomial $q\ge1$ such that $\mathrm{TD}(\rho_{0,n},\rho_{1,n})\ge 1/q(n)$ for all sufficiently large $n$.
--   3. **Computational indistinguishability (I).** For every quantum polynomial-time distinguisher $D$ with polynomial-size quantum advice $\{\sigma_n\}_n$, the advantage
--   $$\big|\Pr[D(1^n,\rho_{0,n}\otimes\sigma_n)=0]-\Pr[D(1^n,\rho_{1,n}\otimes\sigma_n)=0]\big|$$
--   is negligible in $n$.
--
--   "EFI pairs exist" means that some generator $G$ yields an EFI pair. This is the hypothesis of Theorem 1.5.
--
--   **Formalization Note** $G(1^n,b)$ is a circuit of the base model (qubit initialization, partial trace, gates $H,T,\mathrm{CNOT}$, computational-basis measurement) of size at most $p(n)$, run on zero input qubits, whose description a Turing machine computes from $(1^n,b)$ within $p(n)$ steps; $\rho_{b,n}$ is its output. A distinguisher is a uniform family of such circuits (description computed from $1^n$ in polynomial time) acting on $\rho\otimes\sigma_n$ — challenge on the first $k(n)$ qubits, advice on the next $a(n)\le p(n)$ qubits — with output qubit $0$ measured; the advice $\sigma_n$ is any density matrix. Negligibility is the published notion ($\nu\ge0$ and $\nu(n)\le n^{-c}$ eventually for every $c>0$), and $\mathrm{TD}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Definition 5.5 ([BCQ23, Definition 7]), p.43 (PDF p.45); negligible functions p.8 (PDF p.10)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_UnitaryQIPPSPACE_Circuit
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform

open Matrix QAlgorithms.Complexity QAdvFew.PoQOracle
open scoped ComplexOrder

namespace UnitaryQIPPSPACE

namespace Supplement

/-- The product state `ρ ⊗ σ` on `k + a` qubits: `ρ` on the first `k` qubits, `σ` on the last
`a` qubits. -/
def tensorState {k a : ℕ} (ρ : Matrix (Bits k) (Bits k) ℂ) (σ : Matrix (Bits a) (Bits a) ℂ) :
    Matrix (Bits (k + a)) (Bits (k + a)) ℂ :=
  fun x y => ρ (Bits.splitEquiv k a x).1 (Bits.splitEquiv k a y).1 *
    σ (Bits.splitEquiv k a x).2 (Bits.splitEquiv k a y).2

open Classical in
/-- The probability that measuring qubit `0` of an `o`-qubit state `X` in the computational basis
gives outcome `0`: the real part of the sum of the diagonal entries `X(x, x)` whose label reads
`0` (`false`) on qubit `0` (no label qualifies when `o = 0`). -/
noncomputable def probZero (o : ℕ) (X : Matrix (Bits o) (Bits o) ℂ) : ℝ :=
  (∑ x : Bits o, if (∃ h : 0 < o, x ⟨0, h⟩ = false) then X x x else 0).re

/-- **Uniform quantum polynomial-time generation** (Definition 5.5, item 1, p. 43): "A uniform
quantum polynomial-time algorithm `G`, on input `(1^n, b)`, outputs `ρ_{b,n}` for each
`b ∈ {0, 1}`." Here `G n b` is a circuit of the base model (init, partial trace, `{H, T, CNOT}`,
measurement) starting from zero qubits and ending with `k(n)` qubits, and one Turing machine `M`
and one polynomial `p` satisfy, for all `n` and `b`: `|G n b| ≤ p(n)`, and `M` on input
`(1^n, b)` has halted after `p(n)` steps with the description of `G n b` (the convention of
the base `TimeUniformVerifiers`, machines run with the empty oracle). -/
def UniformGen (k : ℕ → ℕ) (G : ℕ → Bool → Circuit) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ (n : ℕ) (b : Bool),
    (G n b).WF 0 (k n) ∧ (G n b).length ≤ p.eval n ∧
    M.result noOracle (tup [unary n, [b]]) (p.eval n) ≠ none ∧
    M.output noOracle (tup [unary n, [b]]) (p.eval n) = (G n b).code

/-- The mixed state `ρ_{b,n}` output by `G` on `(1^n, b)`: the channel of `G n b` applied to the
(unique) state of zero qubits. -/
noncomputable def genState (k : ℕ → ℕ) (G : ℕ → Bool → Circuit) (n : ℕ) (b : Bool) :
    Matrix (Bits (k n)) (Bits (k n)) ℂ :=
  (G n b).chan 0 (k n) 1

/-- A candidate distinguisher for states on `k(n)` qubits: circuits `D n` reading the challenge
state on `k(n)` qubits followed by an advice state on `a(n)` qubits, and ending with `o(n)`
qubits, of which qubit `0` is measured. -/
structure Distinguisher (k : ℕ → ℕ) where
  /-- number of advice qubits -/
  a : ℕ → ℕ
  /-- number of output qubits -/
  o : ℕ → ℕ
  /-- the circuits -/
  D : ℕ → Circuit

/-- **Quantum polynomial-time distinguisher with polynomial-size quantum advice** (Definition 5.5,
item 3, p. 43): one machine `M` and one polynomial `p` with, for every `n`: at least one output
qubit, `D n` well formed from `k(n) + a(n)` to `o(n)` qubits, `|D n| ≤ p(n)`, `a(n) ≤ p(n)`, and
`M` on `1^n` has halted after `p(n)` steps with the description of `D n`. -/
def Distinguisher.IsQPT {k : ℕ → ℕ} (D : Distinguisher k) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ n : ℕ,
    1 ≤ D.o n ∧ (D.D n).WF (k n + D.a n) (D.o n) ∧ (D.D n).length ≤ p.eval n ∧
    D.a n ≤ p.eval n ∧
    M.result noOracle (unary n) (p.eval n) ≠ none ∧
    M.output noOracle (unary n) (p.eval n) = (D.D n).code

/-- `Pr[D(1^n, ρ ⊗ σ_n) = 0]`: run `D n` on `ρ ⊗ σ_n` and measure output qubit `0`. -/
noncomputable def Distinguisher.probZeroOn {k : ℕ → ℕ} (D : Distinguisher k)
    (σ : (n : ℕ) → Matrix (Bits (D.a n)) (Bits (D.a n)) ℂ) (n : ℕ)
    (ρ : Matrix (Bits (k n)) (Bits (k n)) ℂ) : ℝ :=
  probZero (D.o n) ((D.D n).chan (k n + D.a n) (D.o n) (tensorState ρ (σ n)))

/-- **EFI pair** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version
sha256 9e357a00…, Definition 5.5 ([BCQ23, Definition 7]), p. 43 (PDF p. 45)): "An EFI pair is a
family `{ρ_{0,n}, ρ_{1,n}}_{n∈ℕ}` of pairs of mixed states satisfying:
1. Efficient (E) generation. A uniform quantum polynomial-time algorithm `G`, on input
   `(1^n, b)`, outputs `ρ_{b,n}` for each `b ∈ {0, 1}`.
2. Statistical farness (F). There is a polynomial `q ≥ 1` such that
   `TD(ρ_{0,n}, ρ_{1,n}) ≥ 1/q(n)` for all sufficiently large `n`.
3. Computational indistinguishability (I). For every quantum polynomial-time distinguisher `D`
   with polynomial-size quantum advice `{σ_n}_n`, the advantage
   `|Pr[D(1^n, ρ_{0,n} ⊗ σ_n) = 0] − Pr[D(1^n, ρ_{1,n} ⊗ σ_n) = 0]|` is negligible in `n`."

`IsEFIPair k G` says that the states `ρ_{b,n} = genState k G n b` on `k(n)` qubits form an EFI
pair: (E) `UniformGen k G`; (F) a polynomial `q ∈ ℕ[X]` with `q(n) ≥ 1` for every `n` and
`1/q(n) ≤ TD(ρ_{0,n}, ρ_{1,n})` eventually; (I) for every polynomial-time distinguisher `D` and
every advice family `σ` (each `σ_n` a density matrix — positive semidefinite, trace one — on the
`a(n)` advice qubits, otherwise arbitrary), the advantage is negligible.

**Formalization Note** `b = 0` is `false`. Negligibility is the published
`QAdvFew.PoQOracle.Negligible` (`ν ≥ 0` and `ν(n) ≤ n^{−c}` eventually, for every `c > 0`),
equivalent for a nonnegative `ν` to the paper's p. 8 definition ("`ν(n) < 1/p(n)` for all
sufficiently large `n`, for every positive polynomial `p`"). The trace distance is the published
`DimFreeShadow.traceDistance` (`½‖ρ − σ‖₁`). -/
def IsEFIPair (k : ℕ → ℕ) (G : ℕ → Bool → Circuit) : Prop :=
  UniformGen k G ∧
  (∃ q : Polynomial ℕ, (∀ n, 1 ≤ q.eval n) ∧
    ∀ᶠ n in Filter.atTop, 1 / ((q.eval n : ℕ) : ℝ) ≤
      DimFreeShadow.traceDistance (genState k G n false) (genState k G n true)) ∧
  ∀ D : Distinguisher k, D.IsQPT →
    ∀ σ : (n : ℕ) → Matrix (Bits (D.a n)) (Bits (D.a n)) ℂ,
      (∀ n, (σ n).PosSemidef ∧ (σ n).trace = 1) →
      Negligible (fun n => |D.probZeroOn σ n (genState k G n false) -
        D.probZeroOn σ n (genState k G n true)|)

/-- **"EFI pairs exist"** (Theorem 1.5, p. 43): some generator `G` (with output widths `k`)
yields an EFI pair. -/
def EFIPairsExist : Prop := ∃ (k : ℕ → ℕ) (G : ℕ → Bool → Circuit), IsEFIPair k G

end Supplement

end UnitaryQIPPSPACE


