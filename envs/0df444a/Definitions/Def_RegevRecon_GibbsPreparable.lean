-- Prove2me | Definitions.Def_RegevRecon_GibbsPreparable
-- name    : RegevRecon_GibbsPreparable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:23.643979+00:00
-- url     : https://prove2.me/theorems/623d5e34-280f-4091-86b4-1607c2acad2d
-- title:
--   Polynomial-time coherent Gibbs sampling on the ensemble (Corollary 3, Theorem 4)
-- statement:
--   Fix $p,k,D,S,\Lambda,\beta$. **Coherent Gibbs sampling is polynomial-time** if there are a deterministic multi-stack Turing machine $M$, constants $C,K$ and one sequence $\varepsilon_n\to0$ such that for every $n$ with $k\mid nD$ and $m=nD/k$:
--
--   1. on every $(B,\tau)$ in the ensemble's support, on input $(B,\tau,\lfloor2^n\beta\rfloor)$, the machine $M$ writes within $C(n+1)^K$ steps the code of a circuit over $\{H,T,\mathrm{CNOT}\}$ with at most $C(n+1)^K$ gates and wires;
--   2. with probability at least $1-\varepsilon_n$ over $(B,\tau)$, the circuit's failure probability is at most $\varepsilon_n$, and the trace distance from its accepted, normalized state to $|\psi_\beta\rangle\otimes|\mathrm{flag}=1\rangle\otimes|0\rangle_{\mathrm{work}}$ is at most $\varepsilon_n$.
--
--   The first $nb$ wires, $b=\lceil\log_2p\rceil$, hold the bits of $x$; wire $nb$ is the flag; the rest are work wires.
--
--   **Formalization Note** The paper names no machine. The digits of $\beta$ are on the input because a finite machine cannot hold an uncomputable $\beta$, and the clause would be false for such $\beta$ without them. A fixed finite gate set excludes gates that carry real parameters. Since $\varepsilon_n<1$ eventually, the junk value of an accepted vector at failure probability $1$ cannot pass.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), Corollary 3, p.16; (42), p.17; Theorem 4, p.21

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_RegevRecon_GibbsState
import Definitions.Def_RegevRecon_Ensemble
import Definitions.Def_RegevRecon_Circ

namespace RegevRecon

open Finset Filter Topology QAlgorithms

variable {p m n : ℕ} [Fact p.Prime]

/-- The register width `b = ⌈log₂ p⌉`. -/
def regBits (p : ℕ) : ℕ := Nat.clog 2 p

/-- The basis pattern of an assignment: wires `0 ≤ w < n b` hold the bits of `(x j).val` (wire
`j b + i` is bit `i`), wire `n b` (the flag) is `1`, all other (work) wires are `0`. -/
def gibbsBasis (N : ℕ) (x : Fin n → ZMod p) : Qubits N := fun w =>
  if h : w.val < n * regBits p then
    (x ⟨w.val / regBits p, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)⟩).val.testBit
      (w.val % regBits p)
  else decide (w.val = n * regBits p)

/-- **The target vector** `|ψ_β⟩ ⊗ |flag = 1⟩ ⊗ |0⟩_work` on `N` wires, (2), p.2, (42), p.17. -/
noncomputable def gibbsTarget (N : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (β : ℝ) : EuclideanSpace ℂ (Qubits N) :=
  ∑ x : Fin n → ZMod p, ((Real.sqrt (gibbsProb B F β x) : ℝ) : ℂ) • ket (gibbsBasis N x)

/-- The state `U|0…0⟩` a circuit prepares, projected on `flag = 1` (wire `n b` reads `1`). -/
noncomputable def acceptedBranch (p n : ℕ) (c : Circ) : EuclideanSpace ℂ (Qubits c.wires) :=
  WithLp.toLp 2 fun y =>
    if ∀ w : Fin c.wires, w.val = n * regBits p → y w = true then
      act c.unitary (zeroKet c.wires) y else 0

/-- **The failure probability** `1 − ‖Π_{flag=1} U|0…0⟩‖²` of a circuit (Corollary 3, p.16; p.17: "Report
failure otherwise"). -/
noncomputable def failureProb (p n : ℕ) (c : Circ) : ℝ := 1 - ‖acceptedBranch p n c‖ ^ 2

/-- **The trace distance of the accepted, normalized state to the target**, the published `traceDistance`
of the two pure density matrices (all registers included, as in (42)). -/
noncomputable def prepDistance (c : Circ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (β : ℝ) : ℝ :=
  traceDistance
    (pureDensity ((‖acceptedBranch p n c‖⁻¹ : ℂ) • acceptedBranch p n c))
    (pureDensity (gibbsTarget c.wires B F β))

/-- **Polynomial-time coherent Gibbs sampling on the ensemble**, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), Corollary 3, p.16, and Theorem 4,
p.21: after `p, k, D, S, Λ, β` there are a deterministic multi-stack Turing machine `M`, constants `C, K` and
one sequence `ε_n → 0` such that for every `n` with `k ∣ nD` (so `m = nD/k`):

* on every `(B, τ)` of the ensemble's support, `M` writes on input `(B, τ, ⌊2ⁿβ⌋)`, within `C (n+1)^K` steps, the
  code of a circuit over the finite gate set `{H, T, CNOT}` with at most `C (n+1)^K` gates and wires;
* with probability at least `1 − ε_n` over `(B, τ)`, its failure probability and the trace distance of its
  accepted state to `|ψ_β⟩ ⊗ |flag = 1⟩ ⊗ |0⟩_work` are at most `ε_n`.

**Formalization Note** The paper names no machine. `β` is a fixed real, and its binary digits are on the input:
a machine cannot hold an uncomputable `β`, so the clause without them is false for such `β`. `M` may still depend
on `β` ("every fixed `β`"). A fixed finite gate set is the strong reading: gates with real parameters could carry
the instance's reals for free. The accepted vector is `0` only at failure probability `1`, which `failure ≤ ε_n`
excludes once `ε_n < 1`. -/
def GibbsPreparable (k : ℕ) {D : ℕ} (S : Finset (ZMod p)) (Λ : PMF (Fin D → (ZMod p)ˣ)) (β : ℝ) :
    Prop :=
  ∃ (M : Turing.TM2ComputableAux Bool Bool) (C K : ℕ) (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) ∧
    ∀ n : ℕ, k ∣ n * D →
      ∃ circ : Matrix (Fin (n * D / k)) (Fin n) (ZMod p) → (Fin (n * D / k) → ZMod p) → Circ,
        (∀ Bbar ∈ biregular k D (n * D / k) n, ∀ c : Fin n → Fin D → (ZMod p)ˣ,
          (∀ j, Λ (c j) ≠ 0) → ∀ τ : Fin (n * D / k) → ZMod p,
            HMBinPacking.OutputsWithin M (encInstance (fillMatrix Bbar c) τ β)
                (encCirc (circ (fillMatrix Bbar c) τ)) (C * (n + 1) ^ K) ∧
              (circ (fillMatrix Bbar c) τ).gates.length ≤ C * (n + 1) ^ K ∧
              (circ (fillMatrix Bbar c) τ).wires ≤ C * (n + 1) ^ K ∧
              n * regBits p + 1 ≤ (circ (fillMatrix Bbar c) τ).wires) ∧
        1 - ε n ≤ instanceProb k (n * D / k) n Λ fun B τ =>
          failureProb p n (circ B τ) ≤ ε n ∧
            prepDistance (circ B τ) B (targetSets S τ) β ≤ ε n

end RegevRecon


