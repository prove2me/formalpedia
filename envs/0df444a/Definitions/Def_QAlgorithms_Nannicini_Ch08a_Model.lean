-- Prove2me | Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
-- name    : QAlgorithms_Nannicini_Ch08a_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:51:31.049811+00:00
-- url     : https://prove2.me/theorems/ce17de9c-33ee-4595-b9cb-c0b38f7db9c6
-- title:
--   Nannicini Ch08a: supporting definitions
-- statement:
--   Nannicini, Chapter 8 (first part): mirror descent, MMWU, the MMWU SDP solver
--
--   ## QAlgorithms.Nannicini.fixedPointVal
--
--   For natural numbers $p,f$ and any $p$-bit string $z$, let $\operatorname{bits}(z)=\sum_{i=0}^{p-1}\mathbf{1}_{z_i=\mathrm{true}}2^{p-1-i}$, so the first bit is most significant. This returns $(\operatorname{bits}(z)-2^{p-1})/2^f$ as a real number. The exponent uses natural subtraction truncated at zero: when $p=0$ the unique empty string has value zero and the result is $-1/2^f$. The denominator is always positive.
--
--   ## QAlgorithms.Nannicini.IsFixedPointValueOracle
--
--   For natural numbers $m,p,f,g$, real values $t_j$ indexed by $0\le j<m$, real tolerance $\theta$, and complex square matrix $U$ on $\ell+p+g$ wires with $\ell=\operatorname{clog}_2(m)$ the natural ceiling logarithm, this requires unitarity of $U$ and existence of a $p$-bit code for each $j$ such that $|t_j-(\operatorname{bits}(\operatorname{code}_j)-2^{p-1})/2^f|\le\theta$ for every $j$. For each $j$ it additionally requires existence of a norm-one complex vector $\psi_j$ on $g$-bit strings such that applying $U$ to the basis string consisting of the most-significant-first $\ell$-bit encoding of $j$ modulo $2^\ell$, followed by $p$ false bits then $g$ false bits, gives amplitude $\psi_j(v)$ at the concatenation of that same address, the selected code, and $v$, and amplitude zero at any string with a different address-code prefix. The entire code family is chosen before the per-address garbage vectors; other inputs are restricted only by unitarity. There is no positivity requirement on $\theta$. At $m=0$ the code exists vacuously and all address-indexed requirements disappear, leaving unitarity alone. Zero code or garbage width is allowed; the subtraction $p-1$ is truncated, giving encoded value $-1/2^f$ for $p=0$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Nannicini/Ch08a.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Adiabatic
/-!
# Nannicini, Chapter 8 (first part): mirror descent, MMWU, the MMWU SDP solver

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §8.1.2–§8.3.1. Matrices are `n × n` complex matrices indexed by `Fin n`; the
source's 1-based indices `j = 1, …, m` are `Fin m` (0-based), so the source's `A^(1)`, `b_1`,
`e_1` sit at index `0`. Traces of products of Hermitian matrices are real and are written with
`.re`. Iteration indices `t` are the source's, 1-based. The frozen objects used are
`gibbsState`, `mmwuIterate`, `qRelEntropy`, `IsEntropicMirrorDescent` and the namespace
`QAlgorithms.SDP` (`PrimalFeasible`, `DualFeasible`, `IsDualOptimal`, `picPolytope`,
`IsPICOracle`, `mmwuSDP`, `genPicPolytope`).
-/

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

open scoped ComplexOrder






/-- Chunk-local (Nannicini p.195, Prop. 8.21: the register `|ã_j⟩`). The source does not say how a
real number is held in a register; this fixes the word-size model: a `p`-qubit register `z` holds
the offset-binary fixed-point number `(bitsToNat z − 2^{p−1}) / 2^f` (most significant bit first,
`f` fractional bits). -/
noncomputable def fixedPointVal (p f : ℕ) (z : Qubits p) : ℝ :=
  ((bitsToNat z : ℝ) - 2 ^ (p - 1)) / 2 ^ f

/-- Chunk-local (Nannicini p.195, Prop. 8.21: the circuit `U`). `U` is a unitary on an index
register of `⌈log₂ m⌉` qubits, a `p`-qubit value register and a `g`-qubit garbage register with
`U|j⟩|0⟩|0⟩ = |j⟩|ã_j⟩|ψ_j⟩` for every `j ∈ [m]` (`j` written in binary, `natToBits`), where
`ã_j` is a fixed-point number (`fixedPointVal p f`) with `|t_j − ã_j| ≤ θ` and `ψ_j` is a unit
vector. With `θ = 0` it is an exact data oracle. -/
def IsFixedPointValueOracle {m : ℕ} (p f g : ℕ) (t : Fin m → ℝ) (θ : ℝ)
    (U : Matrix (Qubits (Nat.clog 2 m + p + g)) (Qubits (Nat.clog 2 m + p + g)) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Qubits (Nat.clog 2 m + p + g)) ℂ ∧
    ∃ code : Fin m → Qubits p, (∀ j, |t j - fixedPointVal p f (code j)| ≤ θ) ∧
      ∀ j : Fin m, ∃ ψ : EuclideanSpace ℂ (Qubits g), IsState ψ ∧
        act U (ket (Fin.append (Fin.append (natToBits (Nat.clog 2 m) j) (fun _ : Fin p => false))
            (fun _ : Fin g => false))) =
          WithLp.toLp 2 fun z : Qubits (Nat.clog 2 m + p + g) =>
            if (fun i => z (Fin.castAdd g i)) = Fin.append (natToBits (Nat.clog 2 m) j) (code j)
            then ψ (fun l => z (Fin.natAdd (Nat.clog 2 m + p) l)) else 0


end QAlgorithms.Nannicini


