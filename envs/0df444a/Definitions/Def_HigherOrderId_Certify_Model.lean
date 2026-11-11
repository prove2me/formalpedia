-- Prove2me | Definitions.Def_HigherOrderId_Certify_Model
-- name    : HigherOrderId_Certify_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:13:03.623545+00:00
-- url     : https://prove2.me/theorems/9e42006b-cb43-45cb-aae3-af1e0d8bd217
-- title:
--   The multiaffine mechanism, Θ_R and the omitted energy V, m_d, v_N and the rate r_{d,m,N}
-- statement:
--   Fix $d\ge 1$. The space $S^d_0$ consists of the symmetric $d\times d$ real matrices with zero diagonal. For $b\in\mathbb R^d$ and $Q\in\mathbb R^{d\times d}$ the **omitted energy** is
--   $$V(b,Q)=\|b\|_2^2+\tfrac12\|Q\|_F^2=\sum_i b_i^2+\tfrac12\sum_{i,j}Q_{ij}^2,$$
--   and the parameter set is $\Theta_R=\{(b,Q): Q\in S^d_0,\ V(b,Q)\le R^2\}$. At an environment mean $x\in\mathbb R^d$ the multiaffine mechanism has population value $f(x)=\tfrac12+b^\top x+\tfrac12x^\top Qx$ and gradient $\nabla f(x)=b+Qx$.
--
--   The largest admissible number of unspanned directions is $m_d=\lfloor(\sqrt{8d+1}-1)/2\rfloor$. For a budget $N$, radius $\alpha$ and noise level $\sigma$, $v_N=\sigma^2(d-m)/(N\alpha^2)$, and the rate (10) is
--   $$r_{d,m,N}=\frac{\sigma^2(d-m)}{N\alpha^2}\sqrt{d^2+m^6}.$$
--
--   A (randomized) acceptance rule on a measurable space is a measurable function with values in $[0,1]$; a deterministic $\{0,1\}$-rule is the indicator of a measurable set. The coordinates (99) of $(b,Q)$ are indexed by $[d]$ together with the pairs $i<j$; $\langle X,Y\rangle_F=\sum_{ij}X_{ij}Y_{ij}$ and $\|X\|_F$ are the Frobenius inner product and norm.
--
--   **Formalization Note.** Indices are `Fin d`; vectors are `Fin d → ℝ`. `md` uses the printed floor formula (`Nat.floor`). `ThetaIdx d = Fin d ⊕ {(i,j) // i < j}`.
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 5, Eq. (6); p. 6, Eq. (10); p. 20, Eq. (51) and m_d; p. 30, Eqs. (99)–(100)

import Mathlib

open Matrix

namespace HigherOrderId.Certify

/-!
# The multiaffine mechanism, the parameter set Θ_R, the omitted energy V and the rate r_{d,m,N}

Zhang, Yan, Qiao, Yu, *The Higher-Order Identifiability Paradox: Learning and Certifying
Hypergraph Order*, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 5, Eq. (6);
p. 6, Eq. (10); p. 20, Eq. (51) and the definition of m_d; p. 30, Eqs. (99)–(100).

Coordinates are indexed by `Fin d`; vectors of `ℝ^d` are functions `Fin d → ℝ` and
matrices are `Matrix (Fin d) (Fin d) ℝ`.
-/

/-- `Q ∈ S^d_0`: the matrix is symmetric and has zero diagonal. -/
def IsSymZeroDiag {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Q.IsSymm ∧ ∀ i, Q i i = 0

/-- The omitted energy `V(b, Q) = ‖b‖₂² + (1/2)‖Q‖_F²` of (6). -/
noncomputable def energy {d : ℕ} (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, b i ^ 2 + (1 / 2) * ∑ i, ∑ j, Q i j ^ 2

/-- `(b, Q) ∈ Θ_R`: `Q ∈ S^d_0` and `V(b, Q) ≤ R²` ((6), (51)). -/
def InTheta {d : ℕ} (R : ℝ) (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  IsSymZeroDiag Q ∧ energy b Q ≤ R ^ 2

/-- The population mean `f(x) = 1/2 + bᵀx + (1/2) xᵀQx` at an environment mean `x`. -/
noncomputable def mechValue {d : ℕ} (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : ℝ :=
  1 / 2 + b ⬝ᵥ x + (1 / 2) * (x ⬝ᵥ (Q *ᵥ x))

/-- The population gradient `∇f(x) = b + Qx`. -/
noncomputable def mechGrad {d : ℕ} (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  b + Q *ᵥ x

/-- `m_d = ⌊(√(8d + 1) − 1)/2⌋`, the printed formula. -/
noncomputable def md (d : ℕ) : ℕ :=
  ⌊(Real.sqrt (8 * (d : ℝ) + 1) - 1) / 2⌋₊

/-- `v_N = σ²k/(Nα²)` with `k = d − m`. -/
noncomputable def vN (d m N : ℕ) (α σ : ℝ) : ℝ :=
  σ ^ 2 * ((d : ℝ) - (m : ℝ)) / ((N : ℝ) * α ^ 2)

/-- The rate (10): `r_{d,m,N} = (σ²(d − m)/(Nα²)) √(d² + m⁶)`. -/
noncomputable def rate (d m N : ℕ) (α σ : ℝ) : ℝ :=
  vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6)

/-- A randomized acceptance rule: a measurable acceptance probability with values in `[0, 1]`.
A deterministic `{0,1}`-rule is the indicator of a measurable set. -/
def IsRandomizedRule {Ω : Type*} [MeasurableSpace Ω] (φ : Ω → ℝ) : Prop :=
  Measurable φ ∧ ∀ y, 0 ≤ φ y ∧ φ y ≤ 1

/-- Index set of the coordinates `ϑ = (b_1, …, b_d, {Q_ij : i < j})` of (99). -/
abbrev ThetaIdx (d : ℕ) := Fin d ⊕ {p : Fin d × Fin d // p.1 < p.2}

/-- The Frobenius inner product `⟨X, Y⟩_F = Σ_{i,j} X_ij Y_ij`. -/
def frobInner {ι κ : Type*} [Fintype ι] [Fintype κ] (X Y : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

/-- The Frobenius norm `‖X‖_F`. -/
noncomputable def frobNorm {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) : ℝ :=
  Real.sqrt (frobInner X X)

end HigherOrderId.Certify


