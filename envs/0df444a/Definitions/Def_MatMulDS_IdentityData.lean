-- Prove2me | Definitions.Def_MatMulDS_IdentityData
-- name    : MatMulDS_IdentityData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:24.73447+00:00
-- url     : https://prove2.me/theorems/b1981162-95bd-4b55-b4f8-73baadebb969
-- title:
--   Approximate bilinear identities: private maps, weights, score, rates
-- statement:
--   An **approximate bilinear identity** for a block tensor with products $P$ consists of matrices $U,V,C$ with entries in $\mathbb Q[\varepsilon]$ and an integer $h\ge0$ such that
--   $$\sum_{p}(Ux)_p(Vy)_p(C^{\mathsf T}z)_p=\varepsilon^hT+O(\varepsilon^{h+1}),$$
--   and the products relevant to each output $o$, those with $C_{op}\neq0$, all have the same coefficient $\varepsilon^{e(o)}$.
--
--   For such an identity:
--
--   1. a **private map** is an injective $\rho:O\to P$ with $\rho(o)$ relevant to $o$; the identity is **bijective** if $|O|=|P|$;
--   2. weights are **compatible** if they are nonnegative, $\mathrm{wt}(p)\le\mathrm{wt}(\rho(o))$ for relevant $p$, and $\mathrm{wt}(\rho(o))$ depends only on the block of $o$; they are **strict** if integer-valued with strict inequality for $p\neq\rho(o)$;
--   3. it is **$\varepsilon$-homogeneous** if each column of $U,V$ is a power of $\varepsilon$ times a rational vector;
--   4. a **central block** has one output $w_0$, whose coefficients are all $1$, with the sum of all products equal to $\varepsilon^h$ times its inner product, with no error term.
--
--   Its **score** is $\sigma=2\,\mathrm{len}(U)/(2\log P_{\mathrm{base}}-\log|O|)$, and for a distribution $\pi$ on $O$ the rates are $\nu=H(\pi)/2\mathrm{len}(\pi)$, $E=(2\log P_{\mathrm{base}}-H(\pi))/2\mathrm{len}(\pi)$, $\Gamma=(H(\pi)-f)/\mathrm{len}(\pi)$, $Q=\xi/\mathrm{len}(\pi)$, with $f,\xi$ as in (5.4). The tensor square has encoding matrices $U\otimes U,V\otimes V$, decoding matrix $C\otimes C$ and degree $2h$.
--
--   **Formalization Note** The source writes $\mu=\sum_\beta\pi(\beta)\mathrm{wt}(\beta)$; by compatibility this equals the expected weight $\sum_o\pi(o)\mathrm{wt}(\rho(o))$ used here.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), (3.1), p.13 (PDF p.15); §5.3–5.5, pp.28–31 (PDF pp.30–33); Definition 5.6, p.33 (PDF p.35); §6.2, p.38 (PDF p.40); App. A, pp.66–77 (PDF pp.68–79)

import Mathlib
import Definitions.Def_MatMulDS_BlockTensor

set_option autoImplicit false

open Polynomial

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- The data of an approximate bilinear identity with products `P`: the encoding matrices `U`, `V` and the
decoding matrix `C`, with entries polynomials in the indeterminate `ε` with rational coefficients (§3, p.13;
§5.3, p.28), and the degree `h`. -/
structure IdentityData (I K J P : Type) where
  U : P → I × K → ℚ[X]
  V : P → K × J → ℚ[X]
  C : I × J → P → ℚ[X]
  h : ℕ

namespace IdentityData

variable (D : IdentityData I K J P)

/-- **The data is an approximate bilinear identity for the block tensor** (3.1), p.13, in the form of §5.3,
p.28, and App. A.1, p.66:
`Σ_i (Ux)_i (Vy)_i (C^T z)_i = ε^h T + O(ε^{h+1})`, compared coefficient by coefficient in the variables, and
the relevant products of each output all appear with the same coefficient `ε^{e(o)}` ("we assume this property
throughout", p.66).

**Formalization Note** `U`, `V`, `C` matter only at variables and outputs of `T`. Comparing coefficients of
`x_a y_b z_o` in (3.1) gives exactly the divisibility here, since the left-hand side of (3.1) is trilinear. -/
def Computes (T : BlockTensor I K J B) : Prop :=
  (∀ o ∈ T.outputs, ∃ e : ℕ, ∀ p, D.C o p = 0 ∨ D.C o p = X ^ e) ∧
  ∀ o ∈ T.outputs, ∀ a ∈ T.leftVars, ∀ b ∈ T.rightVars,
    open Classical in
    (X : ℚ[X]) ^ (D.h + 1) ∣
      (∑ p, D.C o p * D.U p a * D.V p b) - X ^ D.h * (if T.Incident a b o then 1 else 0)

/-- The set `Prel(o)` of relevant products of an output: those with nonzero decoding coefficient. -/
noncomputable def Prel (o : I × J) : Finset P :=
  open Classical in Finset.univ.filter fun p => D.C o p ≠ 0

/-- A **private map** (p.28): an injective `ρ : O → P` with `ρ(o) ∈ Prel(o)`. -/
def IsPrivateMap (T : BlockTensor I K J B) (ρ : T.Out → P) : Prop :=
  Function.Injective ρ ∧ ∀ o : T.Out, ρ o ∈ D.Prel o.1

/-- **Compatible weights** (p.29; (W1), (W2), p.73): `wt` is nonnegative, the private product of an output is
one of its heaviest relevant products, and `wt(ρ(o))` depends only on the block of `o`. -/
def IsCompatible (T : BlockTensor I K J B) (ρ : T.Out → P) (wt : P → ℝ) : Prop :=
  (∀ p, 0 ≤ wt p) ∧
  (∀ (o : T.Out), ∀ p ∈ D.Prel o.1, wt p ≤ wt (ρ o)) ∧
  (∀ (β : B) (o o' : T.Out), o.1 ∈ T.blockOutputs β → o'.1 ∈ T.blockOutputs β → wt (ρ o) = wt (ρ o'))

/-- **Strict weights** (p.30; p.74): integer values, and the inequality (W1) is strict for all
`p ≠ ρ(o)`. -/
def IsStrict (T : BlockTensor I K J B) (ρ : T.Out → P) (wt : P → ℝ) : Prop :=
  (∀ p, ∃ n : ℤ, wt p = n) ∧ ∀ (o : T.Out), ∀ p ∈ D.Prel o.1, p ≠ ρ o → wt p < wt (ρ o)

/-- **ε-homogeneous** (p.38): every column of `U` and `V` is a power of `ε` times a rational vector. -/
def IsHomogeneous (T : BlockTensor I K J B) : Prop :=
  (∃ (Ub : P → I × K → ℚ) (g : I × K → ℕ), ∀ p, ∀ a ∈ T.leftVars, D.U p a = Polynomial.C (Ub p a) * X ^ g a) ∧
  (∃ (Vb : P → K × J → ℚ) (g' : K × J → ℕ), ∀ p, ∀ b ∈ T.rightVars, D.V p b = Polynomial.C (Vb p b) * X ^ g' b)

/-- A **central output** (6.2), p.36: all decoding coefficients of `w₀` are one, and the sum of all products is
`ε^h` times the inner product of `w₀`, with no error term. -/
def IsCentralOutput (T : BlockTensor I K J B) (w₀ : I × J) : Prop :=
  (∀ p, D.C w₀ p = 1) ∧
  ∀ a ∈ T.leftVars, ∀ b ∈ T.rightVars,
    open Classical in
    (∑ p, D.U p a * D.V p b) = X ^ D.h * (if T.Incident a b w₀ then 1 else 0)

/-- A **central block** (p.38): one of the blocks has only one output, and this output is a central output. -/
def IsCentralBlock (T : BlockTensor I K J B) (β₀ : B) (w₀ : I × J) : Prop :=
  T.blockOutputs β₀ = {w₀} ∧ D.IsCentralOutput T w₀

/-- The identity of the tensor square (§6, p.35): encoding matrices `U ⊗ U` and `V ⊗ V`, decoding matrix
`C ⊗ C`, degree `2h`. -/
noncomputable def square : IdentityData (I × I) (K × K) (J × J) (P × P) where
  U p a := D.U p.1 (a.1.1, a.2.1) * D.U p.2 (a.1.2, a.2.2)
  V p b := D.V p.1 (b.1.1, b.2.1) * D.V p.2 (b.1.2, b.2.2)
  C o p := D.C (o.1.1, o.2.1) p.1 * D.C (o.1.2, o.2.2) p.2
  h := 2 * D.h

end IdentityData

/-- **Bijective identity** (p.28): `|O| = P_base`. -/
def IsBijective (T : BlockTensor I K J B) (P : Type) [Fintype P] : Prop :=
  Fintype.card P = T.outputs.card

/-- `log P_base`, with `P_base = |P|`. -/
noncomputable def logP (P : Type) [Fintype P] : ℝ := Real.log (Fintype.card P)

/-- **The score** of an identity (Definition 5.6, p.33; Definition A.9, p.80):
`σ = 2 len(U) / (2 log P_base − log |O|)` with `len(U) = (1/|O|) Σ_o log len(o)`.

**Formalization Note** If `2 log P_base = log |O|`, which by Lemma A.2 means `P_base = |O| = 1`, the output has
length one and the value is `0/0 = 0` in Lean, which is the score of an identity with no output of length at
least two. -/
noncomputable def score (T : BlockTensor I K J B) (P : Type) [Fintype P] : ℝ :=
  2 * ((1 / (T.outputs.card : ℝ)) * ∑ o ∈ T.outputs, Real.log (T.len o)) /
    (2 * logP P - Real.log (T.outputs.card))

/-! ## Distributions and rates (§5.4, §5.5, App. A.2, A.3) -/

section Rates

variable (T : BlockTensor I K J B)

/-- `π` is a probability distribution on `O` with rational values that is uniform within each block (p.29; p.68).
Only its values on `O` matter. -/
def IsBlockDistribution (π : I × J → ℚ) : Prop :=
  (∀ o ∈ T.outputs, 0 ≤ π o) ∧ (∑ o ∈ T.outputs, π o = 1) ∧
  ∀ β, ∀ o ∈ T.blockOutputs β, ∀ o' ∈ T.blockOutputs β, π o = π o'

/-- `π(β) = Σ_{o∈β} π(o)` (p.68). -/
def piBlock (π : I × J → ℚ) (β : B) : ℚ := ∑ o ∈ T.blockOutputs β, π o

/-- `L` is **admissible** if `Lπ(β)` is an integer for every block `β` (p.29; p.68). -/
def IsAdmissible (π : I × J → ℚ) (L : ℕ) : Prop :=
  ∀ β, ∃ n : ℕ, (L : ℚ) * piBlock T π β = n

/-- The entropy `H(π)`, with natural logarithms (p.14 of the paper's notation). -/
noncomputable def entropy (π : I × J → ℚ) : ℝ := ∑ o ∈ T.outputs, Real.negMulLog (π o : ℝ)

/-- `len(π) = Σ_o π(o) log len(o)` (p.29; (A.3), p.68). -/
noncomputable def lenPi (π : I × J → ℚ) : ℝ := ∑ o ∈ T.outputs, (π o : ℝ) * Real.log (T.len o)

variable {T}

/-- `µ`: the expected weight of the private product of a random output drawn from `π` (p.30; p.74).

**Formalization Note** The paper writes `µ = Σ_β π(β) wt(β)`; by (W2) this is the same number, and this form
needs no choice of an output per block. -/
noncomputable def mu (π : I × J → ℚ) (ρ : T.Out → P) (wt : P → ℝ) : ℝ :=
  ∑ o : T.Out, (π o.1 : ℝ) * wt (ρ o)

/-- `f = log Σ_p e^{−θ wt(p)} + θ η_pre`, (5.4), p.31; (A.18), p.76. -/
noncomputable def fRate (wt : P → ℝ) (θ η : ℝ) : ℝ :=
  Real.log (∑ p, Real.exp (-θ * wt p)) + θ * η

variable (T)

/-- The outputs of block `β`, as outputs. -/
def outsOf (β : B) : Finset T.Out := Finset.univ.filter fun o => o.1 ∈ T.blockOutputs β

omit [Fintype I] [Fintype K] [Fintype J] [DecidableEq B] [Fintype P] [DecidableEq P] in
theorem outsOf_nonempty (β : B) : (outsOf T β).Nonempty := by
  obtain ⟨i, hi⟩ := T.rows_nonempty β
  obtain ⟨j, hj⟩ := T.cols_nonempty β
  have h : (i, j) ∈ T.blockOutputs β := Finset.mem_product.mpr ⟨hi, hj⟩
  exact ⟨⟨(i, j), Finset.mem_biUnion.mpr ⟨β, Finset.mem_univ _, h⟩⟩, by simpa [outsOf] using h⟩

variable {T}

/-- `Z_β = max_{o∈β} Σ_{p∈Prel(o)} e^{−(wt(ρ(o)) − wt(p))}`, p.31; p.76. -/
noncomputable def Zblock (D : IdentityData I K J P) (ρ : T.Out → P) (wt : P → ℝ) (β : B) : ℝ :=
  (outsOf T β).sup' (outsOf_nonempty T β) fun o =>
    ∑ p ∈ D.Prel o.1, Real.exp (-(wt (ρ o) - wt p))

/-- `ξ = Σ_β π(β) log Z_β + µ − η_pre`, (5.4), p.31; (A.18), p.76. -/
noncomputable def xiRate (D : IdentityData I K J P) (π : I × J → ℚ) (ρ : T.Out → P) (wt : P → ℝ)
    (η : ℝ) : ℝ :=
  ∑ β, ((piBlock T π β : ℚ) : ℝ) * Real.log (Zblock D ρ wt β) + mu π ρ wt - η

variable (T)

/-- The tile exponent `ν = H(π) / (2 len(π))`, (A.19), p.77. -/
noncomputable def nuRate (π : I × J → ℚ) : ℝ := entropy T π / (2 * lenPi T π)

/-- The encoding rate `E = (2 log P_base − H(π)) / (2 len(π))`, (5.5), p.31; (A.19), p.77. -/
noncomputable def eRate (P : Type) [Fintype P] (π : I × J → ℚ) : ℝ :=
  (2 * logP P - entropy T π) / (2 * lenPi T π)

/-- The table saving `Γ = (H(π) − f) / len(π)`, (5.5), p.31; (A.19), p.77. -/
noncomputable def gammaRate (π : I × J → ℚ) (f : ℝ) : ℝ := (entropy T π - f) / lenPi T π

/-- The query exponent `Q = ξ / len(π)`, (5.5), p.31; (A.19), p.77. -/
noncomputable def qRate (π : I × J → ℚ) (ξ : ℝ) : ℝ := ξ / lenPi T π

end Rates

end MatMulDS


