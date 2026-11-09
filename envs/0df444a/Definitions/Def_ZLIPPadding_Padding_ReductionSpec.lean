-- Prove2me | Definitions.Def_ZLIPPadding_Padding_ReductionSpec
-- name    : ZLIPPadding_Padding_ReductionSpec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:31.997022+00:00
-- url     : https://prove2.me/theorems/5c4963c7-cfea-4c31-9ea9-1cc48ce217ac
-- title:
--   Uniform executable reduction and all three correctness specifications
-- statement:
--   A reduction witness contains three finite programs and three natural-coefficient polynomial resource bounds, fixed before the input and the oracle. The complete specification quantifies over every real $0<\delta<1$ and uses one dyadic request, chosen independently of all matrices, dimensions and oracle rules. For every promised $G$ and every correct Gram-only oracle, it requires executable realization of the defined vector, basis and sampler laws, halting on every supported trace, only valid dimension-$N$ queries, and uniform bit-cost bounds.
--
--   The vector output is correct or failure, has success at least $1-\delta/2$, and its trace has at most $\lceil(2N/n)\ln(2/\delta)\rceil$ calls. The basis output is correct or failure and succeeds at least $1-\delta/2$, with polynomially many calls. The sampler succeeds at least $1-\delta$ and satisfies
--   $$\Pr[\text{output}=z]=\frac{\Pr[\text{success}]}{2n}\quad(z^TGz=1).$$
--   This formulation avoids conditioning on zero probability. It also specifies the same exact conditional law for every fixed recovered basis. The complete specification is the goal conclusion, never an assumed property of an input object.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 28, 31–32 (PDF pp. 29, 32–33), Theorem 7.1 and §§7.5–7.7

import Definitions.Def_ZLIPPadding_Padding_Algorithms

namespace ZLIPPadding.Padding
noncomputable section
open scoped ENNReal

/-- Only valid dimension-N queries, with every branch halting within its bit bound. -/
def ExecutableLaw {n : ℕ} {α : Type} (P : Program) (A : Oracle)
    (G : ZMat n) (N b u B : ℕ) (decode : Bits → Option α)
    (μ : PMF (Option α)) : Prop :=
  decodedRun decode P A B (encRequest G b u) = μ ∧
  ∀ c, execute P A B (encRequest G b u) c ≠ 0 →
    TraceBound B c ∧ ∀ H ∈ c.requests, H.1 = N ∧ ValidGram H.2

def OneSided {α : Type} (μ : PMF (Option α)) (Good : α → Prop) : Prop :=
  ∀ x, μ (some x) ≠ 0 → Good x

def Success {α : Type} (μ : PMF (Option α)) : ℝ := prob μ {x | x ≠ none}

/-- Pointwise conditional uniformity, stated without dividing by a possibly zero success mass. -/
def UniformUnits {n : ℕ} (G : ZMat n) (μ : PMF (Option (ZVec n))) : Prop :=
  OneSided μ (UnitAnswer G) ∧
  ∀ z, UnitAnswer G z → μ (some z) = mass μ {x | x ≠ none} / (2*n : ℝ≥0∞)

def sourceCap (n N : ℕ) (δ : ℝ) : ℕ :=
  ⌈(2*(N : ℝ)/(n : ℝ))*Real.log (2/δ)⌉₊

def sizeParameter {n : ℕ} (G : ZMat n) (N b u : ℕ) : ℕ :=
  (encGram G).length + N + b + u + 1

/-- One tuple of finite codes and polynomials, fixed before every input and every oracle rule. -/
structure ReductionCode where
  vector : Program
  basis : Program
  sampler : Program
  vectorBound : Polynomial ℕ
  basisBound : Polynomial ℕ
  samplerBound : Polynomial ℕ

/-- This predicate is the theorem's conclusion, never a hypothesis on the input model.
The dyadic request is chosen once for δ, independently of G, n, hidden factors and oracles. -/
def FullReduction (Γ : ℕ → ℝ) (R : RandomizerCode) (D : DimensionCode)
    (C : ReductionCode) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ b u : ℕ,
    0 < u ∧ u ≤ 32 ∧ b = ⌈Real.log (2/δ) / Real.log 2⌉₊ + 3 ∧
    0 < errorBudget b u ∧ errorBudget b u < 1 ∧
    7*δ/8 ≤ (errorBudget b u : ℝ) ∧ (errorBudget b u : ℝ) ≤ δ ∧
    ∀ n (G : ZMat n), ValidGram G → ∀ A : Oracle, CorrectOracle Γ A →
      let N := D.dimension n
      let s := sizeParameter G N b u
      let V := exactVectorLaw R A G N b u
      let W := basisLaw R A G N b u
      let S := samplerLaw R A G N b u
      ExecutableLaw C.vector A G N b u (C.vectorBound.eval s) (decVec n) V ∧
      OneSided V (UnitAnswer G) ∧ Success V ≥ 1-δ/2 ∧
      (∀ c, execute C.vector A (C.vectorBound.eval s) (encRequest G b u) c ≠ 0 →
        c.requests.length ≤ sourceCap n N δ) ∧
      ExecutableLaw C.basis A G N b u (C.basisBound.eval s) (decMat n) W ∧
      OneSided W (BasisAnswer G) ∧ Success W ≥ 1-δ/2 ∧
      ExecutableLaw C.sampler A G N b u (C.samplerBound.eval s) (decVec n) S ∧
      Success S ≥ 1-δ ∧ UniformUnits G S ∧
      (∀ V₀ : ZMat n, BasisAnswer G V₀ →
        UniformUnits G (sampleGivenBasis V₀ b) ∧ Success (sampleGivenBasis V₀ b) ≥ 1-δ/2)

end
end ZLIPPadding.Padding


