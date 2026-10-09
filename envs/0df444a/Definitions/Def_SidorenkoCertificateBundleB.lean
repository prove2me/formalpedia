-- Prove2me | Definitions.Def_SidorenkoCertificateBundleB
-- name    : SidorenkoCertificateBundleB
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T06:13:42.909113+00:00
-- url     : https://prove2.me/theorems/b61d96ae-2ca2-495a-afaf-34389da3fb24
-- title:
--   Sidorenko finite kernel data and conditional identities, bundle B
-- statement:
--   This interface records the data constructions and fully quantified propositions of Signs in the cited source. For every source proposition $P_\ell$, let $C_\ell$ be its one-field proof record:
--   $$C_\ell=\{h:P_\ell\}.$$
--   The carriers of the quantified vector spaces and finite state sets are restricted to the lowest type universe. Each construction requiring an earlier proposition is parameterized by its proof record. A projection recovers the recorded proof when that record is supplied; no records are instantiated by this interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Signs.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Projections.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Restrictions.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Normalization.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/LocalMoments.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/SignMoments.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Monomials.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Charts.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/GlobalMoments.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Activation.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Coefficients.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Types.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Dilution.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Pinning.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Symmetrization.lean, source definitions and theorem statements, specialized to Type 0.

import Definitions.Def_SidorenkoCertificateBundleA
set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Scalar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def characterSignIndicator (ξ : ℤ) (a : K) : ℝ :=
  if quadraticChar K a = ξ then 1 else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0665 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (ξ : ℤ) (a : K),
    0 ≤ characterSignIndicator ξ a))

theorem characterSignIndicator_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0665] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (ξ : ℤ) (a : K),
  0 ≤ characterSignIndicator ξ a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0665.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0666 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (ξ : ℤ) (a : K),
    characterSignIndicator ξ a ≤ 1))

theorem characterSignIndicator_le_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0666] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (ξ : ℤ) (a : K),
  characterSignIndicator ξ a ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0666.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0667 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) (a : K),
    2 * characterSignIndicator ξ a =
          (if a = 0 then 0 else 1) + (ξ : ℝ) * (quadraticChar K a : ℝ)))

theorem characterSignIndicator_formula [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0667] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) (a : K),
  2 * characterSignIndicator ξ a =
        (if a = 0 then 0 else 1) + (ξ : ℝ) * (quadraticChar K a : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0667.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0668 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (b : K),
    uniformMean (fun a : K => if a = b then 1 else 0) = 1 / (Fintype.card K : ℝ)))

theorem uniformMean_singleton [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0668] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (b : K),
  uniformMean (fun a : K => if a = b then 1 else 0) = 1 / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0668.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0669 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (uniformMean (fun a : K => if a = 0 then 0 else 1) = 1 - 1 / (Fintype.card K : ℝ)))

theorem uniformMean_nonzero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0669] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (uniformMean (fun a : K => if a = 0 then 0 else 1) = 1 - 1 / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0669.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0670 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K ≠ 2),
    uniformMean (fun a : K => (quadraticChar K a : ℝ)) = 0))

theorem uniformMean_character [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0670] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K ≠ 2),
  uniformMean (fun a : K => (quadraticChar K a : ℝ)) = 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0670.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0671 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K ≠ 2)
        {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    uniformMean (characterSignIndicator (K := K) ξ) =
          (1 - 1 / (Fintype.card K : ℝ)) / 2))

theorem uniformMean_characterSignIndicator [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0671] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K ≠ 2)
      {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  uniformMean (characterSignIndicator (K := K) ξ) =
        (1 - 1 / (Fintype.card K : ℝ)) / 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0671.proof certificateEvidence
end

def scalarAffineEquiv (c b : K) (hc : c ≠ 0) : K ≃ K where
  toFun a := c * (a-b)
  invFun t := t/c+b
  left_inv a := by field_simp; ring
  right_inv t := by field_simp; ring

section
attribute [local instance] certificateFintype
class ProofCertificate_0672 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (c b : K) (hc : c ≠ 0) (f : K → ℝ),
    uniformMean (fun a => f (c * (a-b))) = uniformMean f))

theorem uniformMean_affine [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0672] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (c b : K) (hc : c ≠ 0) (f : K → ℝ),
  uniformMean (fun a => f (c * (a-b))) = uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0672.proof certificateEvidence
end

end Scalar
section MatrixSign
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def symmetricSingularProb (n : ℕ) : ℝ :=
  uniformMean fun M : SymMatrix K n => if M.val.det = 0 then 1 else 0

noncomputable def symmetricSignProb (n : ℕ) (ξ : ℤ) : ℝ :=
  uniformMean fun M : SymMatrix K n => characterSignIndicator ξ M.val.det

section
attribute [local instance] certificateFintype
class ProofCertificate_0673 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
        (hM : M.val.det ≠ 0),
    uniformMean (fun a => if (symmetricBorder M z a).val.det = 0 then 1 else 0) =
          1 / (Fintype.card K : ℝ)))

theorem border_singularMean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0673] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
      (hM : M.val.det ≠ 0),
  uniformMean (fun a => if (symmetricBorder M z a).val.det = 0 then 1 else 0) =
        1 / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0673.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0674 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
        (hM : M.val.det ≠ 0) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    uniformMean (fun a => characterSignIndicator ξ (symmetricBorder M z a).val.det) =
          (1 - 1 / (Fintype.card K : ℝ)) / 2))

theorem border_signMean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0674] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
      (hM : M.val.det ≠ 0) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  uniformMean (fun a => characterSignIndicator ξ (symmetricBorder M z a).val.det) =
        (1 - 1 / (Fintype.card K : ℝ)) / 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0674.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0675 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ),
    0 ≤ symmetricSingularProb (K := K) n))

theorem symmetricSingularProb_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0675] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ),
  0 ≤ symmetricSingularProb (K := K) n)) := @OAI.SidorenkoCounterexample.ProofCertificate_0675.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0676 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (symmetricSingularProb (K := K) 0 = 0))

theorem symmetricSingularProb_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0676] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (symmetricSingularProb (K := K) 0 = 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0676.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0677 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ),
    symmetricSingularProb (K := K) (n+1) ≤
          symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ)))

theorem symmetricSingularProb_succ [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0677] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ),
  symmetricSingularProb (K := K) (n+1) ≤
        symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0677.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0678 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ),
    symmetricSingularProb (K := K) n ≤ n / (Fintype.card K : ℝ)))

theorem symmetricSingularProb_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0678] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ),
  symmetricSingularProb (K := K) n ≤ n / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0678.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0679 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ) (ξ : ℤ),
    0 ≤ symmetricSignProb (K := K) n ξ))

theorem symmetricSignProb_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0679] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ) (ξ : ℤ),
  0 ≤ symmetricSignProb (K := K) n ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0679.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0680 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ) (ξ : ℤ),
    symmetricSignProb (K := K) n ξ ≤ 1))

theorem symmetricSignProb_le_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0680] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ) (ξ : ℤ),
  symmetricSignProb (K := K) n ξ ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0680.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0681 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ) (hK : ringChar K ≠ 2)
        {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    |symmetricSignProb (K := K) (n+1) ξ - 1/2| ≤
          symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ)))

theorem symmetricSignProb_succ_error [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0681] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ) (hK : ringChar K ≠ 2)
      {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  |symmetricSignProb (K := K) (n+1) ξ - 1/2| ≤
        symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0681.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0682 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ) (hn : 0 < n) (hK : ringChar K ≠ 2)
        {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    |symmetricSignProb (K := K) n ξ - 1/2| ≤ n / (Fintype.card K : ℝ)))

theorem symmetricSignProb_error [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0682] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (n : ℕ) (hn : 0 < n) (hK : ringChar K ≠ 2)
      {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  |symmetricSignProb (K := K) n ξ - 1/2| ≤ n / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0682.proof certificateEvidence
end

end MatrixSign
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
section NondegSign
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0683 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V)
        (hBs : B.IsSymm) (hB : B.Nondegenerate)
        {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K V),
    discriminantSign B hBs = quadraticChar K (B.toMatrix b).det))

theorem discriminantSign_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0683] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V)
      (hBs : B.IsSymm) (hB : B.Nondegenerate)
      {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K V),
  discriminantSign B hBs = quadraticChar K (B.toMatrix b).det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0683.proof certificateEvidence
end

end NondegSign
section SumForms
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
def orthogonalSumForm (A : LinearMap.BilinForm K V) (B : LinearMap.BilinForm K W) :
    LinearMap.BilinForm K (V × W) :=
  A.compl₁₂ (LinearMap.fst K V W) (LinearMap.fst K V W) +
    B.compl₁₂ (LinearMap.snd K V W) (LinearMap.snd K V W)

section
attribute [local instance] certificateFintype
class ProofCertificate_0684 : Prop where
  proof : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _], (∀ (A : LinearMap.BilinForm K V)
        (B : LinearMap.BilinForm K W) (x y : V × W),
    orthogonalSumForm A B x y = A x.1 y.1 + B x.2 y.2))

@[simp]
theorem orthogonalSumForm_apply [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0684] : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _], (∀ (A : LinearMap.BilinForm K V)
      (B : LinearMap.BilinForm K W) (x y : V × W),
  orthogonalSumForm A B x y = A x.1 y.1 + B x.2 y.2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0684.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0685 : Prop where
  proof : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _], (∀ (A : LinearMap.BilinForm K V)
        (B : LinearMap.BilinForm K W) (hA : A.IsSymm) (hB : B.IsSymm),
    (orthogonalSumForm A B).IsSymm))

theorem orthogonalSumForm_isSymm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0685] : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _], (∀ (A : LinearMap.BilinForm K V)
      (B : LinearMap.BilinForm K W) (hA : A.IsSymm) (hB : B.IsSymm),
  (orthogonalSumForm A B).IsSymm)) := @OAI.SidorenkoCounterexample.ProofCertificate_0685.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0686 : Prop where
  proof : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _], (∀ (A : LinearMap.BilinForm K V)
        (B : LinearMap.BilinForm K W) (hA : A.Nondegenerate) (hB : B.Nondegenerate),
    (orthogonalSumForm A B).Nondegenerate))

theorem orthogonalSumForm_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0686] : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _], (∀ (A : LinearMap.BilinForm K V)
      (B : LinearMap.BilinForm K W) (hA : A.Nondegenerate) (hB : B.Nondegenerate),
  (orthogonalSumForm A B).Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0686.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0687 : Prop where
  proof : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _], (∀ (A : LinearMap.BilinForm K V)
        (B : LinearMap.BilinForm K W) {ι κ : Type} [Fintype ι] [Fintype κ]
        [DecidableEq ι] [DecidableEq κ] (b : Basis ι K V) (c : Basis κ K W),
    (orthogonalSumForm A B).toMatrix (b.prod c) =
          Matrix.fromBlocks (A.toMatrix b) 0 0 (B.toMatrix c)))

theorem orthogonalSumForm_matrix [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0687] : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _], (∀ (A : LinearMap.BilinForm K V)
      (B : LinearMap.BilinForm K W) {ι κ : Type} [Fintype ι] [Fintype κ]
      [DecidableEq ι] [DecidableEq κ] (b : Basis ι K V) (c : Basis κ K W),
  (orthogonalSumForm A B).toMatrix (b.prod c) =
        Matrix.fromBlocks (A.toMatrix b) 0 0 (B.toMatrix c))) := @OAI.SidorenkoCounterexample.ProofCertificate_0687.proof certificateEvidence
end

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0688 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (A B : LinearMap.BilinForm K V)
        (hA : A.IsSymm) (hB : B.IsSymm) (hS : (A+B).Nondegenerate)
        (hdim : finrank K (V ⧸ A.ker) + finrank K (V ⧸ B.ker) = finrank K V),
    discriminantSign (A+B) (hA.add hB) = discriminantSign A hA * discriminantSign B hB))

theorem discriminantSign_add [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0688] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (A B : LinearMap.BilinForm K V)
      (hA : A.IsSymm) (hB : B.IsSymm) (hS : (A+B).Nondegenerate)
      (hdim : finrank K (V ⧸ A.ker) + finrank K (V ⧸ B.ker) = finrank K V),
  discriminantSign (A+B) (hA.add hB) = discriminantSign A hA * discriminantSign B hB)) := @OAI.SidorenkoCounterexample.ProofCertificate_0688.proof certificateEvidence
end

end SumForms
section PairSign
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
variable [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0689 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (r : ℕ) (hdim : Fintype.card n = 2*r)
        (A B : Matrix n n K) (hAs : A.IsSymm) (hBs : B.IsSymm)
        (hB : B.det ≠ 0) (hAr : A.rank = r) (hCr : (A-B).rank = r),
    quadraticChar K B.det = quadraticChar K ((-1 : K)^r) *
          discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hAs) *
          discriminantSign (A-B).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hAs.sub hBs))))

theorem half_rank_pair_sign [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0689] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (r : ℕ) (hdim : Fintype.card n = 2*r)
      (A B : Matrix n n K) (hAs : A.IsSymm) (hBs : B.IsSymm)
      (hB : B.det ≠ 0) (hAr : A.rank = r) (hCr : (A-B).rank = r),
  quadraticChar K B.det = quadraticChar K ((-1 : K)^r) *
        discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hAs) *
        discriminantSign (A-B).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hAs.sub hBs)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0689.proof certificateEvidence
end

end PairSign
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
section RadicalCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0690 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (U : Submodule K V) (C : SymForm K (V ⧸ U)),
    (C.val.compl₁₂ U.mkQ U.mkQ).ker = U ↔ C.val.Nondegenerate))

theorem symFormQuotient_nondegenerate_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0690] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (U : Submodule K V) (C : SymForm K (V ⧸ U)),
  (C.val.compl₁₂ U.mkQ U.mkQ).ker = U ↔ C.val.Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0690.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0691 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0628] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (U : Submodule K V)
        (C : SymForm K (V ⧸ U)) (hC : C.val.Nondegenerate),
    discriminantSign (C.val.compl₁₂ U.mkQ U.mkQ)
          (pullback_isSymm C.val C.property U.mkQ) = discriminantSign C.val C.property))

theorem discriminantSign_pullback_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0691] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0628] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (U : Submodule K V)
      (C : SymForm K (V ⧸ U)) (hC : C.val.Nondegenerate),
  discriminantSign (C.val.compl₁₂ U.mkQ U.mkQ)
        (pullback_isSymm C.val C.property U.mkQ) = discriminantSign C.val C.property)) := @OAI.SidorenkoCounterexample.ProofCertificate_0691.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0690] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0628] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0691]
noncomputable def signedRadicalFiberEquiv (U : Submodule K V) (ξ : ℤ) :
    {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} ≃
      {C : SymForm K (V ⧸ U) // C.val.Nondegenerate ∧
        discriminantSign C.val C.property = ξ} := by
  let e : {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} ≃
      {B : {B : SymForm K V // U ≤ B.val.ker} //
        B.val.val.ker = U ∧ discriminantSign B.val.val B.val.property = ξ} :=
    { toFun := fun B => ⟨⟨B.val, le_of_eq B.property.1.symm⟩, B.property⟩
      invFun := fun B => ⟨B.val.val, B.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine e.trans ((formRadicalEquiv U).subtypeEquiv ?_)
  intro B
  let C := formRadicalEquiv U B
  have hback : C.val.compl₁₂ U.mkQ U.mkQ = B.val.val := rfl
  have hn : B.val.val.ker = U ↔ C.val.Nondegenerate := by
    rw [← hback]; exact symFormQuotient_nondegenerate_iff U C
  constructor
  · rintro ⟨hB,hξ⟩
    have hC := hn.mp hB
    refine ⟨hC, ?_⟩
    have hs := discriminantSign_pullback_nondegenerate U C hC
    change discriminantSign B.val.val B.val.property = discriminantSign C.val C.property at hs
    exact hs.symm.trans hξ
  · rintro ⟨hC,hξ⟩
    refine ⟨hn.mpr hC, ?_⟩
    have hs := discriminantSign_pullback_nondegenerate U C hC
    change discriminantSign B.val.val B.val.property = discriminantSign C.val C.property at hs
    exact hs.trans hξ
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0683]
noncomputable def nonsingularSignedMatrixEquiv (ξ : ℤ) :
    {C : SymForm K V // C.val.Nondegenerate ∧ discriminantSign C.val C.property = ξ} ≃
      {M : SymMatrix K (finrank K V) // quadraticChar K M.val.det = ξ ∧ M.val.det ≠ 0} := by
  refine (symFormMatrix K V).subtypeEquiv ?_
  intro C
  have hn : C.val.Nondegenerate ↔ (C.val.toMatrix (Module.finBasis K V)).det ≠ 0 :=
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Module.finBasis K V)
  constructor
  · rintro ⟨hC,hξ⟩
    refine ⟨?_, hn.mp hC⟩
    change quadraticChar K (C.val.toMatrix (Module.finBasis K V)).det = ξ
    rw [← discriminantSign_nondegenerate C.val C.property hC (Module.finBasis K V)]
    exact hξ
  · rintro ⟨hξ,hC⟩
    refine ⟨hn.mpr hC, ?_⟩
    rw [discriminantSign_nondegenerate C.val C.property (hn.mpr hC) (Module.finBasis K V)]
    exact hξ
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0692 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hV : finrank K V = r)
        {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    Nat.card {C : SymForm K V // C.val.Nondegenerate ∧ discriminantSign C.val C.property = ξ} =
          Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ}))

theorem nonsingularSignedForm_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0692] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hV : finrank K V = r)
      {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  Nat.card {C : SymForm K V // C.val.Nondegenerate ∧ discriminantSign C.val C.property = ξ} =
        Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ})) := @OAI.SidorenkoCounterexample.ProofCertificate_0692.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0693 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (U : Submodule K V) {r : ℕ}
        (hU : finrank K (V ⧸ U) = r) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    Nat.card {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} =
          Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ}))

theorem signedRadicalFiber_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0693] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (U : Submodule K V) {r : ℕ}
      (hU : finrank K (V ⧸ U) = r) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  Nat.card {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} =
        Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ})) := @OAI.SidorenkoCounterexample.ProofCertificate_0693.proof certificateEvidence
end

end RadicalCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section RankCard
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
noncomputable def signedNullityFiberEquiv (k : ℕ) (ξ : ℤ) :
    {B : SymForm K V // finrank K B.val.ker = k ∧ discriminantSign B.val B.property = ξ} ≃
      Σ U : DimSubspace K V k,
        {B : SymForm K V // B.val.ker = U.val ∧ discriminantSign B.val B.property = ξ} where
  toFun B := ⟨⟨B.val.val.ker, B.property.1⟩, ⟨B.val, rfl, B.property.2⟩⟩
  invFun UB := ⟨UB.2.val, by rw [UB.2.property.1]; exact UB.1.property, UB.2.property.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨U,hU⟩,⟨B,hB,hξ⟩⟩
    dsimp only
    change B.val.ker = U at hB
    subst U
    rfl

section
attribute [local instance] certificateFintype
class ProofCertificate_0694 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (k : ℕ) (_hk : k ≤ finrank K V)
        {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    Nat.card {B : SymForm K V // finrank K B.val.ker = k ∧ discriminantSign B.val B.property = ξ} =
          Nat.card (DimSubspace K V k) *
            Nat.card {M : SymMatrix K (finrank K V - k) // quadraticChar K M.val.det = ξ}))

theorem signedNullityForm_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0694] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (k : ℕ) (_hk : k ≤ finrank K V)
      {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  Nat.card {B : SymForm K V // finrank K B.val.ker = k ∧ discriminantSign B.val B.property = ξ} =
        Nat.card (DimSubspace K V k) *
          Nat.card {M : SymMatrix K (finrank K V - k) // quadraticChar K M.val.det = ξ})) := @OAI.SidorenkoCounterexample.ProofCertificate_0694.proof certificateEvidence
end

end RankCard
section LayerCard
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def matrixFormEquiv (D : ℕ) : SymMatrix K D ≃ SymForm K (Fin D → K) :=
  Equiv.subtypeEquiv Matrix.toBilin'.toEquiv
    (fun _M => Matrix.isSymm_toBilin'_iff_isSymm.symm)

section
attribute [local instance] certificateFintype
class ProofCertificate_0695 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    (signedLayer K D r ξ).card =
          Nat.card (DimSubspace K (Fin D → K) (D-r)) *
            Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ}))

theorem signedLayer_card_exact [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0695] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  (signedLayer K D r ξ).card =
        Nat.card (DimSubspace K (Fin D → K) (D-r)) *
          Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ})) := @OAI.SidorenkoCounterexample.ProofCertificate_0695.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0696 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ),
    symmetricSignProb (K := K) r ξ =
          (Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} : ℝ) /
            (Fintype.card K : ℝ)^((r+1).choose 2)))

theorem symmetricSignProb_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0696] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ),
  symmetricSignProb (K := K) r ξ =
        (Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} : ℝ) /
          (Fintype.card K : ℝ)^((r+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0696.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0697 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    layerMass K D r ξ =
          (Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ) *
            (Fintype.card K : ℝ)^((r+1).choose 2) * symmetricSignProb (K := K) r ξ /
            (Fintype.card K : ℝ)^((D+1).choose 2)))

theorem layerMass_exact [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0697] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  layerMass K D r ξ =
        (Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ) *
          (Fintype.card K : ℝ)^((r+1).choose 2) * symmetricSignProb (K := K) r ξ /
          (Fintype.card K : ℝ)^((D+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0697.proof certificateEvidence
end

end LayerCard
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section Binary
variable {K : Type} [Field K] [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0698 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (hK : ringChar K ≠ 2) (a b t : K)
        (ha : a ≠ 0) (hb : b ≠ 0),
    ∃ x y : K, a*x^2+b*y^2=t))

theorem binary_norm_surjective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0698] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (hK : ringChar K ≠ 2) (a b t : K)
      (ha : a ≠ 0) (hb : b ≠ 0),
  ∃ x y : K, a*x^2+b*y^2=t)) := @OAI.SidorenkoCounterexample.ProofCertificate_0698.proof certificateEvidence
end

end Binary
section Norms
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0699 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E)
        (hB : B.Nondegenerate) (hd : 0 < finrank K E),
    B ≠ 0))

theorem nondegenerate_ne_zero_of_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0699] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E)
      (hB : B.Nondegenerate) (hd : 0 < finrank K E),
  B ≠ 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0699.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0700 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E) {x : E}
        (hx : B x x ≠ 0),
    finrank K (B.orthogonal (K ∙ x)) + 1 = finrank K E))

theorem orthogonal_line_finrank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0700] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E) {x : E}
      (hx : B x x ≠ 0),
  finrank K (B.orthogonal (K ∙ x)) + 1 = finrank K E)) := @OAI.SidorenkoCounterexample.ProofCertificate_0700.proof certificateEvidence
end

variable [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0701 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _] [inst : Fintype K], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
        (hB : B.Nondegenerate) (hD : 2 ≤ finrank K E) (hK : ringChar K ≠ 2) (t : K),
    ∃ v : E, B v v = t))

theorem symmetric_norm_surjective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0701] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _] [inst : Fintype K], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
      (hB : B.Nondegenerate) (hD : 2 ≤ finrank K E) (hK : ringChar K ≠ 2) (t : K),
  ∃ v : E, B v v = t)) := @OAI.SidorenkoCounterexample.ProofCertificate_0701.proof certificateEvidence
end

end Norms
section Equivalences
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
def BilinEquivalent (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F) : Prop :=
  ∃ e : E ≃ₗ[K] F, ∀ x y, C (e x) (e y) = B x y

def scalarBilin (a : K) : LinearMap.BilinForm K K := a • LinearMap.mul K K

section
attribute [local instance] certificateFintype
class ProofCertificate_0702 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ (a x y : K),
    scalarBilin a x y = a*x*y))

@[simp]
theorem scalarBilin_apply [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0702] : (∀ {K : Type} [inst : Field K], (∀ (a x y : K),
  scalarBilin a x y = a*x*y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0702.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0703 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ (a : K),
    (scalarBilin a).IsSymm))

theorem scalarBilin_symm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0703] : (∀ {K : Type} [inst : Field K], (∀ (a : K),
  (scalarBilin a).IsSymm)) := @OAI.SidorenkoCounterexample.ProofCertificate_0703.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0704 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ (a : K) (ha : a≠0),
    (scalarBilin a).Nondegenerate))

theorem scalarBilin_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0704] : (∀ {K : Type} [inst : Field K], (∀ (a : K) (ha : a≠0),
  (scalarBilin a).Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0704.proof certificateEvidence
end

noncomputable def lineOrthogonalEquiv (B : LinearMap.BilinForm K E) (x : E)
    (hx : B x x ≠ 0) : (K × B.orthogonal (K ∙ x)) ≃ₗ[K] E :=
  ((LinearEquiv.toSpanNonzeroSingleton K E x (by intro h; subst x; simp at hx)).prodCongr
    (LinearEquiv.refl K (B.orthogonal (K ∙ x)))).trans
    ((K ∙ x).prodEquivOfIsCompl _ (B.isCompl_span_singleton_orthogonal hx))

section
attribute [local instance] certificateFintype
class ProofCertificate_0705 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (B : LinearMap.BilinForm K E) (x : E)
        (hx : B x x ≠ 0) (z : K × B.orthogonal (K ∙ x)),
    lineOrthogonalEquiv B x hx z = z.1 • x + z.2.val))

theorem lineOrthogonalEquiv_apply [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0705] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (B : LinearMap.BilinForm K E) (x : E)
      (hx : B x x ≠ 0) (z : K × B.orthogonal (K ∙ x)),
  lineOrthogonalEquiv B x hx z = z.1 • x + z.2.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0705.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0706 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
        (x : E) (hx : B x x ≠ 0) (z w : K × B.orthogonal (K ∙ x)),
    B (lineOrthogonalEquiv B x hx z) (lineOrthogonalEquiv B x hx w) =
          B x x * z.1 * w.1 + B z.2.val w.2.val))

theorem lineOrthogonalEquiv_form [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0706] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
      (x : E) (hx : B x x ≠ 0) (z w : K × B.orthogonal (K ∙ x)),
  B (lineOrthogonalEquiv B x hx z) (lineOrthogonalEquiv B x hx w) =
        B x x * z.1 * w.1 + B z.2.val w.2.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0706.proof certificateEvidence
end

variable [FiniteDimensional K E] [FiniteDimensional K F] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0707 : Prop where
  proof : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _]
      [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E)
        (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
        (hB : B.Nondegenerate) (hC : C.Nondegenerate)
        (e : E ≃ₗ[K] F) (he : ∀ x y, C (e x) (e y) = B x y),
    discriminantSign B hs = discriminantSign C ht))

theorem discriminantSign_isometry [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0707] : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _]
    [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E)
      (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
      (hB : B.Nondegenerate) (hC : C.Nondegenerate)
      (e : E ≃ₗ[K] F) (he : ∀ x y, C (e x) (e y) = B x y),
  discriminantSign B hs = discriminantSign C ht)) := @OAI.SidorenkoCounterexample.ProofCertificate_0707.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0708 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0685] {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _]
      [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _] [inst : Fintype K]
      [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E)
        (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
        (hB : B.Nondegenerate) (hC : C.Nondegenerate),
    discriminantSign (orthogonalSumForm B C) (orthogonalSumForm_isSymm B C hs ht) =
          discriminantSign B hs * discriminantSign C ht))

theorem discriminantSign_orthogonalSum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0708] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0685] {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _]
    [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _] [inst : Fintype K]
    [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E)
      (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
      (hB : B.Nondegenerate) (hC : C.Nondegenerate),
  discriminantSign (orthogonalSumForm B C) (orthogonalSumForm_isSymm B C hs ht) =
        discriminantSign B hs * discriminantSign C ht)) := @OAI.SidorenkoCounterexample.ProofCertificate_0708.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0709 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0703] {K : Type} [inst : Field K] [inst : Fintype K]
      [inst : DecidableEq K], (∀ (a : K) (ha : a≠0),
    discriminantSign (scalarBilin a) (scalarBilin_symm a) = quadraticChar K a))

theorem discriminantSign_scalar [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0709] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0703] {K : Type} [inst : Field K] [inst : Fintype K]
    [inst : DecidableEq K], (∀ (a : K) (ha : a≠0),
  discriminantSign (scalarBilin a) (scalarBilin_symm a) = quadraticChar K a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0709.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0710 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E)
        (hs : B.IsSymm) (hB : B.Nondegenerate) (x : E) (hx : B x x ≠ 0),
    discriminantSign B hs = quadraticChar K (B x x) *
          discriminantSign (B.restrict (B.orthogonal (K ∙ x)))
            (by constructor; intro u v; exact hs.eq u.val v.val)))

theorem discriminantSign_line_complement [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0710] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E)
      (hs : B.IsSymm) (hB : B.Nondegenerate) (x : E) (hx : B x x ≠ 0),
  discriminantSign B hs = quadraticChar K (B x x) *
        discriminantSign (B.restrict (B.orthogonal (K ∙ x)))
          (by constructor; intro u v; exact hs.eq u.val v.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0710.proof certificateEvidence
end

end Equivalences
section Classification
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
  [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0711 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (a b : K) (ha : a≠0) (hb : b≠0)
        (h : quadraticChar K a = quadraticChar K b),
    BilinEquivalent (scalarBilin a) (scalarBilin b)))

theorem scalarBilin_equivalent_of_sign [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0711] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (a b : K) (ha : a≠0) (hb : b≠0)
      (h : quadraticChar K a = quadraticChar K b),
  BilinEquivalent (scalarBilin a) (scalarBilin b))) := @OAI.SidorenkoCounterexample.ProofCertificate_0711.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0712 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E) (hD : finrank K E=1),
    ∃ e : K ≃ₗ[K] E, ∀ s t : K, B (e s) (e t) = B (e 1) (e 1)*s*t))

theorem one_dimensional_form [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0712] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E) (hD : finrank K E=1),
  ∃ e : K ≃ₗ[K] E, ∀ s t : K, B (e s) (e t) = B (e 1) (e 1)*s*t)) := @OAI.SidorenkoCounterexample.ProofCertificate_0712.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0713 : Prop where
  proof : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _]
      [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
        (hs : B.IsSymm) (ht : C.IsSymm) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
        (hE : finrank K E=1) (hF : finrank K F=1)
        (h : discriminantSign B hs = discriminantSign C ht),
    BilinEquivalent B C))

theorem one_dimensional_equivalent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0713] : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _]
    [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
      (hs : B.IsSymm) (ht : C.IsSymm) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
      (hE : finrank K E=1) (hF : finrank K F=1)
      (h : discriminantSign B hs = discriminantSign C ht),
  BilinEquivalent B C)) := @OAI.SidorenkoCounterexample.ProofCertificate_0713.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0714 : Prop where
  proof : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _]
      [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E)
        (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
        (hB : B.Nondegenerate) (hC : C.Nondegenerate) (hK : ringChar K≠2)
        (hd : finrank K E = finrank K F)
        (h : discriminantSign B hs = discriminantSign C ht),
    BilinEquivalent B C))

theorem symmetric_equivalent_of_dim_sign [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0714] : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _]
    [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K E)
      (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
      (hB : B.Nondegenerate) (hC : C.Nondegenerate) (hK : ringChar K≠2)
      (hd : finrank K E = finrank K F)
      (h : discriminantSign B hs = discriminantSign C ht),
  BilinEquivalent B C)) := @OAI.SidorenkoCounterexample.ProofCertificate_0714.proof certificateEvidence
end

end Classification
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section LinearMean
variable {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [Fintype U] [Fintype W]
section
attribute [local instance] certificateFintype
class ProofCertificate_0715 : Prop where
  proof : (∀ {K U W : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _] [inst : Fintype U] [inst : Fintype W], (∀ (f : U →ₗ[K] W) (hf : Function.Surjective f)
        (g : W → ℝ),
    uniformMean (g ∘ f) = uniformMean g))

theorem uniformMean_surjective_linear [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0715] : (∀ {K U W : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _] [inst : Fintype U] [inst : Fintype W], (∀ (f : U →ₗ[K] W) (hf : Function.Surjective f)
      (g : W → ℝ),
  uniformMean (g ∘ f) = uniformMean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_0715.proof certificateEvidence
end

end LinearMean
section Forms
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
noncomputable instance symForm_fintype : Fintype (SymForm K V) := Fintype.ofFinite _

noncomputable def formSignIndicator (ξ : ℤ) (Q : SymForm K V) : ℝ := by
  classical
  exact if Q.val.Nondegenerate then if discriminantSign Q.val Q.property = ξ then 1 else 0 else 0

noncomputable def formSingularIndicator (Q : SymForm K V) : ℝ := by
  classical
  exact if Q.val.Nondegenerate then 0 else 1

section
attribute [local instance] certificateFintype
class ProofCertificate_0716 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (b : Basis ι K V) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) (Q : SymForm K V),
    formSignIndicator ξ Q = characterSignIndicator ξ (Q.val.toMatrix b).det))

theorem formSignIndicator_matrix [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0716] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (b : Basis ι K V) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) (Q : SymForm K V),
  formSignIndicator ξ Q = characterSignIndicator ξ (Q.val.toMatrix b).det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0716.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0717 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : DecidableEq K] [inst_2 : AddCommGroup V] [inst : @_root_.Module K V _ _],
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (b : Basis ι K V) (Q : SymForm K V),
    formSingularIndicator Q = if (Q.val.toMatrix b).det=0 then 1 else 0))

theorem formSingularIndicator_matrix [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0717] : (∀ {K V : Type} [inst : Field K] [inst_1 : DecidableEq K] [inst_2 : AddCommGroup V] [inst : @_root_.Module K V _ _],
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (b : Basis ι K V) (Q : SymForm K V),
  formSingularIndicator Q = if (Q.val.toMatrix b).det=0 then 1 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0717.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0718 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (ξ : ℤ) (Q : SymForm K V),
    0 ≤ formSignIndicator ξ Q))

theorem formSignIndicator_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0718] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (ξ : ℤ) (Q : SymForm K V),
  0 ≤ formSignIndicator ξ Q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0718.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0719 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (ξ : ℤ) (Q : SymForm K V),
    formSignIndicator ξ Q ≤ 1))

theorem formSignIndicator_le_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0719] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (ξ : ℤ) (Q : SymForm K V),
  formSignIndicator ξ Q ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0719.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0720 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (Q : SymForm K V),
    0 ≤ formSingularIndicator Q))

theorem formSingularIndicator_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0720] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (Q : SymForm K V),
  0 ≤ formSingularIndicator Q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0720.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0721 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (uniformMean (formSingularIndicator (K := K) (V := V)) ≤
          (finrank K V : ℝ)/(Fintype.card K : ℝ)))

theorem formSingularMean_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0721] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (uniformMean (formSingularIndicator (K := K) (V := V)) ≤
        (finrank K V : ℝ)/(Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0721.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0722 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (hK : ringChar K ≠ 2) (hd : 0 < finrank K V)
        {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1),
    |uniformMean (formSignIndicator (K := K) (V := V) ξ)-1/2| ≤
          (finrank K V : ℝ)/(Fintype.card K : ℝ)))

theorem formSignMean_error [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0722] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (hK : ringChar K ≠ 2) (hd : 0 < finrank K V)
      {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1),
  |uniformMean (formSignIndicator (K := K) (V := V) ξ)-1/2| ≤
        (finrank K V : ℝ)/(Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0722.proof certificateEvidence
end

variable {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
section
attribute [local instance] certificateFintype
class ProofCertificate_0723 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst_3 : @_root_.Module K V _ _]
      [inst_4 : @FiniteDimensional K V _ _ _] {W : Type} [inst_5 : AddCommGroup W] [inst_6 : @_root_.Module K W _ _]
      [inst : @FiniteDimensional K W _ _ _], (∀ (f : W →ₗ[K] V) (hf : Function.Injective f)
        (g : SymForm K W → ℝ),
    uniformMean (fun Q : SymForm K V => g (symFormPull f Q)) = uniformMean g))

theorem uniformMean_restrict [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0723] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst_3 : @_root_.Module K V _ _]
    [inst_4 : @FiniteDimensional K V _ _ _] {W : Type} [inst_5 : AddCommGroup W] [inst_6 : @_root_.Module K W _ _]
    [inst : @FiniteDimensional K W _ _ _], (∀ (f : W →ₗ[K] V) (hf : Function.Injective f)
      (g : SymForm K W → ℝ),
  uniformMean (fun Q : SymForm K V => g (symFormPull f Q)) = uniformMean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_0723.proof certificateEvidence
end

end Forms
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
section Projections
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
def FormSelfAdjoint (Q : LinearMap.BilinForm K V) (T : V →ₗ[K] V) : Prop :=
  ∀ x y, Q (T x) y = Q x (T y)

section
attribute [local instance] certificateFintype
class ProofCertificate_0724 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (Q : LinearMap.BilinForm K V) (hQ : Q.Nondegenerate)
        (T : V →ₗ[K] V) (hT : FormSelfAdjoint Q T),
    T.ker = Q.orthogonal T.range))

theorem selfAdjoint_projection_ker [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0724] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (Q : LinearMap.BilinForm K V) (hQ : Q.Nondegenerate)
      (T : V →ₗ[K] V) (hT : FormSelfAdjoint Q T),
  T.ker = Q.orthogonal T.range)) := @OAI.SidorenkoCounterexample.ProofCertificate_0724.proof certificateEvidence
end

variable [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0725 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V)
        (hs : Q.IsSymm) (hQ : Q.Nondegenerate) (T : V →ₗ[K] V)
        (hT : FormSelfAdjoint Q T) (hi : IsIdempotentElem T),
    (Q.restrict T.range).Nondegenerate))

theorem selfAdjoint_projection_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0725] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V)
      (hs : Q.IsSymm) (hQ : Q.Nondegenerate) (T : V →ₗ[K] V)
      (hT : FormSelfAdjoint Q T) (hi : IsIdempotentElem T),
  (Q.restrict T.range).Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0725.proof certificateEvidence
end

noncomputable def formProjection (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) : V →ₗ[K] V :=
  U.projection (Q.orthogonal U) (Q.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hU)

section
attribute [local instance] certificateFintype
class ProofCertificate_0726 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
        (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate),
    IsIdempotentElem (formProjection Q hs U hU)))

theorem formProjection_idempotent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0726] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
      (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate),
  IsIdempotentElem (formProjection Q hs U hU))) := @OAI.SidorenkoCounterexample.ProofCertificate_0726.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0727 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
        (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate),
    (formProjection Q hs U hU).range=U))

theorem formProjection_range [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0727] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
      (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate),
  (formProjection Q hs U hU).range=U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0727.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0728 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
        (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate),
    FormSelfAdjoint Q (formProjection Q hs U hU)))

theorem formProjection_selfAdjoint [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0728] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
      (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate),
  FormSelfAdjoint Q (formProjection Q hs U hU))) := @OAI.SidorenkoCounterexample.ProofCertificate_0728.proof certificateEvidence
end

def SelfAdjointIdempotent (Q : LinearMap.BilinForm K V) :=
  {T : V →ₗ[K] V // IsIdempotentElem T ∧ FormSelfAdjoint Q T}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0726] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0727] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0724]
noncomputable def selfAdjointProjectionEquiv (Q : LinearMap.BilinForm K V)
    (hs : Q.IsSymm) (hQ : Q.Nondegenerate) :
    SelfAdjointIdempotent Q ≃ {U : Submodule K V // (Q.restrict U).Nondegenerate} where
  toFun T := ⟨T.val.range,selfAdjoint_projection_nondegenerate Q hs hQ T.val T.property.2 T.property.1⟩
  invFun U := ⟨formProjection Q hs U.val U.property,formProjection_idempotent Q hs U.val U.property,
    formProjection_selfAdjoint Q hs U.val U.property⟩
  left_inv T := by
    apply Subtype.ext
    let hU := selfAdjoint_projection_nondegenerate Q hs hQ T.val T.property.2 T.property.1
    apply ((formProjection_idempotent Q hs T.val.range hU).ext_iff T.property.1).mpr
    constructor
    · exact formProjection_range Q hs T.val.range hU
    · rw [selfAdjoint_projection_ker Q hQ _ (formProjection_selfAdjoint Q hs T.val.range hU),
        formProjection_range,←selfAdjoint_projection_ker Q hQ T.val T.property.2]
  right_inv U := Subtype.ext (formProjection_range Q hs U.val U.property)
end

end Projections
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section MatrixProjection
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
section
attribute [local instance] certificateFintype
class ProofCertificate_0729 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (T : (n → K) →ₗ[K] (n → K)),
    FormSelfAdjoint Q.toBilin' T ↔ T.toMatrix'ᵀ*Q=Q*T.toMatrix'))

theorem matrix_formSelfAdjoint_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0729] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (T : (n → K) →ₗ[K] (n → K)),
  FormSelfAdjoint Q.toBilin' T ↔ T.toMatrix'ᵀ*Q=Q*T.toMatrix')) := @OAI.SidorenkoCounterexample.ProofCertificate_0729.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0730 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q A : Matrix n n K) (hQ : Q.IsSymm) (hA : A.IsSymm),
    FormSelfAdjoint Q.toBilin' (A*Q).toLin'))

theorem matrix_selfAdjoint_of_symmetric [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0730] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q A : Matrix n n K) (hQ : Q.IsSymm) (hA : A.IsSymm),
  FormSelfAdjoint Q.toBilin' (A*Q).toLin')) := @OAI.SidorenkoCounterexample.ProofCertificate_0730.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0731 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q A : Matrix n n K) (hA : A*Q*A=A),
    IsIdempotentElem (A*Q).toLin'))

theorem matrix_projection_idempotent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0731] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q A : Matrix n n K) (hA : A*Q*A=A),
  IsIdempotentElem (A*Q).toLin')) := @OAI.SidorenkoCounterexample.ProofCertificate_0731.proof certificateEvidence
end

def CenterProjection (Q : Matrix n n K) :=
  {A : Matrix n n K // A.IsSymm ∧ A*Q*A=A}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
noncomputable def centerToProjection (Q : Matrix n n K) (hQ : Q.IsSymm)
    (A : CenterProjection Q) : SelfAdjointIdempotent Q.toBilin' :=
  ⟨(A.val*Q).toLin',matrix_projection_idempotent Q A.val A.property.2,
    matrix_selfAdjoint_of_symmetric Q A.val hQ A.property.1⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0732 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.IsSymm)
        (hdet : Q.det≠0) (T : SelfAdjointIdempotent Q.toBilin'),
    (T.val.toMatrix'*Q⁻¹).IsSymm))

theorem projection_to_center_symmetric [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0732] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.IsSymm)
      (hdet : Q.det≠0) (T : SelfAdjointIdempotent Q.toBilin'),
  (T.val.toMatrix'*Q⁻¹).IsSymm)) := @OAI.SidorenkoCounterexample.ProofCertificate_0732.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0733 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hdet : Q.det≠0)
        (T : SelfAdjointIdempotent Q.toBilin'),
    (T.val.toMatrix'*Q⁻¹)*Q*(T.val.toMatrix'*Q⁻¹)=T.val.toMatrix'*Q⁻¹))

theorem projection_to_center_identity [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0733] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hdet : Q.det≠0)
      (T : SelfAdjointIdempotent Q.toBilin'),
  (T.val.toMatrix'*Q⁻¹)*Q*(T.val.toMatrix'*Q⁻¹)=T.val.toMatrix'*Q⁻¹)) := @OAI.SidorenkoCounterexample.ProofCertificate_0733.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
noncomputable def centerProjectionEquiv (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) : CenterProjection Q ≃ SelfAdjointIdempotent Q.toBilin' where
  toFun := centerToProjection Q hQ
  invFun T := ⟨T.val.toMatrix'*Q⁻¹,projection_to_center_symmetric Q hQ hdet T,
    projection_to_center_identity Q hdet T⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val*Q).toLin'.toMatrix'*Q⁻¹=A.val
    rw [LinearMap.toMatrix'_toLin',Matrix.mul_assoc,Matrix.mul_nonsing_inv Q
      (isUnit_iff_ne_zero.mpr hdet),Matrix.mul_one]
  right_inv T := by
    apply Subtype.ext
    change (T.val.toMatrix'*Q⁻¹*Q).toLin'=T.val
    rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hdet),Matrix.mul_one,
      Matrix.toLin'_toMatrix']
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727] [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724]
noncomputable def centerSubspaceEquiv (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) : CenterProjection Q ≃
      {U : Submodule K (n → K) // (Q.toBilin'.restrict U).Nondegenerate} :=
  (centerProjectionEquiv Q hQ hdet).trans
    (selfAdjointProjectionEquiv Q.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ)
      (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hdet)))
end

end MatrixProjection
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section Range
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
section
attribute [local instance] certificateFintype
class ProofCertificate_0734 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.det≠0),
    Function.Surjective Q.toLin'))

theorem matrix_toLin_surjective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0734] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.det≠0),
  Function.Surjective Q.toLin')) := @OAI.SidorenkoCounterexample.ProofCertificate_0734.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0735 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (A Q : Matrix n n K) (hQ : Q.det≠0),
    (A*Q).toLin'.range=A.toLin'.range))

theorem matrix_mul_range [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0735] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (A Q : Matrix n n K) (hQ : Q.det≠0),
  (A*Q).toLin'.range=A.toLin'.range)) := @OAI.SidorenkoCounterexample.ProofCertificate_0735.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0736 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
      [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] {K n : Type} [inst : Field K] [inst : Fintype n]
      [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
        (A : CenterProjection Q),
    (centerSubspaceEquiv Q hQ hdet A).val=A.val.toLin'.range))

theorem centerSubspaceEquiv_val [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0736] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
    [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] {K n : Type} [inst : Field K] [inst : Fintype n]
    [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
      (A : CenterProjection Q),
  (centerSubspaceEquiv Q hQ hdet A).val=A.val.toLin'.range)) := @OAI.SidorenkoCounterexample.ProofCertificate_0736.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0737 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q A : Matrix n n K) (hQ : Q.IsSymm)
        (hdet : Q.det≠0) (hA : A.IsSymm) (hi : A*Q*A=A),
    (Q.toBilin'.restrict A.toLin'.range).Nondegenerate))

theorem center_restriction_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0737] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q A : Matrix n n K) (hQ : Q.IsSymm)
      (hdet : Q.det≠0) (hA : A.IsSymm) (hi : A*Q*A=A),
  (Q.toBilin'.restrict A.toLin'.range).Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0737.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0738 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A),
    (Q.toBilin'.restrict A.toLin'.range).compl₁₂ A.toLin'.rangeRestrict A.toLin'.rangeRestrict =
          A.toBilin'))

theorem center_form_pullback [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0738] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A),
  (Q.toBilin'.restrict A.toLin'.range).compl₁₂ A.toLin'.rangeRestrict A.toLin'.rangeRestrict =
        A.toBilin')) := @OAI.SidorenkoCounterexample.ProofCertificate_0738.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0739 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q R A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A),
    A*R*A=A ↔ ((Q-R).toBilin'.restrict A.toLin'.range)=0))

theorem center_second_equation [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0739] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q R A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A),
  A*R*A=A ↔ ((Q-R).toBilin'.restrict A.toLin'.range)=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0739.proof certificateEvidence
end

variable [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0740 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (Q A : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
        (hA : A.IsSymm) (hi : A*Q*A=A),
    discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) =
          discriminantSign (Q.toBilin'.restrict A.toLin'.range)
            ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _)))

theorem center_discriminant [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0740] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (Q A : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
      (hA : A.IsSymm) (hi : A*Q*A=A),
  discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) =
        discriminantSign (Q.toBilin'.restrict A.toLin'.range)
          ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0740.proof certificateEvidence
end

end Range
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section FormSum
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0741 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
        (hQ : Q.Nondegenerate) (U W : Submodule K V) (hc : IsCompl U W)
        (hU : (Q.restrict U).Nondegenerate) (hW : (Q.restrict W).Nondegenerate)
        (ho : ∀ u : U, ∀ w : W, Q u.val w.val=0),
    discriminantSign Q hs = discriminantSign (Q.restrict U) (hs.restrict U) *
          discriminantSign (Q.restrict W) (hs.restrict W)))

theorem discriminantSign_complements [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0741] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
      (hQ : Q.Nondegenerate) (U W : Submodule K V) (hc : IsCompl U W)
      (hU : (Q.restrict U).Nondegenerate) (hW : (Q.restrict W).Nondegenerate)
      (ho : ∀ u : U, ∀ w : W, Q u.val w.val=0),
  discriminantSign Q hs = discriminantSign (Q.restrict U) (hs.restrict U) *
        discriminantSign (Q.restrict W) (hs.restrict W))) := @OAI.SidorenkoCounterexample.ProofCertificate_0741.proof certificateEvidence
end

end FormSum
section Complement
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
section
attribute [local instance] certificateFintype
class ProofCertificate_0742 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (B A : Matrix n n K) (hB : B.det≠0)
        (hi : A*B⁻¹*A=A),
    (B-A)*B⁻¹*(B-A)=B-A))

theorem center_complement_equation [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0742] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (B A : Matrix n n K) (hB : B.det≠0)
      (hi : A*B⁻¹*A=A),
  (B-A)*B⁻¹*(B-A)=B-A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0742.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0743 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (B A : Matrix n n K) (hB : B.det≠0)
        (hi : A*B⁻¹*A=A),
    IsCompl A.toLin'.range (B-A).toLin'.range))

theorem center_complement_ranges [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0743] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (B A : Matrix n n K) (hB : B.det≠0)
      (hi : A*B⁻¹*A=A),
  IsCompl A.toLin'.range (B-A).toLin'.range)) := @OAI.SidorenkoCounterexample.ProofCertificate_0743.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0744 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (B A : Matrix n n K) (hB : B.det≠0)
        (hA : A.IsSymm) (hi : A*B⁻¹*A=A),
    ∀ u : A.toLin'.range, ∀ w : (B-A).toLin'.range, B⁻¹.toBilin' u.val w.val=0))

theorem center_complement_orthogonal [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0744] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (B A : Matrix n n K) (hB : B.det≠0)
      (hA : A.IsSymm) (hi : A*B⁻¹*A=A),
  ∀ u : A.toLin'.range, ∀ w : (B-A).toLin'.range, B⁻¹.toBilin' u.val w.val=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0744.proof certificateEvidence
end

end Complement
section Signs
variable {K n : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
section
attribute [local instance] certificateFintype
class ProofCertificate_0745 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {a : K} (ha : a≠0),
    quadraticChar K a⁻¹=quadraticChar K a))

theorem quadraticChar_inverse [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0745] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {a : K} (ha : a≠0),
  quadraticChar K a⁻¹=quadraticChar K a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0745.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0746 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype n] [inst : DecidableEq n],
      (∀ (B A : Matrix n n K) (hs : B.IsSymm) (hB : B.det≠0)
        (hA : A.IsSymm) (hi : A*B⁻¹*A=A),
    quadraticChar K B.det =
          discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) *
            discriminantSign (B-A).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hs.sub hA))))

theorem center_complement_sign [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0746] : (∀ {K n : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype n] [inst : DecidableEq n],
    (∀ (B A : Matrix n n K) (hs : B.IsSymm) (hB : B.det≠0)
      (hA : A.IsSymm) (hi : A*B⁻¹*A=A),
  quadraticChar K B.det =
        discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) *
          discriminantSign (B-A).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hs.sub hA)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0746.proof certificateEvidence
end

end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Split
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
def dualKerEquiv (φ : V →ₗ[K] K) (x : V) (hx : φ x=1) : (φ.ker × K) ≃ₗ[K] V where
  toFun p := p.1.val+p.2 • x
  invFun y := (⟨y-φ y • x, by simp [LinearMap.mem_ker,hx]⟩,φ y)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add,map_smul,smul_eq_mul,hx,mul_one,
        show φ p.1.val=0 from p.1.property,zero_add,add_sub_cancel_right]
    · simp [hx]
  right_inv y := by simp
  map_add' p q := by simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add,add_smul]; abel
  map_smul' a p := by simp only [Prod.smul_fst,Prod.smul_snd,Submodule.coe_smul,
    smul_add,smul_smul,smul_eq_mul,RingHom.id_apply]

section
attribute [local instance] certificateFintype
class ProofCertificate_0747 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
        (p : φ.ker × K),
    dualKerEquiv φ x hx p = p.1.val + p.2 • x))

@[simp]
theorem dualKerEquiv_apply [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0747] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
      (p : φ.ker × K),
  dualKerEquiv φ x hx p = p.1.val + p.2 • x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0747.proof certificateEvidence
end

def rankOneForm (φ : V →ₗ[K] K) : SymForm K V :=
  ⟨(LinearMap.mul K K).compl₁₂ φ φ, by constructor; intro x y; exact mul_comm _ _⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0748 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (x y : V),
    (rankOneForm φ).val x y = φ x * φ y))

@[simp]
theorem rankOneForm_apply [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0748] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (x y : V),
  (rankOneForm φ).val x y = φ x * φ y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0748.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0749 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ [FiniteDimensional K V] (φ : V →ₗ[K] K) (x : V) (hx : φ x=1),
    finrank K φ.ker+1=finrank K V))

theorem dualKer_finrank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0749] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ [FiniteDimensional K V] (φ : V →ₗ[K] K) (x : V) (hx : φ x=1),
  finrank K φ.ker+1=finrank K V)) := @OAI.SidorenkoCounterexample.ProofCertificate_0749.proof certificateEvidence
end

end Split
section Signs
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
noncomputable def dualKerBasis (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type} (b : Basis ι K φ.ker) : Basis (ι ⊕ PUnit.{1}) K V :=
  (b.prod (Basis.singleton PUnit.{1} K)).map (dualKerEquiv φ x hx)

section
attribute [local instance] certificateFintype
class ProofCertificate_0750 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
        {ι : Type} (b : Basis ι K φ.ker) (i : ι),
    dualKerBasis φ x hx b (.inl i) = (b i).val))

@[simp]
theorem dualKerBasis_inl [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0750] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
      {ι : Type} (b : Basis ι K φ.ker) (i : ι),
  dualKerBasis φ x hx b (.inl i) = (b i).val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0750.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0751 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
        {ι : Type} (b : Basis ι K φ.ker) (i : PUnit.{1}),
    dualKerBasis φ x hx b (.inr i) = x))

@[simp]
theorem dualKerBasis_inr [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0751] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
      {ι : Type} (b : Basis ι K φ.ker) (i : PUnit.{1}),
  dualKerBasis φ x hx b (.inr i) = x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0751.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0752 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
        (Q : SymForm K V) (a : K),
    (Q+a • rankOneForm φ).val.toMatrix (dualKerBasis φ x hx (Module.finBasis K φ.ker)) =
          borderRaw ((symFormPull φ.ker.subtype Q).val.toMatrix (Module.finBasis K φ.ker))
            (fun i => Q.val (Module.finBasis K φ.ker i).val x) (Q.val x x+a)))

theorem rankOne_shift_matrix [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0752] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
      (Q : SymForm K V) (a : K),
  (Q+a • rankOneForm φ).val.toMatrix (dualKerBasis φ x hx (Module.finBasis K φ.ker)) =
        borderRaw ((symFormPull φ.ker.subtype Q).val.toMatrix (Module.finBasis K φ.ker))
          (fun i => Q.val (Module.finBasis K φ.ker i).val x) (Q.val x x+a))) := @OAI.SidorenkoCounterexample.ProofCertificate_0752.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0753 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
        (Q : SymForm K V) (hQ : (symFormPull φ.ker.subtype Q).val.Nondegenerate)
        (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1),
    uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ)) =
          (1-1/(Fintype.card K : ℝ))/2))

theorem rankOne_shift_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0753] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
      (Q : SymForm K V) (hQ : (symFormPull φ.ker.subtype Q).val.Nondegenerate)
      (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1),
  uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ)) =
        (1-1/(Fintype.card K : ℝ))/2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0753.proof certificateEvidence
end

end Signs
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Means
variable {A B : Type} [Fintype A] [Fintype B]
section
attribute [local instance] certificateFintype
class ProofCertificate_0754 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (f : A → B → ℝ),
    uniformMean (fun a => uniformMean (f a)) =
          uniformMean (fun b => uniformMean fun a => f a b)))

theorem uniformMean_swap [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0754] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (f : A → B → ℝ),
  uniformMean (fun a => uniformMean (f a)) =
        uniformMean (fun b => uniformMean fun a => f a b))) := @OAI.SidorenkoCounterexample.ProofCertificate_0754.proof certificateEvidence
end

variable [AddGroup A]
section
attribute [local instance] certificateFintype
class ProofCertificate_0755 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A] [inst : AddGroup A], (∀ (f : A → ℝ) (t : A),
    uniformMean (fun a => f (a+t)) = uniformMean f))

theorem uniformMean_translate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0755] : (∀ {A : Type} [inst : Fintype A] [inst : AddGroup A], (∀ (f : A → ℝ) (t : A),
  uniformMean (fun a => f (a+t)) = uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0755.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0756 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B] [inst : AddGroup A], (∀ [Nonempty B] (f : A → ℝ) (t : B → A),
    uniformMean (fun a => uniformMean fun b => f (a+t b)) = uniformMean f))

theorem uniformMean_average_translate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0756] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B] [inst : AddGroup A], (∀ [Nonempty B] (f : A → ℝ) (t : B → A),
  uniformMean (fun a => uniformMean fun b => f (a+t b)) = uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0756.proof certificateEvidence
end

end Means
section ShiftError
variable {K U : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
section
attribute [local instance] certificateFintype
class ProofCertificate_0757 : Prop where
  proof : (∀ {K U : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup U]
      [inst_4 : @_root_.Module K U _ _] [inst : @FiniteDimensional K U _ _ _], (∀ (φ : U →ₗ[K] K) (x : U) (hx : φ x=1)
        (Q : SymForm K U) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    |uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ))-1/2| ≤
          formSingularIndicator (symFormPull φ.ker.subtype Q)+1/(Fintype.card K : ℝ)))

theorem rankOne_shift_error [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0757] : (∀ {K U : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup U]
    [inst_4 : @_root_.Module K U _ _] [inst : @FiniteDimensional K U _ _ _], (∀ (φ : U →ₗ[K] K) (x : U) (hx : φ x=1)
      (Q : SymForm K U) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  |uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ))-1/2| ≤
        formSingularIndicator (symFormPull φ.ker.subtype Q)+1/(Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0757.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0758 : Prop where
  proof : (∀ {K U : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup U]
      [inst_4 : @_root_.Module K U _ _] [inst : @FiniteDimensional K U _ _ _], (∀ (ξ : ℤ) (Q : SymForm K U),
    |formSignIndicator ξ Q-1/2| ≤ 1))

theorem centered_formSign_abs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0758] : (∀ {K U : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup U]
    [inst_4 : @_root_.Module K U _ _] [inst : @FiniteDimensional K U _ _ _], (∀ (ξ : ℤ) (Q : SymForm K U),
  |formSignIndicator ξ Q-1/2| ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0758.proof certificateEvidence
end

end ShiftError
section Separate
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0759 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (U W : Submodule K V)
        (hd : finrank K U=finrank K W) (hne : U≠W),
    ∃ (φ : V →ₗ[K] K) (x : U), φ x.val=1 ∧ φ.comp W.subtype=0))

theorem equal_dimension_separating_dual [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0759] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (U W : Submodule K V)
      (hd : finrank K U=finrank K W) (hne : U≠W),
  ∃ (φ : V →ₗ[K] K) (x : U), φ x.val=1 ∧ φ.comp W.subtype=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0759.proof certificateEvidence
end

end Separate
section Covariance
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0760 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (U : Submodule K V),
    symFormPull U.subtype (rankOneForm φ) = rankOneForm (φ.comp U.subtype)))

theorem rankOne_restrict [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0760] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (U : Submodule K V),
  symFormPull U.subtype (rankOneForm φ) = rankOneForm (φ.comp U.subtype))) := @OAI.SidorenkoCounterexample.ProofCertificate_0760.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0761 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (W : Submodule K V)
        (h : φ.comp W.subtype=0),
    symFormPull W.subtype (rankOneForm φ)=0))

theorem rankOne_restrict_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0761] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (φ : V →ₗ[K] K) (W : Submodule K V)
      (h : φ.comp W.subtype=0),
  symFormPull W.subtype (rankOneForm φ)=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0761.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0762 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (U W : Submodule K V)
        (hd : finrank K U=finrank K W) (hne : U≠W) (hK : ringChar K ≠ 2)
        {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    |uniformMean (fun Q : SymForm K V =>
          (formSignIndicator ξ (symFormPull U.subtype Q)-1/2) *
          (formSignIndicator ζ (symFormPull W.subtype Q)-1/2))| ≤
          (finrank K U : ℝ)/(Fintype.card K : ℝ)))

theorem restriction_covariance_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0762] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (U W : Submodule K V)
      (hd : finrank K U=finrank K W) (hne : U≠W) (hK : ringChar K ≠ 2)
      {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  |uniformMean (fun Q : SymForm K V =>
        (formSignIndicator ξ (symFormPull U.subtype Q)-1/2) *
        (formSignIndicator ζ (symFormPull W.subtype Q)-1/2))| ≤
        (finrank K U : ℝ)/(Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0762.proof certificateEvidence
end

end Covariance
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Variance
variable {A I : Type} [Fintype A] [Fintype I] [Nonempty I]
section
attribute [local instance] certificateFintype
class ProofCertificate_0763 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I], (∀ (f : I → ℝ),
    (uniformMean f)^2 = uniformMean fun i => uniformMean fun j => f i*f j))

theorem uniformMean_square [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0763] : (∀ {I : Type} [inst : Fintype I], (∀ (f : I → ℝ),
  (uniformMean f)^2 = uniformMean fun i => uniformMean fun j => f i*f j)) := @OAI.SidorenkoCounterexample.ProofCertificate_0763.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0764 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (f : A → ℝ),
    (uniformMean fun a => |f a|)^2 ≤ uniformMean fun a => (f a)^2))

theorem uniformMean_abs_sq_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0764] : (∀ {A : Type} [inst : Fintype A], (∀ (f : A → ℝ),
  (uniformMean fun a => |f a|)^2 ≤ uniformMean fun a => (f a)^2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0764.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0765 : Prop where
  proof : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I] [inst : Nonempty I], (∀ (f : I → A → ℝ) (ε : ℝ) (hε : 0≤ε)
        (hb : ∀ i a, |f i a| ≤ 1)
        (hc : ∀ i j, i≠j → |uniformMean fun a => f i a*f j a| ≤ ε) [Nonempty A],
    uniformMean (fun a => (uniformMean fun i => f i a)^2) ≤ ε+1/(Fintype.card I : ℝ)))

theorem family_variance_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0765] : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I] [inst : Nonempty I], (∀ (f : I → A → ℝ) (ε : ℝ) (hε : 0≤ε)
      (hb : ∀ i a, |f i a| ≤ 1)
      (hc : ∀ i j, i≠j → |uniformMean fun a => f i a*f j a| ≤ ε) [Nonempty A],
  uniformMean (fun a => (uniformMean fun i => f i a)^2) ≤ ε+1/(Fintype.card I : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0765.proof certificateEvidence
end

end Variance
section Restriction
variable {K V I : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I] [Nonempty I]
section
attribute [local instance] certificateFintype
class ProofCertificate_0766 : Prop where
  proof : (∀ {K V I : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype I] [inst : Nonempty I], (∀ (U : I → Submodule K V) (hinj : Function.Injective U)
        (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
        {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    uniformMean (fun Q : SymForm K V =>
          (uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2)^2) ≤
          (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ)))

theorem restriction_family_variance [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0766] : (∀ {K V I : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype I] [inst : Nonempty I], (∀ (U : I → Submodule K V) (hinj : Function.Injective U)
      (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
      {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  uniformMean (fun Q : SymForm K V =>
        (uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2)^2) ≤
        (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0766.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0767 : Prop where
  proof : (∀ {K V I : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype I] [inst : Nonempty I], (∀ (U : I → Submodule K V) (hinj : Function.Injective U)
        (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
        {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    (uniformMean (fun Q : SymForm K V =>
          |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2|))^2 ≤
          (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ)))

theorem restriction_family_L1_sq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0767] : (∀ {K V I : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype I] [inst : Nonempty I], (∀ (U : I → Submodule K V) (hinj : Function.Injective U)
      (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
      {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  (uniformMean (fun Q : SymForm K V =>
        |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2|))^2 ≤
        (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0767.proof certificateEvidence
end

end Restriction
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section AlternatingTwo
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
abbrev AltForm := {B : LinearMap.BilinForm K V // B.IsAlt}

instance altForm_finite [Finite K] [Finite V] : Finite (AltForm (K := K) (V := V)) :=
  Finite.of_injective (fun B : AltForm (K := K) (V := V) => fun x y => B.val x y) (by
    intro B C h
    apply Subtype.ext
    ext x y
    exact congrFun (congrFun h x) y)

def altFormToMap (B : AltForm (K := K) (V := V)) : V [⋀^Fin 2]→ₗ[K] K where
  toFun v := B.val (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all
    · exact B.property _
    · exact B.property _

section
attribute [local instance] certificateFintype
class ProofCertificate_0768 : Prop where
  proof : (∀ {V : Type}, (∀ (x y z : V),
    Function.update ![x,y] (0 : Fin 2) z = ![z,y]))

theorem update_vec_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0768] : (∀ {V : Type}, (∀ (x y z : V),
  Function.update ![x,y] (0 : Fin 2) z = ![z,y])) := @OAI.SidorenkoCounterexample.ProofCertificate_0768.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0769 : Prop where
  proof : (∀ {V : Type}, (∀ (x y z : V),
    Function.update ![x,y] (1 : Fin 2) z = ![x,z]))

theorem update_vec_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0769] : (∀ {V : Type}, (∀ (x y z : V),
  Function.update ![x,y] (1 : Fin 2) z = ![x,z])) := @OAI.SidorenkoCounterexample.ProofCertificate_0769.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0769] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0768]
def mapToAltForm (f : V [⋀^Fin 2]→ₗ[K] K) : AltForm (K := K) (V := V) :=
  ⟨{ toFun := fun x => {
       toFun := fun y => f ![x,y]
       map_add' := fun y z => by
         simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_add ![x,(0:V)] (1 : Fin 2) y z
       map_smul' := fun c y => by
         simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_smul ![x,(0:V)] (1 : Fin 2) c y }
     map_add' := fun x y => by
       ext z
       change f ![x+y,z] = f ![x,z]+f ![y,z]
       simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_add ![(0:V),z] (0 : Fin 2) x y
     map_smul' := fun c x => by
       ext z
       change f ![c • x,z] = c * f ![x,z]
       simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_smul ![(0:V),z] (0 : Fin 2) c x },
    fun x => f.map_eq_zero_of_eq ![x,x] (by simp : (![x,x] : Fin 2 → V) 0 = ![x,x] 1) (by decide : (0 : Fin 2) ≠ 1)⟩
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0769] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0768]
def altFormMapEquiv : AltForm (K := K) (V := V) ≃ (V [⋀^Fin 2]→ₗ[K] K) where
  toFun := altFormToMap
  invFun := mapToAltForm
  left_inv B := by apply Subtype.ext; ext x y; rfl
  right_inv f := by
    ext v
    change f ![v 0,v 1] = f v
    congr 1
    ext i
    fin_cases i <;> rfl
end

variable [FiniteDimensional K V] [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0770 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K], (Nat.card (AltForm (K := K) (V := V)) =
        Fintype.card K ^ (finrank K V).choose 2))

theorem altForm_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0770] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K], (Nat.card (AltForm (K := K) (V := V)) =
      Fintype.card K ^ (finrank K V).choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0770.proof certificateEvidence
end

end AlternatingTwo
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section OrthogonalCharts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
def canonicalOrthogonal : LinearMap.BilinForm K (V × Module.Dual K V) where
  toFun p := {
    toFun := fun q => q.2 p.1 + p.2 q.1
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro z
    change z.2 (p.1+q.1) + (p.2+q.2) z.1 =
      (z.2 p.1 + p.2 z.1) + (z.2 q.1 + q.2 z.1)
    simp
    ring
  map_smul' := by
    intro a p
    apply LinearMap.ext
    intro z
    change z.2 (a • p.1) + (a • p.2) z.1 = a * (z.2 p.1+p.2 z.1)
    simp
    ring

section
attribute [local instance] certificateFintype
class ProofCertificate_0771 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (p q : V × Module.Dual K V),
    canonicalOrthogonal p q = q.2 p.1 + p.2 q.1))

@[simp]
theorem canonicalOrthogonal_apply [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0771] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (p q : V × Module.Dual K V),
  canonicalOrthogonal p q = q.2 p.1 + p.2 q.1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0771.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0772 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], ((canonicalOrthogonal (K := K) (V := V)).IsSymm))

theorem canonicalOrthogonal_symm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0772] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], ((canonicalOrthogonal (K := K) (V := V)).IsSymm)) := @OAI.SidorenkoCounterexample.ProofCertificate_0772.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0773 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], ((canonicalOrthogonal (K := K) (V := V)).Nondegenerate))

theorem canonicalOrthogonal_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0773] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], ((canonicalOrthogonal (K := K) (V := V)).Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0773.proof certificateEvidence
end

variable [FiniteDimensional K V]
abbrev MaxOrthogonal := {L : Submodule K (V × Module.Dual K V) //
  canonicalOrthogonal.orthogonal L = L}

section
attribute [local instance] certificateFintype
class ProofCertificate_0774 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (L : MaxOrthogonal (K := K) (V := V)),
    finrank K L.val = finrank K V))

theorem maxOrthogonal_finrank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0774] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (L : MaxOrthogonal (K := K) (V := V)),
  finrank K L.val = finrank K V)) := @OAI.SidorenkoCounterexample.ProofCertificate_0774.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0775 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (U : Submodule K V) (B : AltForm (K := K) (V := U)),
    formGraph U B.val ≤ canonicalOrthogonal.orthogonal (formGraph U B.val)))

theorem formGraph_orthogonal_isotropic [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0775] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (U : Submodule K V) (B : AltForm (K := K) (V := U)),
  formGraph U B.val ≤ canonicalOrthogonal.orthogonal (formGraph U B.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0775.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0775] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0773]
noncomputable def graphMaxOrthogonal (U : Submodule K V) (B : AltForm (K := K) (V := U)) :
    MaxOrthogonal (K := K) (V := V) :=
  ⟨formGraph U B.val, by
    apply (Submodule.eq_of_le_of_finrank_eq (formGraph_orthogonal_isotropic U B) _).symm
    rw [formGraph_finrank, LinearMap.BilinForm.finrank_orthogonal canonicalOrthogonal_nondegenerate,
      Module.finrank_prod, Subspace.dual_finrank_eq, formGraph_finrank, Nat.add_sub_cancel_left]⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0776 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0775] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0773] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (U : Submodule K V),
    Function.Injective (graphMaxOrthogonal (K := K) U)))

theorem graphMaxOrthogonal_form_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0776] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0775] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0773] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (U : Submodule K V),
  Function.Injective (graphMaxOrthogonal (K := K) U))) := @OAI.SidorenkoCounterexample.ProofCertificate_0776.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0777 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (L : MaxOrthogonal (K := K) (V := V))
        {p q : V × Module.Dual K V} (hp : p ∈ L.val) (hq : q ∈ L.val),
    canonicalOrthogonal p q = 0))

theorem maxOrthogonal_pairing_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0777] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (L : MaxOrthogonal (K := K) (V := V))
      {p q : V × Module.Dual K V} (hp : p ∈ L.val) (hq : q ∈ L.val),
  canonicalOrthogonal p q = 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0777.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0778 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0775] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0773] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (hK : ringChar K ≠ 2),
    Function.Surjective (fun S : Σ U : Submodule K V, AltForm (K := K) (V := U) => graphMaxOrthogonal S.1 S.2)))

theorem graphMaxOrthogonal_surjective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0778] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0775] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0773] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (hK : ringChar K ≠ 2),
  Function.Surjective (fun S : Σ U : Submodule K V, AltForm (K := K) (V := U) => graphMaxOrthogonal S.1 S.2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0778.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0775] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0773] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0016] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0776] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0778]
noncomputable def maxOrthogonalGraphEquiv (hK : ringChar K ≠ 2) :
    (Σ U : Submodule K V, AltForm (K := K) (V := U)) ≃ MaxOrthogonal (K := K) (V := V) :=
  Equiv.ofBijective (fun S => graphMaxOrthogonal S.1 S.2) ⟨by
    rintro ⟨U,B⟩ ⟨W,C⟩ he
    have h : U = W := by
      rw [← formGraph_fst_range U B.val, ← formGraph_fst_range W C.val]
      exact congrArg (fun L : MaxOrthogonal (K := K) (V := V) =>
        L.val.map (LinearMap.fst K V (Module.Dual K V))) he
    cases h
    congr 1
    exact graphMaxOrthogonal_form_injective U he,
    graphMaxOrthogonal_surjective hK⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0779 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ [Fintype K] [Finite V] (hK : ringChar K ≠ 2),
    letI := Fintype.ofFinite (Submodule K V)
    Nat.card (MaxOrthogonal (K := K) (V := V)) =
      ∑ U : Submodule K V, (Fintype.card K)^((finrank K U).choose 2)))

theorem maxOrthogonal_card_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0779] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ [Fintype K] [Finite V] (hK : ringChar K ≠ 2),
  letI := Fintype.ofFinite (Submodule K V)
  Nat.card (MaxOrthogonal (K := K) (V := V)) =
    ∑ U : Submodule K V, (Fintype.card K)^((finrank K U).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0779.proof certificateEvidence
end

end OrthogonalCharts
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section SplitSign
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0780 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (b : Basis ι K V),
    canonicalOrthogonal.toMatrix (b.prod b.dualBasis) =
          Matrix.fromBlocks (0 : Matrix ι ι K) 1 1 0))

theorem canonicalOrthogonal_matrix [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0780] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (b : Basis ι K V),
  canonicalOrthogonal.toMatrix (b.prod b.dualBasis) =
        Matrix.fromBlocks (0 : Matrix ι ι K) 1 1 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0780.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0781 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ {ι : Type} [Fintype ι] [DecidableEq ι],
    (Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0).det = (-1 : K) ^ Fintype.card ι))

theorem hyperbolic_block_det [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0781] : (∀ {K : Type} [inst : Field K], (∀ {ι : Type} [Fintype ι] [DecidableEq ι],
  (Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0).det = (-1 : K) ^ Fintype.card ι)) := @OAI.SidorenkoCounterexample.ProofCertificate_0781.proof certificateEvidence
end

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0782 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0772] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K],
      (discriminantSign (canonicalOrthogonal (K := K) (V := V)) canonicalOrthogonal_symm =
          quadraticChar K ((-1 : K) ^ finrank K V)))

theorem canonicalOrthogonal_sign [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0782] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0772] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K],
    (discriminantSign (canonicalOrthogonal (K := K) (V := V)) canonicalOrthogonal_symm =
        quadraticChar K ((-1 : K) ^ finrank K V))) := @OAI.SidorenkoCounterexample.ProofCertificate_0782.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0783 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {E : Type} [AddCommGroup E] [Module K E]
        [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
        (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
        (r : ℕ) (hd : finrank K E = 2*r)
        (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)),
    BilinEquivalent B (canonicalOrthogonal (K := K) (V := Fin r → K))))

theorem split_form_equivalent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0783] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {E : Type} [AddCommGroup E] [Module K E]
      [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
      (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
      (r : ℕ) (hd : finrank K E = 2*r)
      (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)),
  BilinEquivalent B (canonicalOrthogonal (K := K) (V := Fin r → K)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0783.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0784 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {E : Type} [AddCommGroup E] [Module K E]
        [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
        (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
        (r : ℕ) (hd : finrank K E = 2*r)
        (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)),
    Nat.card (SymplecticLagrangian B) =
          Nat.card (MaxOrthogonal (K := K) (V := Fin r → K))))

theorem split_form_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0784] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {E : Type} [AddCommGroup E] [Module K E]
      [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
      (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
      (r : ℕ) (hd : finrank K E = 2*r)
      (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)),
  Nat.card (SymplecticLagrangian B) =
        Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0784.proof certificateEvidence
end

end SplitSign
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module Filter
noncomputable def grassmannFactor (D k : ℕ) (q : ℝ) : ℝ :=
  ∏ i : Fin k, (1 - 1 / q^(D-i.val)) / (1 - 1 / q^(k-i.val))

section
attribute [local instance] certificateFintype
class ProofCertificate_0785 : Prop where
  proof : ((∀ (D k i : ℕ) (hik : i ≤ k) (hkD : k ≤ D)
        (q : ℝ) (hq : q ≠ 0),
    (q^D - q^i)/(q^k-q^i) = q^(D-k) *
          ((1 - 1/q^(D-i)) / (1 - 1/q^(k-i)))))

theorem grassmann_single_factor [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0785] : ((∀ (D k i : ℕ) (hik : i ≤ k) (hkD : k ≤ D)
      (q : ℝ) (hq : q ≠ 0),
  (q^D - q^i)/(q^k-q^i) = q^(D-k) *
        ((1 - 1/q^(D-i)) / (1 - 1/q^(k-i))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0785.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0786 : Prop where
  proof : ((∀ {K V : Type} [Field K] [AddCommGroup V]
        [Module K V] [Fintype K] [Finite V] (k : ℕ) (hk : k ≤ finrank K V),
    (Nat.card (DimSubspace K V k) : ℝ) =
          (Fintype.card K : ℝ)^(k*(finrank K V-k)) *
            grassmannFactor (finrank K V) k (Fintype.card K)))

theorem subspace_count_normalized [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0786] : ((∀ {K V : Type} [Field K] [AddCommGroup V]
      [Module K V] [Fintype K] [Finite V] (k : ℕ) (hk : k ≤ finrank K V),
  (Nat.card (DimSubspace K V k) : ℝ) =
        (Fintype.card K : ℝ)^(k*(finrank K V-k)) *
          grassmannFactor (finrank K V) k (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0786.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0787 : Prop where
  proof : ((∀ (n : ℕ) (hn : 0<n),
    Tendsto (fun q : ℝ => 1/q^n) atTop (nhds 0)))

theorem inverse_power_tendsto_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0787] : ((∀ (n : ℕ) (hn : 0<n),
  Tendsto (fun q : ℝ => 1/q^n) atTop (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0787.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0788 : Prop where
  proof : ((∀ (D k : ℕ) (hk : k ≤ D),
    Tendsto (grassmannFactor D k) atTop (nhds 1)))

theorem grassmannFactor_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0788] : ((∀ (D k : ℕ) (hk : k ≤ D),
  Tendsto (grassmannFactor D k) atTop (nhds 1))) := @OAI.SidorenkoCounterexample.ProofCertificate_0788.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0789 : Prop where
  proof : ((∀ (r k : ℕ),
    (r+k+1).choose 2 = (r+1).choose 2 + (k+1).choose 2 + r*k))

theorem triangular_nat_add [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0789] : ((∀ (r k : ℕ),
  (r+k+1).choose 2 = (r+1).choose 2 + (k+1).choose 2 + r*k)) := @OAI.SidorenkoCounterexample.ProofCertificate_0789.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0790 : Prop where
  proof : ((∀ {K : Type} [Field K] [Fintype K] [DecidableEq K]
        (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    layerMass K D r ξ * (Fintype.card K : ℝ)^((D-r+1).choose 2) =
          grassmannFactor D (D-r) (Fintype.card K) * symmetricSignProb (K := K) r ξ))

theorem layerMass_normalized [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0790] : ((∀ {K : Type} [Field K] [Fintype K] [DecidableEq K]
      (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  layerMass K D r ξ * (Fintype.card K : ℝ)^((D-r+1).choose 2) =
        grassmannFactor D (D-r) (Fintype.card K) * symmetricSignProb (K := K) r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0790.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0791 : Prop where
  proof : ((Tendsto (fun q : OddPrime => (q.val : ℝ)) primeInfinity atTop))

theorem primeInfinity_real_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0791] : ((Tendsto (fun q : OddPrime => (q.val : ℝ)) primeInfinity atTop)) := @OAI.SidorenkoCounterexample.ProofCertificate_0791.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0792 : Prop where
  proof : ((∀ (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    Tendsto (fun q : OddPrime => symmetricSignProb (K := ZMod q.val) r ξ)
          primeInfinity (nhds (1/2))))

theorem symmetricSignProb_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0792] : ((∀ (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  Tendsto (fun q : OddPrime => symmetricSignProb (K := ZMod q.val) r ξ)
        primeInfinity (nhds (1/2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0792.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0793 : Prop where
  proof : ((∀ (D r : ℕ) (hr : 0<r) (hrD : r ≤ D)
        {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    Tendsto (fun q : OddPrime => layerMass (ZMod q.val) D r ξ *
          (q.val:ℝ)^((D-r+1).choose 2)) primeInfinity (nhds (1/2))))

theorem layerMass_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0793] : ((∀ (D r : ℕ) (hr : 0<r) (hrD : r ≤ D)
      {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  Tendsto (fun q : OddPrime => layerMass (ZMod q.val) D r ξ *
        (q.val:ℝ)^((D-r+1).choose 2)) primeInfinity (nhds (1/2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0793.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Filter Topology
open scoped BigOperators
section CountDimension
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0794 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : Finite V], (∀ (hK : ringChar K ≠ 2),
    Nat.card (MaxOrthogonal (K := K) (V := V)) =
          ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
            Fintype.card K ^ k.val.choose 2))

theorem maxOrthogonal_card_by_dimension [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0794] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : Finite V], (∀ (hK : ringChar K ≠ 2),
  Nat.card (MaxOrthogonal (K := K) (V := V)) =
        ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
          Fintype.card K ^ k.val.choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0794.proof certificateEvidence
end

end CountDimension
noncomputable def orthogonalFactor (r : ℕ) (q : ℝ) : ℝ :=
  ∑ k : Fin (r+1), grassmannFactor r k.val q / q^((r-k.val).choose 2)

section
attribute [local instance] certificateFintype
class ProofCertificate_0795 : Prop where
  proof : ((∀ (a b : ℕ),
    (a+b).choose 2 = a.choose 2+b.choose 2+a*b))

theorem choose_two_add [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0795] : ((∀ (a b : ℕ),
  (a+b).choose 2 = a.choose 2+b.choose 2+a*b)) := @OAI.SidorenkoCounterexample.ProofCertificate_0795.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0796 : Prop where
  proof : ((∀ {K : Type} [Field K] [Fintype K]
        (hK : ringChar K ≠ 2) (r : ℕ),
    (Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) : ℝ) /
          (Fintype.card K : ℝ)^r.choose 2 = orthogonalFactor r (Fintype.card K)))

theorem maxOrthogonal_normalized [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0796] : ((∀ {K : Type} [Field K] [Fintype K]
      (hK : ringChar K ≠ 2) (r : ℕ),
  (Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) : ℝ) /
        (Fintype.card K : ℝ)^r.choose 2 = orthogonalFactor r (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0796.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0797 : Prop where
  proof : ((∀ (r : ℕ) (hr : 0<r),
    Tendsto (orthogonalFactor r) atTop (nhds 2)))

theorem orthogonalFactor_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0797] : ((∀ (r : ℕ) (hr : 0<r),
  Tendsto (orthogonalFactor r) atTop (nhds 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0797.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0798 : Prop where
  proof : ((∀ {K E : Type} [Field K] [Fintype K] [DecidableEq K]
        [AddCommGroup E] [Module K E] [FiniteDimensional K E]
        (B : LinearMap.BilinForm K E) (hs : B.IsSymm) (hB : B.Nondegenerate)
        (hK : ringChar K ≠ 2) (r : ℕ) (hd : finrank K E=2*r)
        (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)),
    (Nat.card (SymplecticLagrangian B) : ℝ)/(Fintype.card K : ℝ)^r.choose 2 =
          orthogonalFactor r (Fintype.card K)))

theorem split_form_normalized [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0798] : ((∀ {K E : Type} [Field K] [Fintype K] [DecidableEq K]
      [AddCommGroup E] [Module K E] [FiniteDimensional K E]
      (B : LinearMap.BilinForm K E) (hs : B.IsSymm) (hB : B.Nondegenerate)
      (hK : ringChar K ≠ 2) (r : ℕ) (hd : finrank K E=2*r)
      (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)),
  (Nat.card (SymplecticLagrangian B) : ℝ)/(Fintype.card K : ℝ)^r.choose 2 =
        orthogonalFactor r (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0798.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section PairSigns
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
section
attribute [local instance] certificateFintype
class ProofCertificate_0799 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D r : Nat}, (∀ (hd : D=2*r) (A B : SymMatrix K D)
        (hB : B.val.det≠0) (ha : A.val.rank=r) (hb : (A-B).val.rank=r),
    quadraticChar K B.val.det = quadraticChar K ((-1 : K)^r) *
          matrixSign K D A * matrixSign K D (A-B)))

theorem signed_pair_compatibility [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0799] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D r : Nat}, (∀ (hd : D=2*r) (A B : SymMatrix K D)
      (hB : B.val.det≠0) (ha : A.val.rank=r) (hb : (A-B).val.rank=r),
  quadraticChar K B.val.det = quadraticChar K ((-1 : K)^r) *
        matrixSign K D A * matrixSign K D (A-B))) := @OAI.SidorenkoCounterexample.ProofCertificate_0799.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0800 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D r : Nat}, (∀ (hd : D=2*r) (A B : SymMatrix K D)
        (hB : B.val.det≠0) (ha : A.val.rank=r) {ξ ζ : ℤ} (hx : matrixSign K D A=ξ)
        (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ),
    ((A-B).val.rank=r ∧ matrixSign K D (A-B)=ζ) ↔ A.val*B.val⁻¹*A.val=A.val))

theorem signed_second_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0800] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D r : Nat}, (∀ (hd : D=2*r) (A B : SymMatrix K D)
      (hB : B.val.det≠0) (ha : A.val.rank=r) {ξ ζ : ℤ} (hx : matrixSign K D A=ξ)
      (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ),
  ((A-B).val.rank=r ∧ matrixSign K D (A-B)=ζ) ↔ A.val*B.val⁻¹*A.val=A.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0800.proof certificateEvidence
end

end PairSigns
section Equiv
variable {K n : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
section
attribute [local instance] certificateFintype
class ProofCertificate_0801 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
      [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] {K n : Type} [inst : Field K] [inst : Fintype n]
      [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
        (A : CenterProjection Q),
    finrank K (centerSubspaceEquiv Q hQ hdet A).val = A.val.rank))

theorem centerSubspaceEquiv_rank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0801] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
    [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] {K n : Type} [inst : Field K] [inst : Fintype n]
    [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
      (A : CenterProjection Q),
  finrank K (centerSubspaceEquiv Q hQ hdet A).val = A.val.rank)) := @OAI.SidorenkoCounterexample.ProofCertificate_0801.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0802 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
      [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] {K n : Type} [inst : Field K] [inst : Fintype K]
      [inst : DecidableEq K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
        (A : CenterProjection Q),
    discriminantSign A.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr A.property.1) =
        discriminantSign (Q.toBilin'.restrict (centerSubspaceEquiv Q hQ hdet A).val)
          ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _)))

theorem centerSubspaceEquiv_sign [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0802] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
    [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] {K n : Type} [inst : Field K] [inst : Fintype K]
    [inst : DecidableEq K] [inst : Fintype n] [inst : DecidableEq n], (∀ (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
      (A : CenterProjection Q),
  discriminantSign A.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr A.property.1) =
      discriminantSign (Q.toBilin'.restrict (centerSubspaceEquiv Q hQ hdet A).val)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0802.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727] [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] [c9 : OAI.SidorenkoCounterexample.ProofCertificate_0736]
noncomputable def centerPredicateEquiv (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (P : Submodule K (n → K) → Prop) :
    {A : CenterProjection Q // P A.val.toLin'.range} ≃
    {U : Submodule K (n → K) // (Q.toBilin'.restrict U).Nondegenerate ∧ P U} :=
  ((centerSubspaceEquiv Q hQ hdet).subtypeEquiv (fun A => by
    rw [centerSubspaceEquiv_val])).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
end

end Equiv
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section SignedProjector
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
def SignedProjector (Q : Matrix (Fin D) (Fin D) K) (r : ℕ) (ξ : ℤ) :=
  {A : CenterProjection Q // A.val.rank=r ∧
    discriminantSign A.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr A.property.1)=ξ}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0800] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0640]
noncomputable def pairSignedCenterEquiv (hd : D=2*r) (B : SymMatrix K D)
    (hB : B.val.det≠0) (ξ ζ : ℤ)
    (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ} ≃
      SignedProjector B.val⁻¹ r ξ where
  toFun A :=
    ⟨⟨A.val.val,A.val.property,
      (signed_second_iff hd A.val B hB ((mem_signedLayer ..).mp A.property.1).1
        ((mem_signedLayer ..).mp A.property.1).2 hm).mp
        ((mem_signedLayer ..).mp A.property.2)⟩,
      ((mem_signedLayer ..).mp A.property.1).1,((mem_signedLayer ..).mp A.property.1).2⟩
  invFun A :=
    ⟨⟨A.val.val,A.val.property.1⟩,
      (mem_signedLayer ..).mpr A.property,
      (mem_signedLayer ..).mpr ((signed_second_iff hd ⟨A.val.val,A.val.property.1⟩ B hB
        A.property.1 A.property.2 hm).mpr A.val.property.2)⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727] [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] [c9 : OAI.SidorenkoCounterexample.ProofCertificate_0801] [c10 : OAI.SidorenkoCounterexample.ProofCertificate_0802]
noncomputable def signedProjectorSubspaceEquiv (Q : Matrix (Fin D) (Fin D) K)
    (hQ : Q.IsSymm) (hdet : Q.det≠0) (r : ℕ) (ξ : ℤ) :
    SignedProjector Q r ξ ≃
    {U : DimSubspace K (Fin D → K) r // (Q.toBilin'.restrict U.val).Nondegenerate ∧
      discriminantSign (Q.toBilin'.restrict U.val)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict U.val)=ξ} where
  toFun A :=
    ⟨⟨(centerSubspaceEquiv Q hQ hdet A.val).val,
      (centerSubspaceEquiv_rank Q hQ hdet A.val).trans A.property.1⟩,
      (centerSubspaceEquiv Q hQ hdet A.val).property,
      (centerSubspaceEquiv_sign Q hQ hdet A.val).symm.trans A.property.2⟩
  invFun U :=
    ⟨(centerSubspaceEquiv Q hQ hdet).symm ⟨U.val.val,U.property.1⟩,by
      constructor
      · rw [←centerSubspaceEquiv_rank Q hQ hdet,Equiv.apply_symm_apply]; exact U.val.property
      · rw [centerSubspaceEquiv_sign Q hQ hdet,Equiv.apply_symm_apply]; exact U.property.2⟩
  left_inv A := by
    apply Subtype.ext
    exact (centerSubspaceEquiv Q hQ hdet).symm_apply_apply A.val
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change ((centerSubspaceEquiv Q hQ hdet)
      ((centerSubspaceEquiv Q hQ hdet).symm ⟨U.val.val,U.property.1⟩)).val=U.val.val
    rw [Equiv.apply_symm_apply]
end

end SignedProjector
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Isotropic
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0803 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (L : LinearMap.BilinForm K V) (U : Submodule K V),
    L.restrict U=0 ↔ U ≤ L.orthogonal U))

theorem restrict_eq_zero_iff_isotropic [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0803] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (L : LinearMap.BilinForm K V) (U : Submodule K V),
  L.restrict U=0 ↔ U ≤ L.orthogonal U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0803.proof certificateEvidence
end

variable [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0804 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ (L : LinearMap.BilinForm K V) (hL : L.Nondegenerate)
        (r : ℕ) (hd : finrank K V=2*r) (U : Submodule K V) (hu : finrank K U=r),
    L.restrict U=0 ↔ L.orthogonal U=U))

theorem half_isotropic_iff_self [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0804] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ (L : LinearMap.BilinForm K V) (hL : L.Nondegenerate)
      (r : ℕ) (hd : finrank K V=2*r) (U : Submodule K V) (hu : finrank K U=r),
  L.restrict U=0 ↔ L.orthogonal U=U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0804.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0804] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0030] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0803]
noncomputable def halfIsotropicEquiv (L : LinearMap.BilinForm K V) (hL : L.Nondegenerate)
    (r : ℕ) (hd : finrank K V=2*r) :
    {U : DimSubspace K V r // L.restrict U.val=0} ≃ SymplecticLagrangian L where
  toFun U := ⟨U.val.val,(half_isotropic_iff_self L hL r hd U.val.val U.val.property).mp U.property⟩
  invFun U := ⟨⟨U.val,by
    have h := self_orthogonal_twice_finrank L U.val hL U.property
    omega⟩,(restrict_eq_zero_iff_isotropic L U.val).mpr (by rw [U.property])⟩
  left_inv U := by apply Subtype.ext; rfl
  right_inv U := rfl
end

end Isotropic
section Triple
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0800] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0640] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0739]
noncomputable def tripleSignedCenterEquiv (hd : D=2*r) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (ξ ζ θ : ℤ)
    (hmB : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ)
    (hmC : quadraticChar K C.val.det=quadraticChar K ((-1 : K)^r)*ξ*θ) :
    {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ ∧
      A-C ∈ signedLayer K D r θ} ≃
    {A : SignedProjector B.val⁻¹ r ξ // (B.val⁻¹-C.val⁻¹).toBilin'.restrict A.val.val.toLin'.range=0} where
  toFun A := ⟨pairSignedCenterEquiv hd B hB ξ ζ hmB ⟨A.val,A.property.1,A.property.2.1⟩,by
    apply (center_second_equation B.val⁻¹ C.val⁻¹ A.val.val A.val.property
      ((pairSignedCenterEquiv hd B hB ξ ζ hmB ⟨A.val,A.property.1,A.property.2.1⟩).val.property.2)).mp
    exact (signed_second_iff hd A.val C hC ((mem_signedLayer ..).mp A.property.1).1
      ((mem_signedLayer ..).mp A.property.1).2 hmC).mp ((mem_signedLayer ..).mp A.property.2.2)⟩
  invFun A :=
    let a := (pairSignedCenterEquiv hd B hB ξ ζ hmB).symm A.val
    ⟨a.val,a.property.1,a.property.2,(mem_signedLayer ..).mpr
      ((signed_second_iff hd a.val C hC ((mem_signedLayer ..).mp a.property.1).1
        ((mem_signedLayer ..).mp a.property.1).2 hmC).mpr
        ((center_second_equation B.val⁻¹ C.val⁻¹ A.val.val.val A.val.val.property.1
          A.val.val.property.2).mpr A.property))⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl
end

end Triple
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Count
variable {I K V : Type} [Fintype I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0805 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I], (∀ (f : I → ℝ),
    (Fintype.card I : ℝ)*uniformMean f=∑ i, f i))

theorem uniformMean_mul_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0805] : (∀ {I : Type} [inst : Fintype I], (∀ (f : I → ℝ),
  (Fintype.card I : ℝ)*uniformMean f=∑ i, f i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0805.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0806 : Prop where
  proof : (∀ {I K V : Type} [inst : Fintype I] [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K]
      [inst_3 : AddCommGroup V] [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (U : I → Submodule K V) (Q : SymForm K V) (ξ : ℤ),
    (Nat.card {i : I // (Q.val.restrict (U i)).Nondegenerate ∧
          discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ} : ℝ) =
        (Fintype.card I : ℝ)*uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))))

theorem restrictionSign_count [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0806] : (∀ {I K V : Type} [inst : Fintype I] [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K]
    [inst_3 : AddCommGroup V] [inst_4 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (U : I → Submodule K V) (Q : SymForm K V) (ξ : ℤ),
  (Nat.card {i : I // (Q.val.restrict (U i)).Nondegenerate ∧
        discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ} : ℝ) =
      (Fintype.card I : ℝ)*uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0806.proof certificateEvidence
end

end Count
section Identities
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0731] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0730] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0732] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0733] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0725] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0726] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0728] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0727] [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0724] [c9 : OAI.SidorenkoCounterexample.ProofCertificate_0801] [c10 : OAI.SidorenkoCounterexample.ProofCertificate_0802] [c11 : OAI.SidorenkoCounterexample.ProofCertificate_0736]
noncomputable def signedProjectorIsotropicEquiv (Q : Matrix (Fin D) (Fin D) K)
    (hQ : Q.IsSymm) (hdet : Q.det≠0) (r : ℕ) (ξ : ℤ)
    (L : LinearMap.BilinForm K (Fin D → K)) :
    {A : SignedProjector Q r ξ // L.restrict A.val.val.toLin'.range=0} ≃
    {U : {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0} //
      (Q.toBilin'.restrict U.val.val).Nondegenerate ∧
      discriminantSign (Q.toBilin'.restrict U.val.val)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict U.val.val)=ξ} where
  toFun A :=
    let U := signedProjectorSubspaceEquiv Q hQ hdet r ξ A.val
    ⟨⟨U.val,by
      change L.restrict (centerSubspaceEquiv Q hQ hdet A.val.val).val=0
      rw [centerSubspaceEquiv_val]; exact A.property⟩,U.property⟩
  invFun U :=
    let A := (signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm ⟨U.val.val,U.property⟩
    ⟨A,by
      rw [←centerSubspaceEquiv_val Q hQ hdet]
      change L.restrict ((signedProjectorSubspaceEquiv Q hQ hdet r ξ) A).val.val=0
      rw [show (signedProjectorSubspaceEquiv Q hQ hdet r ξ) A=⟨U.val.val,U.property⟩ from
        Equiv.apply_symm_apply _ _]
      exact U.val.property⟩
  left_inv A := by
    apply Subtype.ext
    exact (signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm_apply_apply A.val
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change ((signedProjectorSubspaceEquiv Q hQ hdet r ξ)
      ((signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm ⟨U.val.val,U.property⟩)).val=U.val.val
    rw [Equiv.apply_symm_apply]
end

noncomputable def pairRestrictionFraction (Q : SymMatrix K D) (r : ℕ) (ξ : ℤ) : ℝ := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  exact uniformMean (fun U : DimSubspace K (Fin D → K) r =>
    formSignIndicator ξ (symFormPull U.val.subtype (matrixFormEquiv D Q)))

noncomputable def isotropicRestrictionFraction (Q : SymMatrix K D)
    (L : LinearMap.BilinForm K (Fin D → K)) (r : ℕ) (ξ : ℤ) : ℝ := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0}
  exact uniformMean (fun U : {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0} =>
    formSignIndicator ξ (symFormPull U.val.val.subtype (matrixFormEquiv D Q)))

section
attribute [local instance] certificateFintype
class ProofCertificate_0807 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D r : Nat}, (∀ (hd : D=2*r) (B : SymMatrix K D) (hB : B.val.det≠0)
        (ξ ζ : ℤ) (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ),
    (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ} : ℝ) =
        (Nat.card (DimSubspace K (Fin D → K) r) : ℝ) *
          pairRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D) r ξ))

theorem pairCenter_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0807] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D r : Nat}, (∀ (hd : D=2*r) (B : SymMatrix K D) (hB : B.val.det≠0)
      (ξ ζ : ℤ) (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ),
  (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ} : ℝ) =
      (Nat.card (DimSubspace K (Fin D → K) r) : ℝ) *
        pairRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D) r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0807.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0808 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D r : Nat}, (∀ (hd : D=2*r) (B C : SymMatrix K D)
        (hB : B.val.det≠0) (hC : C.val.det≠0) (ξ ζ θ : ℤ)
        (hmB : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ)
        (hmC : quadraticChar K C.val.det=quadraticChar K ((-1 : K)^r)*ξ*θ),
    (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ ∧
          A-C ∈ signedLayer K D r θ} : ℝ) =
        (Nat.card {U : DimSubspace K (Fin D → K) r //
          (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0} : ℝ) *
          isotropicRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D)
            (B.val⁻¹-C.val⁻¹).toBilin' r ξ))

theorem tripleCenter_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0808] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D r : Nat}, (∀ (hd : D=2*r) (B C : SymMatrix K D)
      (hB : B.val.det≠0) (hC : C.val.det≠0) (ξ ζ θ : ℤ)
      (hmB : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ)
      (hmC : quadraticChar K C.val.det=quadraticChar K ((-1 : K)^r)*ξ*θ),
  (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ ∧
        A-C ∈ signedLayer K D r θ} : ℝ) =
      (Nat.card {U : DimSubspace K (Fin D → K) r //
        (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0} : ℝ) *
        isotropicRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D)
          (B.val⁻¹-C.val⁻¹).toBilin' r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0808.proof certificateEvidence
end

end Identities
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Filter
open scoped BigOperators
section Coeff
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def pairCoefficient (r : ℕ) (ξ ζ : ℤ) : ℝ :=
  (Nat.card (DimSubspace K (Fin (2*r) → K) r) : ℝ) /
    (Fintype.card (SymMatrix K (2*r)) : ℝ) /
      (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ)

noncomputable def tripleCoefficient (r : ℕ) (ξ ζ θ : ℤ) : ℝ :=
  (Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) : ℝ) /
    (Fintype.card (SymMatrix K (2*r)) : ℝ) /
      (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ)

section
attribute [local instance] certificateFintype
class ProofCertificate_0809 : Prop where
  proof : ((∀ (r : ℕ),
    r*r+2*((r+1).choose 2)=(2*r+1).choose 2))

theorem pair_exponent_cancel [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0809] : ((∀ (r : ℕ),
  r*r+2*((r+1).choose 2)=(2*r+1).choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0809.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0810 : Prop where
  proof : ((∀ (r : ℕ),
    r.choose 2+3*((r+1).choose 2)=(2*r+1).choose 2))

theorem triple_exponent_cancel [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0810] : ((∀ (r : ℕ),
  r.choose 2+3*((r+1).choose 2)=(2*r+1).choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0810.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0811 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ),
    pairCoefficient (K := K) r ξ ζ =
          grassmannFactor (2*r) r (Fintype.card K) /
            ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
              (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2)))))

theorem pairCoefficient_normalized [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0811] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ),
  pairCoefficient (K := K) r ξ ζ =
        grassmannFactor (2*r) r (Fintype.card K) /
          ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
            (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0811.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0812 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (ξ ζ θ : ℤ),
    tripleCoefficient (K := K) r ξ ζ θ =
          orthogonalFactor r (Fintype.card K) /
            ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
              (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
              (layerMass K (2*r) r θ * (Fintype.card K : ℝ)^((r+1).choose 2)))))

theorem tripleCoefficient_normalized [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0812] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (ξ ζ θ : ℤ),
  tripleCoefficient (K := K) r ξ ζ θ =
        orthogonalFactor r (Fintype.card K) /
          ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
            (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
            (layerMass K (2*r) r θ * (Fintype.card K : ℝ)^((r+1).choose 2))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0812.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0813 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ),
    0≤pairCoefficient (K := K) r ξ ζ))

theorem pairCoefficient_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0813] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ),
  0≤pairCoefficient (K := K) r ξ ζ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0813.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0814 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ),
    0≤tripleCoefficient (K := K) r ξ ζ θ))

theorem tripleCoefficient_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0814] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ),
  0≤tripleCoefficient (K := K) r ξ ζ θ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0814.proof certificateEvidence
end

end Coeff
section
attribute [local instance] certificateFintype
class ProofCertificate_0815 : Prop where
  proof : ((∀ (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
        (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1),
    Tendsto (fun q : OddPrime => pairCoefficient (K := ZMod q.val) r ξ ζ)
          primeInfinity (nhds 4)))

theorem pairCoefficient_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0815] : ((∀ (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
      (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1),
  Tendsto (fun q : OddPrime => pairCoefficient (K := ZMod q.val) r ξ ζ)
        primeInfinity (nhds 4))) := @OAI.SidorenkoCounterexample.ProofCertificate_0815.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0816 : Prop where
  proof : ((∀ (r : ℕ) (hr : 0<r) {ξ ζ θ : ℤ}
        (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1),
    Tendsto (fun q : OddPrime => tripleCoefficient (K := ZMod q.val) r ξ ζ θ)
          primeInfinity (nhds 16)))

theorem tripleCoefficient_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0816] : ((∀ (r : ℕ) (hr : 0<r) {ξ ζ θ : ℤ}
      (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1),
  Tendsto (fun q : OddPrime => tripleCoefficient (K := ZMod q.val) r ξ ζ θ)
        primeInfinity (nhds 16))) := @OAI.SidorenkoCounterexample.ProofCertificate_0816.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Sizes
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0817 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (r : ℕ),
    Fintype.card K ^ r.choose 2 ≤ Nat.card (MaxOrthogonal (K := K) (V := Fin r → K))))

theorem maxOrthogonal_card_lower [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0817] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (r : ℕ),
  Fintype.card K ^ r.choose 2 ≤ Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0817.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0818 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (L : LinearMap.BilinForm K (Fin (2*r) → K))
        (hs : L.IsSymm) (hL : L.Nondegenerate) (hK : ringChar K≠2)
        (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)),
    Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} =
          Nat.card (MaxOrthogonal (K := K) (V := Fin r → K))))

theorem halfIsotropic_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0818] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (L : LinearMap.BilinForm K (Fin (2*r) → K))
      (hs : L.IsSymm) (hL : L.Nondegenerate) (hK : ringChar K≠2)
      (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)),
  Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} =
        Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0818.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0819 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (r : ℕ) (hr : 0<r),
    (Fintype.card K : ℝ) ≤ Nat.card (DimSubspace K (Fin (2*r) → K) r)))

theorem pairFamily_card_ge [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0819] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (r : ℕ) (hr : 0<r),
  (Fintype.card K : ℝ) ≤ Nat.card (DimSubspace K (Fin (2*r) → K) r))) := @OAI.SidorenkoCounterexample.ProofCertificate_0819.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0820 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (hr : 1<r)
        (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
        (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)),
    (Fintype.card K : ℝ) ≤ Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0}))

theorem isotropicFamily_card_ge [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0820] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (hr : 1<r)
      (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
      (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)),
  (Fintype.card K : ℝ) ≤ Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0})) := @OAI.SidorenkoCounterexample.ProofCertificate_0820.proof certificateEvidence
end

end Sizes
section Bounds
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] {D r : ℕ}
section
attribute [local instance] certificateFintype
class ProofCertificate_0821 : Prop where
  proof : (∀ {K I : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype I] {D r : Nat}, (∀ (U : I → Submodule K (Fin D → K))
        (hinj : Function.Injective U) (hd : ∀ i, finrank K (U i)=r)
        (hc : (Fintype.card K : ℝ)≤Fintype.card I) (hK : ringChar K≠2)
        {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    uniformMean (fun Q : SymMatrix K D =>
          |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype (matrixFormEquiv D Q)))-1/2|) ≤
            Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ))))

theorem matrix_restriction_family_L1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0821] : (∀ {K I : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype I] {D r : Nat}, (∀ (U : I → Submodule K (Fin D → K))
      (hinj : Function.Injective U) (hd : ∀ i, finrank K (U i)=r)
      (hc : (Fintype.card K : ℝ)≤Fintype.card I) (hK : ringChar K≠2)
      {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  uniformMean (fun Q : SymMatrix K D =>
        |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype (matrixFormEquiv D Q)))-1/2|) ≤
          Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0821.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0822 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (hr : 0<r) (hK : ringChar K≠2)
        {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    uniformMean (fun Q : SymMatrix K (2*r) => |pairRestrictionFraction Q r ξ-1/2|) ≤
          Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ))))

theorem pairRestrictionFraction_L1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0822] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (hr : 0<r) (hK : ringChar K≠2)
      {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  uniformMean (fun Q : SymMatrix K (2*r) => |pairRestrictionFraction Q r ξ-1/2|) ≤
        Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0822.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0823 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (hr : 1<r)
        (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
        (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r))
        {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    uniformMean (fun Q : SymMatrix K (2*r) => |isotropicRestrictionFraction Q L r ξ-1/2|) ≤
          Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ))))

theorem isotropicRestrictionFraction_L1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0823] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (hr : 1<r)
      (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
      (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r))
      {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  uniformMean (fun Q : SymMatrix K (2*r) => |isotropicRestrictionFraction Q L r ξ-1/2|) ≤
        Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0823.proof certificateEvidence
end

end Bounds
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {I A B : Type} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
section
attribute [local instance] certificateFintype
class ProofCertificate_0824 : Prop where
  proof : (∀ {I A : Type} [inst : Fintype I] [inst : Fintype A], (∀ (f : I → A → ℝ),
    uniformMean (fun a => ∑ i, f i a)=∑ i, uniformMean (f i)))

theorem uniformMean_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0824] : (∀ {I A : Type} [inst : Fintype I] [inst : Fintype A], (∀ (f : I → A → ℝ),
  uniformMean (fun a => ∑ i, f i a)=∑ i, uniformMean (f i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0824.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0825 : Prop where
  proof : (∀ {I A : Type} [inst : Fintype I] [inst : DecidableEq I] [inst : Fintype A], (∀ [Nonempty A] (i : I) (f : A → ℝ),
    uniformMean (fun x : I → A => f (x i))=uniformMean f))

theorem uniformMean_coordinate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0825] : (∀ {I A : Type} [inst : Fintype I] [inst : DecidableEq I] [inst : Fintype A], (∀ [Nonempty A] (i : I) (f : A → ℝ),
  uniformMean (fun x : I → A => f (x i))=uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0825.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0826 : Prop where
  proof : (∀ {I A : Type} [inst : Fintype I] [inst : DecidableEq I] [inst : Fintype A], (∀ [Nonempty A] (i : I) (f : (I → A) → ℝ),
    uniformMean f=uniformMean (fun x : I → A => uniformMean (fun a : A => f (Function.update x i a)))))

theorem uniformMean_update [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0826] : (∀ {I A : Type} [inst : Fintype I] [inst : DecidableEq I] [inst : Fintype A], (∀ [Nonempty A] (i : I) (f : (I → A) → ℝ),
  uniformMean f=uniformMean (fun x : I → A => uniformMean (fun a : A => f (Function.update x i a))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0826.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0827 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (f : A → ℝ) (c : ℝ),
    uniformMean (fun a => f a*c)=uniformMean f*c))

theorem uniformMean_mul_right [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0827] : (∀ {A : Type} [inst : Fintype A], (∀ (f : A → ℝ) (c : ℝ),
  uniformMean (fun a => f a*c)=uniformMean f*c)) := @OAI.SidorenkoCounterexample.ProofCertificate_0827.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0828 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ [Nonempty A] (P : A → Prop) [DecidablePred P]
        (f : A → ℝ) (b : ℝ) (hf : ∀ a, P a → f a≤b) (hb : 0≤b),
    uniformMean (fun a => if P a then f a else 0)≤b))

theorem uniformMean_ite_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0828] : (∀ {A : Type} [inst : Fintype A], (∀ [Nonempty A] (P : A → Prop) [DecidablePred P]
      (f : A → ℝ) (b : ℝ) (hf : ∀ a, P a → f a≤b) (hb : 0≤b),
  uniformMean (fun a => if P a then f a else 0)≤b)) := @OAI.SidorenkoCounterexample.ProofCertificate_0828.proof certificateEvidence
end

end Mean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Inverting
variable {K : Type} [Field K] [Fintype K]
noncomputable def symmetricInverse (D : ℕ) (M : SymMatrix K D) : SymMatrix K D :=
  by
  classical
  exact if M.val.det = 0 then M else ⟨M.val⁻¹, M.property.inv⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0829 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ (D : ℕ),
    Function.Involutive (symmetricInverse (K := K) D)))

theorem symmetricInverse_involutive [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0829] : (∀ {K : Type} [inst : Field K], (∀ (D : ℕ),
  Function.Involutive (symmetricInverse (K := K) D))) := @OAI.SidorenkoCounterexample.ProofCertificate_0829.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0829]
noncomputable def symmetricInverseEquiv (D : ℕ) : SymMatrix K D ≃ SymMatrix K D :=
  (symmetricInverse_involutive D).toPerm
end

end Inverting
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Center
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def pairLocal (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun A => rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B))

noncomputable def tripleLocal (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun A => rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) *
    rankKernel K (2*r) r θ (A-C))

def pairMatch (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : Prop :=
  quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ

def tripleMatch (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : Prop :=
  pairMatch r ξ ζ B ∧ pairMatch r ξ θ C ∧ pairMatch r ζ θ (C-B)

section
attribute [local instance] certificateFintype
class ProofCertificate_0830 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)),
    pairLocal r ξ ζ B =
          (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
            A-B ∈ signedLayer K (2*r) r ζ} : ℝ) /
          (Fintype.card (SymMatrix K (2*r)) : ℝ) /
            (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ)))

theorem pairLocal_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0830] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)),
  pairLocal r ξ ζ B =
        (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
          A-B ∈ signedLayer K (2*r) r ζ} : ℝ) /
        (Fintype.card (SymMatrix K (2*r)) : ℝ) /
          (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0830.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0831 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)),
    tripleLocal r ξ ζ θ B C =
          (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
            A-B ∈ signedLayer K (2*r) r ζ ∧ A-C ∈ signedLayer K (2*r) r θ} : ℝ) /
          (Fintype.card (SymMatrix K (2*r)) : ℝ) /
            (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ)))

theorem tripleLocal_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0831] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)),
  tripleLocal r ξ ζ θ B C =
        (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
          A-B ∈ signedLayer K (2*r) r ζ ∧ A-C ∈ signedLayer K (2*r) r θ} : ℝ) /
        (Fintype.card (SymMatrix K (2*r)) : ℝ) /
          (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0831.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0832 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
        (hB : B.val.det≠0) (hm : pairMatch r ξ ζ B),
    pairLocal r ξ ζ B = pairCoefficient (K := K) r ξ ζ *
          pairRestrictionFraction (symmetricInverse (2*r) B) r ξ))

theorem pairLocal_match [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0832] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
      (hB : B.val.det≠0) (hm : pairMatch r ξ ζ B),
  pairLocal r ξ ζ B = pairCoefficient (K := K) r ξ ζ *
        pairRestrictionFraction (symmetricInverse (2*r) B) r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0832.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0833 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
        (hB : B.val.det≠0) (hm : ¬pairMatch r ξ ζ B),
    pairLocal r ξ ζ B=0))

theorem pairLocal_mismatch [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0833] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
      (hB : B.val.det≠0) (hm : ¬pairMatch r ξ ζ B),
  pairLocal r ξ ζ B=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0833.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0834 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r))
        (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
        (hm : ¬tripleMatch r ξ ζ θ B C),
    tripleLocal r ξ ζ θ B C=0))

theorem tripleLocal_mismatch [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0834] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r))
      (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
      (hm : ¬tripleMatch r ξ ζ θ B C),
  tripleLocal r ξ ζ θ B C=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0834.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0835 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ (D : ℕ) (B C : SymMatrix K D)
        (hB : B.val.det≠0) (hC : C.val.det≠0),
    (B.val⁻¹-C.val⁻¹).det = B.val.det⁻¹ * (C-B).val.det * C.val.det⁻¹))

theorem inverse_difference_det [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0835] : (∀ {K : Type} [inst : Field K], (∀ (D : ℕ) (B C : SymMatrix K D)
      (hB : B.val.det≠0) (hC : C.val.det≠0),
  (B.val⁻¹-C.val⁻¹).det = B.val.det⁻¹ * (C-B).val.det * C.val.det⁻¹)) := @OAI.SidorenkoCounterexample.ProofCertificate_0835.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0836 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ (D : ℕ) (B C : SymMatrix K D)
        (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0),
    (B.val⁻¹-C.val⁻¹).toBilin'.Nondegenerate))

theorem inverse_difference_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0836] : (∀ {K : Type} [inst : Field K], (∀ (D : ℕ) (B C : SymMatrix K D)
      (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0),
  (B.val⁻¹-C.val⁻¹).toBilin'.Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0836.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0837 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (B C : SymMatrix K (2*r))
        (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
        {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
        (hm : tripleMatch r ξ ζ θ B C),
    discriminantSign (B.val⁻¹-C.val⁻¹).toBilin'
          (Matrix.isSymm_toBilin'_iff_isSymm.mpr (B.property.inv.sub C.property.inv)) =
            quadraticChar K ((-1 : K)^r)))

theorem matching_inverse_difference_split [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0837] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (B C : SymMatrix K (2*r))
      (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
      {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
      (hm : tripleMatch r ξ ζ θ B C),
  discriminantSign (B.val⁻¹-C.val⁻¹).toBilin'
        (Matrix.isSymm_toBilin'_iff_isSymm.mpr (B.property.inv.sub C.property.inv)) =
          quadraticChar K ((-1 : K)^r))) := @OAI.SidorenkoCounterexample.ProofCertificate_0837.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0838 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (B C : SymMatrix K (2*r))
        (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
        {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
        (hm : tripleMatch r ξ ζ θ B C),
    tripleLocal r ξ ζ θ B C = tripleCoefficient (K := K) r ξ ζ θ *
          isotropicRestrictionFraction (symmetricInverse (2*r) B) (B.val⁻¹-C.val⁻¹).toBilin' r ξ))

theorem tripleLocal_match [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0838] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (B C : SymMatrix K (2*r))
      (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
      {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
      (hm : tripleMatch r ξ ζ θ B C),
  tripleLocal r ξ ζ θ B C = tripleCoefficient (K := K) r ξ ζ θ *
        isotropicRestrictionFraction (symmetricInverse (2*r) B) (B.val⁻¹-C.val⁻¹).toBilin' r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0838.proof certificateEvidence
end

end Center
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Means
variable {A B : Type} [Fintype A] [Fintype B]
section
attribute [local instance] certificateFintype
class ProofCertificate_0839 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ {f : A → ℝ} (hf : ∀ a, f a ≤ 1),
    uniformMean f ≤ 1))

theorem uniformMean_le_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0839] : (∀ {A : Type} [inst : Fintype A], (∀ {f : A → ℝ} (hf : ∀ a, f a ≤ 1),
  uniformMean f ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0839.proof certificateEvidence
end

variable [AddCommGroup A]
section
attribute [local instance] certificateFintype
class ProofCertificate_0840 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A] [inst : AddCommGroup A], (∀ (a : A) (f : A → ℝ),
    uniformMean (fun x => f (a-x))=uniformMean f))

theorem uniformMean_subLeft [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0840] : (∀ {A : Type} [inst : Fintype A] [inst : AddCommGroup A], (∀ (a : A) (f : A → ℝ),
  uniformMean (fun x => f (a-x))=uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0840.proof certificateEvidence
end

end Means
section Range
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
section
attribute [local instance] certificateFintype
class ProofCertificate_0841 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (Q : SymMatrix K D) (r : ℕ) (ξ : ℤ),
    0 ≤ pairRestrictionFraction Q r ξ ∧ pairRestrictionFraction Q r ξ ≤ 1))

theorem pairRestrictionFraction_range [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0841] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (Q : SymMatrix K D) (r : ℕ) (ξ : ℤ),
  0 ≤ pairRestrictionFraction Q r ξ ∧ pairRestrictionFraction Q r ξ ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0841.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0842 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (Q : SymMatrix K D)
        (L : LinearMap.BilinForm K (Fin D → K)) (r : ℕ) (ξ : ℤ),
    0 ≤ isotropicRestrictionFraction Q L r ξ ∧ isotropicRestrictionFraction Q L r ξ ≤ 1))

theorem isotropicRestrictionFraction_range [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0842] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (Q : SymMatrix K D)
      (L : LinearMap.BilinForm K (Fin D → K)) (r : ℕ) (ξ : ℤ),
  0 ≤ isotropicRestrictionFraction Q L r ξ ∧ isotropicRestrictionFraction Q L r ξ ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0842.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0843 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] {D : Nat}, (∀ (f : SymMatrix K D → ℝ),
    uniformMean (fun B => f (symmetricInverse D B))=uniformMean f))

theorem uniformMean_inverse [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0843] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] {D : Nat}, (∀ (f : SymMatrix K D → ℝ),
  uniformMean (fun B => f (symmetricInverse D B))=uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0843.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0844 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] {D : Nat}, (∀ (f : SymMatrix K D → SymMatrix K D → ℝ),
    uniformMean (fun B => uniformMean fun C =>
          f (symmetricInverse D B) (symmetricInverse D B-symmetricInverse D C)) =
            uniformMean (fun L => uniformMean fun Q => f Q L)))

theorem uniformMean_inverse_difference [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0844] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] {D : Nat}, (∀ (f : SymMatrix K D → SymMatrix K D → ℝ),
  uniformMean (fun B => uniformMean fun C =>
        f (symmetricInverse D B) (symmetricInverse D B-symmetricInverse D C)) =
          uniformMean (fun L => uniformMean fun Q => f Q L))) := @OAI.SidorenkoCounterexample.ProofCertificate_0844.proof certificateEvidence
end

end Range
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0845 : Prop where
  proof : ((∀ (c f m : ℝ) (hc : 0 ≤ c),
    |c*f-m| ≤ |c/2-m|+c*|f-1/2|))

theorem scalar_fraction_error [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0845] : ((∀ (c f m : ℝ) (hc : 0 ≤ c),
  |c*f-m| ≤ |c/2-m|+c*|f-1/2|)) := @OAI.SidorenkoCounterexample.ProofCertificate_0845.proof certificateEvidence
end

section Error
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
def matrixSplit (r : ℕ) (L : SymMatrix K (2*r)) : Prop :=
  L.val.det≠0 ∧ discriminantSign L.val.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr L.property)=quadraticChar K ((-1 : K)^r)

noncomputable def pairError (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  if B.val.det≠0 then |pairLocal r ξ ζ B-(if pairMatch r ξ ζ B then 2 else 0)| else 0

noncomputable def tripleError (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : ℝ :=
  if B.val.det≠0 ∧ C.val.det≠0 ∧ (C-B).val.det≠0 then
    |tripleLocal r ξ ζ θ B C-(if tripleMatch r ξ ζ θ B C then 8 else 0)| else 0

noncomputable def splitFractionError (r : ℕ) (ξ : ℤ) (Q L : SymMatrix K (2*r)) : ℝ :=
  if matrixSplit r L then |isotropicRestrictionFraction Q L.val.toBilin' r ξ-1/2| else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0846 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Q L : SymMatrix K (2*r)),
    0 ≤ splitFractionError r ξ Q L))

theorem splitFractionError_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0846] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Q L : SymMatrix K (2*r)),
  0 ≤ splitFractionError r ξ Q L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0846.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0847 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)),
    pairError r ξ ζ B ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
          pairCoefficient (K := K) r ξ ζ*|pairRestrictionFraction (symmetricInverse (2*r) B) r ξ-1/2|))

theorem pairError_pointwise [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0847] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)),
  pairError r ξ ζ B ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
        pairCoefficient (K := K) r ξ ζ*|pairRestrictionFraction (symmetricInverse (2*r) B) r ξ-1/2|)) := @OAI.SidorenkoCounterexample.ProofCertificate_0847.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0848 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
        (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
        (B C : SymMatrix K (2*r)),
    tripleError r ξ ζ θ B C ≤ |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
          tripleCoefficient (K := K) r ξ ζ θ * splitFractionError r ξ
            (symmetricInverse (2*r) B) (symmetricInverse (2*r) B-symmetricInverse (2*r) C)))

theorem tripleError_pointwise [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0848] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
      (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
      (B C : SymMatrix K (2*r)),
  tripleError r ξ ζ θ B C ≤ |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
        tripleCoefficient (K := K) r ξ ζ θ * splitFractionError r ξ
          (symmetricInverse (2*r) B) (symmetricInverse (2*r) B-symmetricInverse (2*r) C))) := @OAI.SidorenkoCounterexample.ProofCertificate_0848.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0849 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
        {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (L : SymMatrix K (2*r)),
    uniformMean (fun Q => splitFractionError r ξ Q L) ≤
          Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ))))

theorem splitFractionError_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0849] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
      {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (L : SymMatrix K (2*r)),
  uniformMean (fun Q => splitFractionError r ξ Q L) ≤
        Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0849.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0850 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
        {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    uniformMean (pairError (K := K) r ξ ζ) ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
          pairCoefficient (K := K) r ξ ζ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ))))

theorem pairError_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0850] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
      {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  uniformMean (pairError (K := K) r ξ ζ) ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
        pairCoefficient (K := K) r ξ ζ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0850.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0851 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
        {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1),
    uniformMean (fun B => uniformMean (fun C => tripleError (K := K) r ξ ζ θ B C)) ≤
          |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
            tripleCoefficient (K := K) r ξ ζ θ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ))))

theorem tripleError_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0851] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
      {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1),
  uniformMean (fun B => uniformMean (fun C => tripleError (K := K) r ξ ζ θ B C)) ≤
        |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
          tripleCoefficient (K := K) r ξ ζ θ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0851.proof certificateEvidence
end

end Error
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Bounds
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0852 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)),
    0≤pairLocal r ξ ζ B))

theorem pairLocal_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0852] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)),
  0≤pairLocal r ξ ζ B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0852.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0853 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)),
    0≤tripleLocal r ξ ζ θ B C))

theorem tripleLocal_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0853] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)),
  0≤tripleLocal r ξ ζ θ B C)) := @OAI.SidorenkoCounterexample.ProofCertificate_0853.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0854 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)),
    0≤pairError r ξ ζ B))

theorem pairError_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0854] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)),
  0≤pairError r ξ ζ B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0854.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0855 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)),
    0≤tripleError r ξ ζ θ B C))

theorem tripleError_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0855] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)),
  0≤tripleError r ξ ζ θ B C)) := @OAI.SidorenkoCounterexample.ProofCertificate_0855.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0856 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) (hB : B.val.det≠0),
    pairLocal r ξ ζ B ≤ pairCoefficient (K := K) r ξ ζ))

theorem pairLocal_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0856] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) (hB : B.val.det≠0),
  pairLocal r ξ ζ B ≤ pairCoefficient (K := K) r ξ ζ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0856.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0857 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
        (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
        (B C : SymMatrix K (2*r)) (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0),
    tripleLocal r ξ ζ θ B C ≤ tripleCoefficient (K := K) r ξ ζ θ))

theorem tripleLocal_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0857] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
      (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
      (B C : SymMatrix K (2*r)) (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0),
  tripleLocal r ξ ζ θ B C ≤ tripleCoefficient (K := K) r ξ ζ θ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0857.proof certificateEvidence
end

end Bounds
section
attribute [local instance] certificateFintype
class ProofCertificate_0858 : Prop where
  proof : ((∀ (r : ℕ),
    Tendsto (fun q : OddPrime => Real.sqrt (((r : ℝ)+1)/(q.val : ℝ))) primeInfinity (nhds 0)))

theorem localFraction_error_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0858] : ((∀ (r : ℕ),
  Tendsto (fun q : OddPrime => Real.sqrt (((r : ℝ)+1)/(q.val : ℝ))) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0858.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0859 : Prop where
  proof : ((∀ (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
        (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1),
    Tendsto (fun q : OddPrime => uniformMean (pairError (K := ZMod q.val) r ξ ζ)) primeInfinity (nhds 0)))

theorem pairError_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0859] : ((∀ (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
      (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1),
  Tendsto (fun q : OddPrime => uniformMean (pairError (K := ZMod q.val) r ξ ζ)) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0859.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0860 : Prop where
  proof : ((∀ (r : ℕ) (hr : 1<r) {ξ ζ θ : ℤ}
        (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1),
    Tendsto (fun q : OddPrime => uniformMean (fun B => uniformMean
          (fun C => tripleError (K := ZMod q.val) r ξ ζ θ B C))) primeInfinity (nhds 0)))

theorem tripleError_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0860] : ((∀ (r : ℕ) (hr : 1<r) {ξ ζ θ : ℤ}
      (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1),
  Tendsto (fun q : OddPrime => uniformMean (fun B => uniformMean
        (fun C => tripleError (K := ZMod q.val) r ξ ζ θ B C))) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0860.proof certificateEvidence
end

end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Gauss
variable {K V : Type} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0861 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (ψ : AddChar K ℂ) (a : K),
    star (ψ a) = (ψ a)⁻¹))

theorem char_conj [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0861] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (ψ : AddChar K ℂ) (a : K),
  star (ψ a) = (ψ a)⁻¹)) := @OAI.SidorenkoCounterexample.ProofCertificate_0861.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0862 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst : Fintype K] [inst : AddCommGroup V] [inst : Fintype V], (∀ (ψ : AddChar K ℂ) (f : V → K),
    ‖∑ x, ψ (f x)‖ ^ 2 = ‖∑ u, ∑ z, ψ (f (z+u) - f z)‖))

theorem character_differencing [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0862] : (∀ {K V : Type} [inst : Field K] [inst : Fintype K] [inst : AddCommGroup V] [inst : Fintype V], (∀ (ψ : AddChar K ℂ) (f : V → K),
  ‖∑ x, ψ (f x)‖ ^ 2 = ‖∑ u, ∑ z, ψ (f (z+u) - f z)‖)) := @OAI.SidorenkoCounterexample.ProofCertificate_0862.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0863 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype V], (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (f : V →ₗ[K] K) (hf : f ≠ 0),
    ∑ x, ψ (f x) = 0))

theorem linear_character_sum_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0863] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype V], (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (f : V →ₗ[K] K) (hf : f ≠ 0),
  ∑ x, ψ (f x) = 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0863.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0864 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
        (l : V →ₗ[K] K) (c : K) (z u : V),
    (B (z+u) (z+u) + l (z+u) + c) - (B z z + l z + c) =
          B u u + l u + (2 : K) * B u z))

theorem quadratic_difference [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0864] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
      (l : V →ₗ[K] K) (c : K) (z u : V),
  (B (z+u) (z+u) + l (z+u) + c) - (B z z + l z + c) =
        B u u + l u + (2 : K) * B u z)) := @OAI.SidorenkoCounterexample.ProofCertificate_0864.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0865 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst : @_root_.Module K V _ _]
      [inst : Fintype V], (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
        (l : V →ₗ[K] K) (c : K),
    ‖∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
          (Fintype.card V : ℝ) * Nat.card B.ker))

theorem quadratic_gauss_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0865] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst : @_root_.Module K V _ _]
    [inst : Fintype V], (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
      (l : V →ₗ[K] K) (c : K),
  ‖∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
        (Fintype.card V : ℝ) * Nat.card B.ker)) := @OAI.SidorenkoCounterexample.ProofCertificate_0865.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0866 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst : @_root_.Module K V _ _]
      [inst : Fintype V], (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
        (l : V →ₗ[K] K) (c : K),
    ‖(Fintype.card V : ℂ)⁻¹ * ∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
          1 / (Fintype.card K : ℝ) ^ finrank K B.range))

theorem normalized_quadratic_gauss_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0866] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst : @_root_.Module K V _ _]
    [inst : Fintype V], (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
      (l : V →ₗ[K] K) (c : K),
  ‖(Fintype.card V : ℂ)⁻¹ * ∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
        1 / (Fintype.card K : ℝ) ^ finrank K B.range)) := @OAI.SidorenkoCounterexample.ProofCertificate_0866.proof certificateEvidence
end

end Gauss
section Fourier
variable {K ι : Type} [Field K] [Fintype K] [Fintype ι] [DecidableEq ι] [DecidableEq K]
noncomputable def coordinatePairing (v : ι → K) : (ι → K) →ₗ[K] K where
  toFun t := t ⬝ᵥ v
  map_add' := fun _ _ => add_dotProduct _ _ _
  map_smul' := fun _ _ => smul_dotProduct _ _ _

section
attribute [local instance] certificateFintype
class ProofCertificate_0867 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
      (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (v : ι → K),
    ∑ t : ι → K, ψ (t ⬝ᵥ v) = if v = 0 then (Fintype.card (ι → K) : ℂ) else 0))

theorem coordinate_character_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0867] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
    (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (v : ι → K),
  ∑ t : ι → K, ψ (t ⬝ᵥ v) = if v = 0 then (Fintype.card (ι → K) : ℂ) else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0867.proof certificateEvidence
end

noncomputable def finiteFourier (ψ : AddChar K ℂ) (μ : (ι → K) → ℝ)
    (t : ι → K) : ℂ := ∑ x, (μ x : ℂ) * ψ (t ⬝ᵥ x)

section
attribute [local instance] certificateFintype
class ProofCertificate_0868 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
      (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (μ : (ι → K) → ℝ),
    ∑ t, ‖finiteFourier ψ μ t‖ ^ 2 =
          (Fintype.card (ι → K) : ℝ) * ∑ x, (μ x)^2))

theorem finite_parseval [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0868] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
    (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (μ : (ι → K) → ℝ),
  ∑ t, ‖finiteFourier ψ μ t‖ ^ 2 =
        (Fintype.card (ι → K) : ℝ) * ∑ x, (μ x)^2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0868.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0869 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
      (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (t : ι → K),
    finiteFourier ψ (fun x => μ x - (Fintype.card (ι → K) : ℝ)⁻¹) t =
          if t = 0 then 0 else finiteFourier ψ μ t))

theorem finiteFourier_sub_uniform [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0869] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
    (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (t : ι → K),
  finiteFourier ψ (fun x => μ x - (Fintype.card (ι → K) : ℝ)⁻¹) t =
        if t = 0 then 0 else finiteFourier ψ μ t)) := @OAI.SidorenkoCounterexample.ProofCertificate_0869.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0870 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
      (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1),
    (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
          ∑ t, if t = 0 then 0 else ‖finiteFourier ψ μ t‖^2))

theorem finite_fourier_l1_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0870] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
    (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1),
  (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
        ∑ t, if t = 0 then 0 else ‖finiteFourier ψ μ t‖^2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0870.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0871 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
      (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (ε : ℝ) (hε : 0 ≤ ε)
        (hf : ∀ t ≠ 0, ‖finiteFourier ψ μ t‖ ^ 2 ≤ ε),
    (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
          (Fintype.card (ι → K) : ℝ) * ε))

theorem finite_fourier_l1_of_uniform_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0871] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K],
    (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (ε : ℝ) (hε : 0 ≤ ε)
      (hf : ∀ t ≠ 0, ‖finiteFourier ψ μ t‖ ^ 2 ≤ ε),
  (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
        (Fintype.card (ι → K) : ℝ) * ε)) := @OAI.SidorenkoCounterexample.ProofCertificate_0871.proof certificateEvidence
end

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
noncomputable def uniformLaw (f : Ω → ι → K) (x : ι → K) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ v, if f v = x then 1 else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0872 : Prop where
  proof : (∀ {K ι : Type} [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K] {Ω : Type}
      [inst : Fintype Ω] [inst : Nonempty Ω], (∀ (f : Ω → ι → K),
    ∑ x, uniformLaw f x = 1))

theorem uniformLaw_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0872] : (∀ {K ι : Type} [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K] {Ω : Type}
    [inst : Fintype Ω] [inst : Nonempty Ω], (∀ (f : Ω → ι → K),
  ∑ x, uniformLaw f x = 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0872.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0873 : Prop where
  proof : (∀ {K ι : Type} [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K] {Ω : Type}
      [inst : Fintype Ω], (∀ (f : Ω → ι → K) (g : (ι → K) → ℝ),
    ∑ x, uniformLaw f x * g x = (Fintype.card Ω : ℝ)⁻¹ * ∑ v, g (f v)))

theorem uniformLaw_average [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0873] : (∀ {K ι : Type} [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K] {Ω : Type}
    [inst : Fintype Ω], (∀ (f : Ω → ι → K) (g : (ι → K) → ℝ),
  ∑ x, uniformLaw f x * g x = (Fintype.card Ω : ℝ)⁻¹ * ∑ v, g (f v))) := @OAI.SidorenkoCounterexample.ProofCertificate_0873.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0874 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K]
      {Ω : Type} [inst : Fintype Ω], (∀ (ψ : AddChar K ℂ) (f : Ω → ι → K) (t : ι → K),
    finiteFourier ψ (uniformLaw f) t =
          (Fintype.card Ω : ℂ)⁻¹ * ∑ v, ψ (t ⬝ᵥ f v)))

theorem finiteFourier_uniformLaw [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0874] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι] [inst : DecidableEq K]
    {Ω : Type} [inst : Fintype Ω], (∀ (ψ : AddChar K ℂ) (f : Ω → ι → K) (t : ι → K),
  finiteFourier ψ (uniformLaw f) t =
        (Fintype.card Ω : ℂ)⁻¹ * ∑ v, ψ (t ⬝ᵥ f v))) := @OAI.SidorenkoCounterexample.ProofCertificate_0874.proof certificateEvidence
end

variable {V : Type} [AddCommGroup V] [Module K V] [Fintype V]
noncomputable def quadraticMap (B : ι → LinearMap.BilinForm K V)
    (l : ι → V →ₗ[K] K) (c : ι → K) (v : V) (i : ι) : K :=
  B i v v + l i v + c i

section
attribute [local instance] certificateFintype
class ProofCertificate_0875 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst_1 : Fintype ι] {V : Type} [inst_2 : AddCommGroup V]
      [inst : @_root_.Module K V _ _], (∀ (B : ι → LinearMap.BilinForm K V)
        (l : ι → V →ₗ[K] K) (c t : ι → K) (v : V),
    t ⬝ᵥ quadraticMap B l c v =
          (∑ i, t i • B i) v v + (∑ i, t i • l i) v + ∑ i, t i * c i))

theorem quadraticMap_frequency [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0875] : (∀ {K ι : Type} [inst : Field K] [inst_1 : Fintype ι] {V : Type} [inst_2 : AddCommGroup V]
    [inst : @_root_.Module K V _ _], (∀ (B : ι → LinearMap.BilinForm K V)
      (l : ι → V →ₗ[K] K) (c t : ι → K) (v : V),
  t ⬝ᵥ quadraticMap B l c v =
        (∑ i, t i • B i) v v + (∑ i, t i • l i) v + ∑ i, t i * c i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0875.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0876 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : Fintype ι] [inst_3 : DecidableEq ι]
      [inst_4 : DecidableEq K] {V : Type} [inst_5 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype V],
      (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
        (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c t : ι → K),
    ‖finiteFourier ψ (uniformLaw (quadraticMap B l c)) t‖^2 ≤
          1 / (Fintype.card K : ℝ) ^ finrank K (∑ i, t i • B i).range))

theorem quadraticMap_fourier_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0876] : (∀ {K ι : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : Fintype ι] [inst_3 : DecidableEq ι]
    [inst_4 : DecidableEq K] {V : Type} [inst_5 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype V],
    (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
      (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c t : ι → K),
  ‖finiteFourier ψ (uniformLaw (quadraticMap B l c)) t‖^2 ≤
        1 / (Fintype.card K : ℝ) ^ finrank K (∑ i, t i • B i).range)) := @OAI.SidorenkoCounterexample.ProofCertificate_0876.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0877 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : Fintype ι] [inst_3 : DecidableEq ι]
      [inst_4 : DecidableEq K] {V : Type} [inst_5 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype V],
      (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
        (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
        (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c : ι → K)
        (hrank : ∀ t : ι → K, t ≠ 0 →
          Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range),
    (∑ x, |uniformLaw (quadraticMap B l c) x -
          (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤ 1 / (Fintype.card K : ℝ)))

theorem quadraticMap_joint_l1_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0877] : (∀ {K ι : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : Fintype ι] [inst_3 : DecidableEq ι]
    [inst_4 : DecidableEq K] {V : Type} [inst_5 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype V],
    (∀ (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
      (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
      (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c : ι → K)
      (hrank : ∀ t : ι → K, t ≠ 0 →
        Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range),
  (∑ x, |uniformLaw (quadraticMap B l c) x -
        (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤ 1 / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0877.proof certificateEvidence
end

end Fourier
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SignMoments
variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι]
noncomputable def characterProduct (x : ι → K) : ℝ := ∏ i, (quadraticChar K (x i) : ℝ)

section
attribute [local instance] certificateFintype
class ProofCertificate_0878 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype ι], (∀ (x : ι → K),
    |characterProduct x| ≤ 1))

theorem characterProduct_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0878] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype ι], (∀ (x : ι → K),
  |characterProduct x| ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0878.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0879 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype ι] [inst : DecidableEq ι],
      (∀ [Nonempty ι] (hodd : ringChar K ≠ 2),
    ∑ x : ι → K, characterProduct x = 0))

theorem characterProduct_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0879] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype ι] [inst : DecidableEq ι],
    (∀ [Nonempty ι] (hodd : ringChar K ≠ 2),
  ∑ x : ι → K, characterProduct x = 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0879.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0880 : Prop where
  proof : (∀ {K ι : Type} [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι], (∀ (μ ν : (ι → K) → ℝ) (g : (ι → K) → ℝ)
        (hg : ∀ x, |g x| ≤ 1),
    |(∑ x, μ x * g x) - ∑ x, ν x * g x| ≤ ∑ x, |μ x-ν x|))

theorem bounded_test_l1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0880] : (∀ {K ι : Type} [inst : Fintype K] [inst : Fintype ι] [inst : DecidableEq ι], (∀ (μ ν : (ι → K) → ℝ) (g : (ι → K) → ℝ)
      (hg : ∀ x, |g x| ≤ 1),
  |(∑ x, μ x * g x) - ∑ x, ν x * g x| ≤ ∑ x, |μ x-ν x|)) := @OAI.SidorenkoCounterexample.ProofCertificate_0880.proof certificateEvidence
end

variable {V : Type} [AddCommGroup V] [Module K V] [Fintype V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0881 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : Fintype ι]
      [inst_4 : DecidableEq ι] {V : Type} [inst_5 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype V],
      (∀ [Nonempty ι]
        (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (hodd : (2:K) ≠ 0)
        (B : ι → LinearMap.BilinForm K V) (hB : ∀ i, (B i).IsSymm)
        (l : ι → V →ₗ[K] K) (c : ι → K)
        (hrank : ∀ t : ι → K, t ≠ 0 →
          Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range),
    ((Fintype.card V : ℝ)⁻¹ * ∑ v, characterProduct (quadraticMap B l c v))^2 ≤
          1 / (Fintype.card K : ℝ)))

theorem quadraticMap_character_moment [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0881] : (∀ {K ι : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] [inst_3 : Fintype ι]
    [inst_4 : DecidableEq ι] {V : Type} [inst_5 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype V],
    (∀ [Nonempty ι]
      (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (hodd : (2:K) ≠ 0)
      (B : ι → LinearMap.BilinForm K V) (hB : ∀ i, (B i).IsSymm)
      (l : ι → V →ₗ[K] K) (c : ι → K)
      (hrank : ∀ t : ι → K, t ≠ 0 →
        Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range),
  ((Fintype.card V : ℝ)⁻¹ * ∑ v, characterProduct (quadraticMap B l c v))^2 ≤
        1 / (Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0881.proof certificateEvidence
end

end SignMoments
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Mom
variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] {N : ℕ}
section
attribute [local instance] certificateFintype
class ProofCertificate_0882 : Prop where
  proof : (∀ {K : Type} [inst : Field K] {N : Nat}, (∀ (M : Matrix (Fin N) (Fin N) K),
    finrank K M.toBilin'.range=M.rank))

theorem matrix_form_rank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0882] : (∀ {K : Type} [inst : Field K] {N : Nat}, (∀ (M : Matrix (Fin N) (Fin N) K),
  finrank K M.toBilin'.range=M.rank)) := @OAI.SidorenkoCounterexample.ProofCertificate_0882.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0883 : Prop where
  proof : (∀ {K : Type} [inst : Field K] {N : Nat}, (∀ (M : SymMatrix K N) (z w : Fin N → K) (a : K),
    a-(z-w) ⬝ᵥ M.val⁻¹.mulVec (z-w) =
          (-M.val⁻¹.toBilin') z z + (2 • (M.val⁻¹.toBilin' w)) z +
            (a-M.val⁻¹.toBilin' w w)))

theorem schur_polynomial [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0883] : (∀ {K : Type} [inst : Field K] {N : Nat}, (∀ (M : SymMatrix K N) (z w : Fin N → K) (a : K),
  a-(z-w) ⬝ᵥ M.val⁻¹.mulVec (z-w) =
        (-M.val⁻¹.toBilin') z z + (2 • (M.val⁻¹.toBilin' w)) z +
          (a-M.val⁻¹.toBilin' w w))) := @OAI.SidorenkoCounterexample.ProofCertificate_0883.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0884 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype ι] {N : Nat}, (∀ (M : ι → SymMatrix K N) (t : ι → K),
    finrank K (∑ i, t i • (-((M i).val⁻¹.toBilin'))).range =
          (∑ i, t i • (M i).val⁻¹).rank))

theorem inverse_form_span_rank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0884] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype ι] {N : Nat}, (∀ (M : ι → SymMatrix K N) (t : ι → K),
  finrank K (∑ i, t i • (-((M i).val⁻¹.toBilin'))).range =
        (∑ i, t i • (M i).val⁻¹).rank)) := @OAI.SidorenkoCounterexample.ProofCertificate_0884.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0885 : Prop where
  proof : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype ι] [inst : DecidableEq ι]
      [inst : Nonempty ι] {N : Nat}, (∀ (hodd : ringChar K≠2)
        (M : ι → SymMatrix K N) (hM : ∀ i, (M i).val.det≠0)
        (w : ι → Fin N → K) (a : ι → K)
        (hrank : ∀ t : ι → K, t≠0 →
          Fintype.card ι+1≤(∑ i, t i • (M i).val⁻¹).rank),
    (uniformMean (fun z : Fin N → K =>
          ∏ i, (quadraticChar K (symmetricBorder (M i) (z-w i) (a i)).val.det : ℝ)))^2 ≤
          1/(Fintype.card K : ℝ)))

theorem schur_sign_moment [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0885] : (∀ {K ι : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype ι] [inst : DecidableEq ι]
    [inst : Nonempty ι] {N : Nat}, (∀ (hodd : ringChar K≠2)
      (M : ι → SymMatrix K N) (hM : ∀ i, (M i).val.det≠0)
      (w : ι → Fin N → K) (a : ι → K)
      (hrank : ∀ t : ι → K, t≠0 →
        Fintype.card ι+1≤(∑ i, t i • (M i).val⁻¹).rank),
  (uniformMean (fun z : Fin N → K =>
        ∏ i, (quadraticChar K (symmetricBorder (M i) (z-w i) (a i)).val.det : ℝ)))^2 ≤
        1/(Fintype.card K : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0885.proof certificateEvidence
end

end Mom
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Span
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] {N : ℕ}
section
attribute [local instance] certificateFintype
class ProofCertificate_0886 : Prop where
  proof : (∀ {K I : Type} [inst : Field K] [inst : Fintype I] {N : Nat}, (∀ (t : I → K) (Q : I → SymMatrix K N),
    finrank K (weightedCombination t (fun i => matrixFormEquiv N (Q i))).val.range =
          (∑ i, t i • (Q i).val).rank))

theorem matrix_combination_form_rank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0886] : (∀ {K I : Type} [inst : Field K] [inst : Fintype I] {N : Nat}, (∀ (t : I → K) (Q : I → SymMatrix K N),
  finrank K (weightedCombination t (fun i => matrixFormEquiv N (Q i))).val.range =
        (∑ i, t i • (Q i).val).rank)) := @OAI.SidorenkoCounterexample.ProofCertificate_0886.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0887 : Prop where
  proof : (∀ {K I : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype I] [inst : DecidableEq I]
      {N : Nat}, (∀ (s : ℕ) (hs : s ≤ N),
    uniformMean (fun Q : I → SymMatrix K N => if ∃ t : I → K, t≠0 ∧
          (∑ i, t i • (Q i).val).rank ≤ s then 1 else 0)  ≤
          (Fintype.card K : ℝ)^(Fintype.card I) *
            (2^(N-s)/(Fintype.card K : ℝ)^((N-s+1).choose 2))))

theorem matrix_low_rank_span_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0887] : (∀ {K I : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype I] [inst : DecidableEq I]
    {N : Nat}, (∀ (s : ℕ) (hs : s ≤ N),
  uniformMean (fun Q : I → SymMatrix K N => if ∃ t : I → K, t≠0 ∧
        (∑ i, t i • (Q i).val).rank ≤ s then 1 else 0)  ≤
        (Fintype.card K : ℝ)^(Fintype.card I) *
          (2^(N-s)/(Fintype.card K : ℝ)^((N-s+1).choose 2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0887.proof certificateEvidence
end

noncomputable def goodMinors (M : I → SymMatrix K N) : Prop :=
  (∀ i, (M i).val.det≠0) ∧ ∀ t : I → K, t≠0 →
    Fintype.card I+1 ≤ (∑ i, t i • (M i).val⁻¹).rank

noncomputable def minorBadBound (N s : ℕ) (q : ℝ) : ℝ :=
  (s : ℝ)*N/q + q^s*(2^(N-s)/q^((N-s+1).choose 2))

section
attribute [local instance] certificateFintype
class ProofCertificate_0888 : Prop where
  proof : (∀ {K I : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype I] [inst : DecidableEq I]
      {N : Nat}, (∀ (hN : Fintype.card I ≤ N),
    uniformMean (fun M : I → SymMatrix K N => if goodMinors M then 0 else 1)  ≤
          minorBadBound N (Fintype.card I) (Fintype.card K)))

theorem badMinors_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0888] : (∀ {K I : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype I] [inst : DecidableEq I]
    {N : Nat}, (∀ (hN : Fintype.card I ≤ N),
  uniformMean (fun M : I → SymMatrix K N => if goodMinors M then 0 else 1)  ≤
        minorBadBound N (Fintype.card I) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0888.proof certificateEvidence
end

end Span
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Star
variable {K I J W : Type} [Field K] [AddCommGroup W] [Module K W]
def starDifference (v : I) (k : J → I) : (I → W) →ₗ[K] (J → W) where
  toFun X j := X v-X (k j)
  map_add' X Y := by ext j; simp only [Pi.add_apply]; abel
  map_smul' c X := by ext j; simp only [Pi.smul_apply,RingHom.id_apply,smul_sub]

section
attribute [local instance] certificateFintype
class ProofCertificate_0889 : Prop where
  proof : (∀ {K I J W : Type} [inst : Field K] [inst_1 : AddCommGroup W] [inst : @_root_.Module K W _ _], (∀ (v : I) (k : J → I) (hk : Function.Injective k)
        (hv : ∀ j, k j≠v),
    Function.Surjective (starDifference (K := K) (W := W) v k)))

theorem starDifference_surjective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0889] : (∀ {K I J W : Type} [inst : Field K] [inst_1 : AddCommGroup W] [inst : @_root_.Module K W _ _], (∀ (v : I) (k : J → I) (hk : Function.Injective k)
      (hv : ∀ j, k j≠v),
  Function.Surjective (starDifference (K := K) (W := W) v k))) := @OAI.SidorenkoCounterexample.ProofCertificate_0889.proof certificateEvidence
end

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W]
section
attribute [local instance] certificateFintype
class ProofCertificate_0890 : Prop where
  proof : (∀ {K I J W : Type} [inst : Field K] [inst_1 : AddCommGroup W] [inst : @_root_.Module K W _ _] [inst : Fintype I]
      [inst : DecidableEq I] [inst : Fintype J] [inst : DecidableEq J] [inst : Fintype W], (∀ (v : I) (k : J → I) (hk : Function.Injective k)
        (hv : ∀ j, k j≠v) (f : (J → W) → ℝ),
    uniformMean (fun X : I → W => f (fun j => X v-X (k j)))=uniformMean f))

theorem uniformMean_starDifference [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0890] : (∀ {K I J W : Type} [inst : Field K] [inst_1 : AddCommGroup W] [inst : @_root_.Module K W _ _] [inst : Fintype I]
    [inst : DecidableEq I] [inst : Fintype J] [inst : DecidableEq J] [inst : Fintype W], (∀ (v : I) (k : J → I) (hk : Function.Injective k)
      (hv : ∀ j, k j≠v) (f : (J → W) → ℝ),
  uniformMean (fun X : I → W => f (fun j => X v-X (k j)))=uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0890.proof certificateEvidence
end

end Star
section Border
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
section
attribute [local instance] certificateFintype
class ProofCertificate_0891 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ {N : ℕ} (W V : SymMatrix K N) (z w : Fin N → K) (a b : K),
    symmetricBorder W z a-symmetricBorder V w b=symmetricBorder (W-V) (z-w) (a-b)))

theorem symmetricBorder_sub [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0891] : (∀ {K : Type} [inst : Field K], (∀ {N : ℕ} (W V : SymMatrix K N) (z w : Fin N → K) (a b : K),
  symmetricBorder W z a-symmetricBorder V w b=symmetricBorder (W-V) (z-w) (a-b))) := @OAI.SidorenkoCounterexample.ProofCertificate_0891.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0892 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I] [inst : DecidableEq I], (∀ {A B : Type} [Fintype A] [Fintype B]
        (f : (I → A × B) → ℝ),
    uniformMean f=uniformMean fun a : I → A => uniformMean fun b : I → B => f (fun i => (a i,b i))))

theorem uniformMean_pi_prod [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0892] : (∀ {I : Type} [inst : Fintype I] [inst : DecidableEq I], (∀ {A B : Type} [Fintype A] [Fintype B]
      (f : (I → A × B) → ℝ),
  uniformMean f=uniformMean fun a : I → A => uniformMean fun b : I → B => f (fun i => (a i,b i)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0892.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0893 : Prop where
  proof : (∀ {K I : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype I] [inst : DecidableEq I], (∀ (N : ℕ) (f : (I → SymMatrix K (N+1)) → ℝ),
    uniformMean f=uniformMean (fun W : I → SymMatrix K N =>
          uniformMean (fun z : I → (Fin N → K) => uniformMean (fun a : I → K =>
            f (fun i => symmetricBorder (W i) (z i) (a i)))))))

theorem uniformMean_bordered [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0893] : (∀ {K I : Type} [inst : Field K] [inst : Fintype K] [inst : Fintype I] [inst : DecidableEq I], (∀ (N : ℕ) (f : (I → SymMatrix K (N+1)) → ℝ),
  uniformMean f=uniformMean (fun W : I → SymMatrix K N =>
        uniformMean (fun z : I → (Fin N → K) => uniformMean (fun a : I → K =>
          f (fun i => symmetricBorder (W i) (z i) (a i))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0893.proof certificateEvidence
end

end Border
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section StarMoment
variable {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J] {N : ℕ}
noncomputable def starSign (v : I) (k : J → I) (W : I → SymMatrix K N)
    (z : I → (Fin N → K)) (a : I → K) : ℝ :=
  ∏ j, (quadraticChar K (symmetricBorder (W v-W (k j)) (z v-z (k j)) (a v-a (k j))).val.det : ℝ)

section
attribute [local instance] certificateFintype
class ProofCertificate_0894 : Prop where
  proof : (∀ {K I J : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype J] {N : Nat}, (∀ (v : I) (k : J → I) (W : I → SymMatrix K N)
        (z : I → (Fin N → K)) (a : I → K),
    |starSign v k W z a| ≤ 1))

theorem starSign_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0894] : (∀ {K I J : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype J] {N : Nat}, (∀ (v : I) (k : J → I) (W : I → SymMatrix K N)
      (z : I → (Fin N → K)) (a : I → K),
  |starSign v k W z a| ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0894.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0895 : Prop where
  proof : (∀ {K I J : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : DecidableEq I] [inst : Fintype J]
      [inst : DecidableEq J] [inst : Nonempty J] {N : Nat}, (∀ (hK : ringChar K≠2) (v : I) (k : J → I)
        (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
        (hW : goodMinors (fun j => W v-W (k j))),
    |uniformMean (fun z' => starSign v k W (Function.update z v z') a)| ≤
          Real.sqrt (1/(Fintype.card K : ℝ))))

theorem starSign_update_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0895] : (∀ {K I J : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : DecidableEq I] [inst : Fintype J]
    [inst : DecidableEq J] [inst : Nonempty J] {N : Nat}, (∀ (hK : ringChar K≠2) (v : I) (k : J → I)
      (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
      (hW : goodMinors (fun j => W v-W (k j))),
  |uniformMean (fun z' => starSign v k W (Function.update z v z') a)| ≤
        Real.sqrt (1/(Fintype.card K : ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0895.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0896 : Prop where
  proof : (∀ {K I J : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : DecidableEq I] [inst : Fintype J]
      [inst : DecidableEq J] [inst : Nonempty J] {N : Nat}, (∀ (hK : ringChar K≠2) (v : I) (k : J → I)
        (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
        (R : (I → (Fin N → K)) → ℝ) (hR : ∀ z, |R z| ≤ 1)
        (hRi : ∀ z', R (Function.update z v z')=R z),
    |uniformMean (fun z' => R (Function.update z v z') * starSign v k W (Function.update z v z') a)| ≤
          Real.sqrt (1/(Fintype.card K : ℝ)) +
            (if goodMinors (fun j => W v-W (k j)) then 0 else 1)))

theorem testedStar_update_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0896] : (∀ {K I J : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : DecidableEq I] [inst : Fintype J]
    [inst : DecidableEq J] [inst : Nonempty J] {N : Nat}, (∀ (hK : ringChar K≠2) (v : I) (k : J → I)
      (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
      (R : (I → (Fin N → K)) → ℝ) (hR : ∀ z, |R z| ≤ 1)
      (hRi : ∀ z', R (Function.update z v z')=R z),
  |uniformMean (fun z' => R (Function.update z v z') * starSign v k W (Function.update z v z') a)| ≤
        Real.sqrt (1/(Fintype.card K : ℝ)) +
          (if goodMinors (fun j => W v-W (k j)) then 0 else 1))) := @OAI.SidorenkoCounterexample.ProofCertificate_0896.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0897 : Prop where
  proof : (∀ {K I J : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype I] [inst : DecidableEq I]
      [inst : Fintype J] [inst : DecidableEq J] [inst : Nonempty J] {N : Nat}, (∀ (hK : ringChar K≠2) (v : I) (k : J → I)
        (hk : Function.Injective k) (hv : ∀ j, k j≠v) (hN : Fintype.card J ≤ N)
        (R : (I → SymMatrix K N) → (I → (Fin N → K)) → (I → K) → ℝ)
        (hR : ∀ W z a, |R W z a| ≤ 1)
        (hRi : ∀ W z a z', R W (Function.update z v z') a=R W z a),
    |uniformMean (fun W => uniformMean fun a => uniformMean fun z => R W z a * starSign v k W z a)| ≤
           Real.sqrt (1/(Fintype.card K : ℝ)) + minorBadBound N (Fintype.card J) (Fintype.card K)))

theorem testedStar_mean_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0897] : (∀ {K I J : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] [inst : Fintype I] [inst : DecidableEq I]
    [inst : Fintype J] [inst : DecidableEq J] [inst : Nonempty J] {N : Nat}, (∀ (hK : ringChar K≠2) (v : I) (k : J → I)
      (hk : Function.Injective k) (hv : ∀ j, k j≠v) (hN : Fintype.card J ≤ N)
      (R : (I → SymMatrix K N) → (I → (Fin N → K)) → (I → K) → ℝ)
      (hR : ∀ W z a, |R W z a| ≤ 1)
      (hRi : ∀ W z a z', R W (Function.update z v z') a=R W z a),
  |uniformMean (fun W => uniformMean fun a => uniformMean fun z => R W z a * starSign v k W z a)| ≤
         Real.sqrt (1/(Fintype.card K : ℝ)) + minorBadBound N (Fintype.card J) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0897.proof certificateEvidence
end

end StarMoment
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
def pairLeft : Fin 33 → Fin 13 := ![0,0,2,0,2,0,1,2,3,1,4,1,3,3,4,1,9,4,8,1,7,10,8,7,8,5,5,5,6,6,6,6,5]

def pairRight : Fin 33 → Fin 13 := ![2,3,3,9,9,1,3,4,4,9,9,10,10,11,11,12,12,8,9,7,10,11,11,12,12,7,10,11,8,11,7,12,6]

section
attribute [local instance] certificateFintype
class ProofCertificate_0898 : Prop where
  proof : ((∀ e, pairVertices e={pairLeft e,pairRight e}))

theorem pair_endpoints [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0898] : ((∀ e, pairVertices e={pairLeft e,pairRight e})) := @OAI.SidorenkoCounterexample.ProofCertificate_0898.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0899 : Prop where
  proof : ((∀ e, pairLeft e≠pairRight e))

theorem pair_endpoints_ne [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0899] : ((∀ e, pairLeft e≠pairRight e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0899.proof certificateEvidence
end

def pairOther (v : Fin 13) (e : Fin 33) : Fin 13 := if pairLeft e=v then pairRight e else pairLeft e

section
attribute [local instance] certificateFintype
class ProofCertificate_0900 : Prop where
  proof : ((∀ (v : Fin 13) (e : Fin 33) (_hv : v∈pairVertices e),
    pairOther v e≠v))

theorem pairOther_ne [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0900] : ((∀ (v : Fin 13) (e : Fin 33) (_hv : v∈pairVertices e),
  pairOther v e≠v)) := @OAI.SidorenkoCounterexample.ProofCertificate_0900.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0901 : Prop where
  proof : ((∀ (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e),
    pairVertices e={v,pairOther v e}))

theorem pair_vertices_other [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0901] : ((∀ (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e),
  pairVertices e={v,pairOther v e})) := @OAI.SidorenkoCounterexample.ProofCertificate_0901.proof certificateEvidence
end

def selectedIncident (F : Finset (Fin 33)) (v : Fin 13) : Finset (Fin 33) :=
  F.filter (fun e => v∈pairVertices e)

section
attribute [local instance] certificateFintype
class ProofCertificate_0902 : Prop where
  proof : ((∀ (F : Finset (Fin 33)) (v : Fin 13),
    (selectedIncident F v).card ≤ 6))

theorem selectedIncident_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0902] : ((∀ (F : Finset (Fin 33)) (v : Fin 13),
  (selectedIncident F v).card ≤ 6)) := @OAI.SidorenkoCounterexample.ProofCertificate_0902.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0903 : Prop where
  proof : ((∀ (F : Finset (Fin 33)) (v : Fin 13),
    Function.Injective (fun e : selectedIncident F v => pairOther v e.val)))

theorem pairOther_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0903] : ((∀ (F : Finset (Fin 33)) (v : Fin 13),
  Function.Injective (fun e : selectedIncident F v => pairOther v e.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0903.proof certificateEvidence
end

section Signs
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
noncomputable def pairSign (X : Fin 13 → SymMatrix K D) (e : Fin 33) : ℝ :=
  quadraticChar K (X (pairLeft e)-X (pairRight e)).val.det

section
attribute [local instance] certificateFintype
class ProofCertificate_0904 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (X : Fin 13 → SymMatrix K D) (e : Fin 33),
    |pairSign X e| ≤ 1))

theorem pairSign_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0904] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (X : Fin 13 → SymMatrix K D) (e : Fin 33),
  |pairSign X e| ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0904.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0905 : Prop where
  proof : (∀ {K : Type} [inst : Field K] {D : Nat}, (∀ (hD : Even D) (A B : SymMatrix K D),
    (A-B).val.det=(B-A).val.det))

theorem determinant_difference_even [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0905] : (∀ {K : Type} [inst : Field K] {D : Nat}, (∀ (hD : Even D) (A B : SymMatrix K D),
  (A-B).val.det=(B-A).val.det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0905.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0906 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (hD : Even D) (X : Fin 13 → SymMatrix K D)
        (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e),
    pairSign X e=quadraticChar K (X v-X (pairOther v e)).val.det))

theorem pairSign_other [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0906] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (hD : Even D) (X : Fin 13 → SymMatrix K D)
      (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e),
  pairSign X e=quadraticChar K (X v-X (pairOther v e)).val.det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0906.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0907 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (F : Finset (Fin 33)) (X : Fin 13 → SymMatrix K D),
    |∏ e∈F, pairSign X e| ≤ 1))

theorem pairSign_product_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0907] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (F : Finset (Fin 33)) (X : Fin 13 → SymMatrix K D),
  |∏ e∈F, pairSign X e| ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0907.proof certificateEvidence
end

end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Moment
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}
noncomputable def nonincidentProduct (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) : ℝ :=
  ∏ e∈F\selectedIncident F v, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e

section
attribute [local instance] certificateFintype
class ProofCertificate_0908 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {N : Nat}, (∀ (F : Finset (Fin 33)) (v : Fin 13)
        (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K),
    |nonincidentProduct F v W z a| ≤ 1))

theorem nonincidentProduct_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0908] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {N : Nat}, (∀ (F : Finset (Fin 33)) (v : Fin 13)
      (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K),
  |nonincidentProduct F v W z a| ≤ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0908.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0909 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {N : Nat}, (∀ (F : Finset (Fin 33)) (v : Fin 13)
        (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K)
        (z' : Fin N → K),
    nonincidentProduct F v W (Function.update z v z') a=
          nonincidentProduct F v W z a))

theorem nonincidentProduct_update [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0909] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {N : Nat}, (∀ (F : Finset (Fin 33)) (v : Fin 13)
      (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K)
      (z' : Fin N → K),
  nonincidentProduct F v W (Function.update z v z') a=
        nonincidentProduct F v W z a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0909.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0910 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {N : Nat}, (∀ (hN : Even (N+1)) (F : Finset (Fin 33)) (v : Fin 13)
        (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K),
    (∏ e∈F, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e)=
          nonincidentProduct F v W z a * starSign v
            (fun e : selectedIncident F v => pairOther v e.val) W z a))

theorem pairSign_product_split [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0910] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {N : Nat}, (∀ (hN : Even (N+1)) (F : Finset (Fin 33)) (v : Fin 13)
      (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K),
  (∏ e∈F, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e)=
        nonincidentProduct F v W z a * starSign v
          (fun e : selectedIncident F v => pairOther v e.val) W z a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0910.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0911 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {N : Nat}, (∀ (hK : ringChar K≠2) (hN : Even (N+1))
        (F : Finset (Fin 33)) (v : Fin 13) (hne : (selectedIncident F v).Nonempty)
        (hc : (selectedIncident F v).card ≤ N),
    |uniformMean (fun X : Fin 13 → SymMatrix K (N+1) => ∏ e∈F, pairSign X e)| ≤
          Real.sqrt (1/(Fintype.card K : ℝ)) +
            minorBadBound N (selectedIncident F v).card (Fintype.card K)))

theorem pairSign_moment_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0911] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {N : Nat}, (∀ (hK : ringChar K≠2) (hN : Even (N+1))
      (F : Finset (Fin 33)) (v : Fin 13) (hne : (selectedIncident F v).Nonempty)
      (hc : (selectedIncident F v).card ≤ N),
  |uniformMean (fun X : Fin 13 → SymMatrix K (N+1) => ∏ e∈F, pairSign X e)| ≤
        Real.sqrt (1/(Fintype.card K : ℝ)) +
          minorBadBound N (selectedIncident F v).card (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0911.proof certificateEvidence
end

end Moment
section
attribute [local instance] certificateFintype
class ProofCertificate_0912 : Prop where
  proof : ((∀ (N s : ℕ) (h : s<(N-s+1).choose 2),
    Tendsto (minorBadBound N s) atTop (nhds 0)))

theorem minorBadBound_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0912] : ((∀ (N s : ℕ) (h : s<(N-s+1).choose 2),
  Tendsto (minorBadBound N s) atTop (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0912.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0913 : Prop where
  proof : ((∀ (N s : ℕ) (hN : 11≤N) (hs : s≤6),
    s≤N ∧ s<(N-s+1).choose 2))

theorem sign_moment_dimension [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0913] : ((∀ (N s : ℕ) (hN : 11≤N) (hs : s≤6),
  s≤N ∧ s<(N-s+1).choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0913.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0914 : Prop where
  proof : ((∀ (D : ℕ) (hD : Even D) (hbig : 12≤D)
        (F : Finset (Fin 33)) (hF : F.Nonempty),
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
          ∏ e∈F, pairSign X e)) primeInfinity (nhds 0)))

theorem pairSign_moment_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0914] : ((∀ (D : ℕ) (hD : Even D) (hbig : 12≤D)
      (F : Finset (Fin 33)) (hF : F.Nonempty),
  Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
        ∏ e∈F, pairSign X e)) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0914.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Product
variable {I : Type} [DecidableEq I]
section
attribute [local instance] certificateFintype
class ProofCertificate_0915 : Prop where
  proof : (∀ {I : Type}, (∀ (s : Finset I) (f : I → ℝ) {C : ℝ} (_hC : 0≤C)
        (hf : ∀ i∈s, |f i|≤C),
    |∏ i∈s, f i|≤C^s.card))

theorem abs_prod_le_pow [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0915] : (∀ {I : Type}, (∀ (s : Finset I) (f : I → ℝ) {C : ℝ} (_hC : 0≤C)
      (hf : ∀ i∈s, |f i|≤C),
  |∏ i∈s, f i|≤C^s.card)) := @OAI.SidorenkoCounterexample.ProofCertificate_0915.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0916 : Prop where
  proof : (∀ {I : Type} [inst : DecidableEq I], (∀ (s : Finset I) (f g : I → ℝ) {C : ℝ} (hC : 1≤C)
        (hf : ∀ i∈s, |f i|≤C) (hg : ∀ i∈s, |g i|≤C),
    |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ C^s.card * ∑ i∈s, |f i-g i|))

theorem product_difference_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0916] : (∀ {I : Type} [inst : DecidableEq I], (∀ (s : Finset I) (f g : I → ℝ) {C : ℝ} (hC : 1≤C)
      (hf : ∀ i∈s, |f i|≤C) (hg : ∀ i∈s, |g i|≤C),
  |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ C^s.card * ∑ i∈s, |f i-g i|)) := @OAI.SidorenkoCounterexample.ProofCertificate_0916.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0917 : Prop where
  proof : (∀ {I : Type} [inst : DecidableEq I], (∀ (s : Finset I) (f g : I → ℝ)
        (hf : ∀ i∈s, |f i|≤1) (hg : ∀ i∈s, |g i|≤1),
    |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ ∑ i∈s, |f i-g i|))

theorem product_difference_unit [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0917] : (∀ {I : Type} [inst : DecidableEq I], (∀ (s : Finset I) (f g : I → ℝ)
      (hf : ∀ i∈s, |f i|≤1) (hg : ∀ i∈s, |g i|≤1),
  |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ ∑ i∈s, |f i-g i|)) := @OAI.SidorenkoCounterexample.ProofCertificate_0917.proof certificateEvidence
end

end Product
section Mean
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]
section
attribute [local instance] certificateFintype
class ProofCertificate_0918 : Prop where
  proof : (∀ {I A : Type} [inst : Fintype A], (∀ (s : Finset I) (f : I → A → ℝ),
    uniformMean (fun a => ∑ i∈s, f i a)=∑ i∈s, uniformMean (f i)))

theorem uniformMean_finset_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0918] : (∀ {I A : Type} [inst : Fintype A], (∀ (s : Finset I) (f : I → A → ℝ),
  uniformMean (fun a => ∑ i∈s, f i a)=∑ i∈s, uniformMean (f i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0918.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0919 : Prop where
  proof : (∀ {I A : Type} [inst : Fintype I] [inst : DecidableEq I] [inst : Fintype A], (∀ (f : I → A → ℝ),
    uniformMean (fun x : I → A => ∏ i, f i (x i))=∏ i, uniformMean (f i)))

theorem uniformMean_pi_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0919] : (∀ {I A : Type} [inst : Fintype I] [inst : DecidableEq I] [inst : Fintype A], (∀ (f : I → A → ℝ),
  uniformMean (fun x : I → A => ∏ i, f i (x i))=∏ i, uniformMean (f i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0919.proof certificateEvidence
end

end Mean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Difference
variable {K I W : Type} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
section
attribute [local instance] certificateFintype
class ProofCertificate_0920 : Prop where
  proof : (∀ {K I W : Type} [inst : Field K] [inst_1 : Fintype I] [inst_2 : DecidableEq I] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _] [inst : Fintype W], (∀ (i k : I) (hik : i≠k) (f : W → ℝ),
    uniformMean (fun X : I → W => f (X i-X k))=uniformMean f))

theorem uniformMean_point_difference [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0920] : (∀ {K I W : Type} [inst : Field K] [inst_1 : Fintype I] [inst_2 : DecidableEq I] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _] [inst : Fintype W], (∀ (i k : I) (hik : i≠k) (f : W → ℝ),
  uniformMean (fun X : I → W => f (X i-X k))=uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0920.proof certificateEvidence
end

end Difference
section Pair
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
noncomputable def pairSingular (X : Fin 13 → SymMatrix K D) (e : Fin 33) : ℝ :=
  if (X (pairLeft e)-X (pairRight e)).val.det=0 then 1 else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0921 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : DecidableEq K] {D : Nat}, (∀ (X : Fin 13 → SymMatrix K D) (e : Fin 33),
    0≤pairSingular X e))

theorem pairSingular_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0921] : (∀ {K : Type} [inst : Field K] [inst : DecidableEq K] {D : Nat}, (∀ (X : Fin 13 → SymMatrix K D) (e : Fin 33),
  0≤pairSingular X e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0921.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0922 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (e : Fin 33),
    uniformMean (fun X : Fin 13 → SymMatrix K D => pairSingular X e)≤(D : ℝ)/Fintype.card K))

theorem pairSingular_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0922] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (e : Fin 33),
  uniformMean (fun X : Fin 13 → SymMatrix K D => pairSingular X e)≤(D : ℝ)/Fintype.card K)) := @OAI.SidorenkoCounterexample.ProofCertificate_0922.proof certificateEvidence
end

def fullTransverse (X : Fin 13 → SymMatrix K D) : Prop :=
  ∀ e : Fin 33, (X (pairLeft e)-X (pairRight e)).val.det≠0

section
attribute [local instance] certificateFintype
class ProofCertificate_0923 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : DecidableEq K] {D : Nat}, (∀ (X : Fin 13 → SymMatrix K D),
    (if fullTransverse X then 0 else 1 : ℝ) ≤ ∑ e, pairSingular X e))

theorem nonTransverse_pointwise [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0923] : (∀ {K : Type} [inst : Field K] [inst : DecidableEq K] {D : Nat}, (∀ (X : Fin 13 → SymMatrix K D),
  (if fullTransverse X then 0 else 1 : ℝ) ≤ ∑ e, pairSingular X e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0923.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0924 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (uniformMean (fun X : Fin 13 → SymMatrix K D => if fullTransverse X then 0 else 1) ≤
          33*((D : ℝ)/Fintype.card K)))

theorem nonTransverse_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0924] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (uniformMean (fun X : Fin 13 → SymMatrix K D => if fullTransverse X then 0 else 1) ≤
        33*((D : ℝ)/Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0924.proof certificateEvidence
end

noncomputable def pairBool (X : Fin 13 → SymMatrix K D) (e : Fin 33) : Bool :=
  decide (pairSign X e=1)

def boolSign (b : Bool) : ℝ := if b then 1 else -1

section
attribute [local instance] certificateFintype
class ProofCertificate_0925 : Prop where
  proof : ((∀ (b : Bool),
    |boolSign b|=1))

@[simp]
theorem boolSign_abs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0925] : ((∀ (b : Bool),
  |boolSign b|=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0925.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0926 : Prop where
  proof : ((∀ (b : Bool),
    boolSign b^2=1))

@[simp]
theorem boolSign_sq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0926] : ((∀ (b : Bool),
  boolSign b^2=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0926.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0927 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (X : Fin 13 → SymMatrix K D) (e : Fin 33),
    |boolSign (pairBool X e)-pairSign X e| ≤ pairSingular X e))

theorem pairBool_error [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0927] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (X : Fin 13 → SymMatrix K D) (e : Fin 33),
  |boolSign (pairBool X e)-pairSign X e| ≤ pairSingular X e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0927.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0928 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (F : Finset (Fin 33)),
    |uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, boolSign (pairBool X e))-
          uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, pairSign X e)| ≤
            (F.card : ℝ)*((D : ℝ)/Fintype.card K)))

theorem pairBool_moment_error [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0928] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K] {D : Nat}, (∀ (F : Finset (Fin 33)),
  |uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, boolSign (pairBool X e))-
        uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, pairSign X e)| ≤
          (F.card : ℝ)*((D : ℝ)/Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0928.proof certificateEvidence
end

end Pair
section
attribute [local instance] certificateFintype
class ProofCertificate_0929 : Prop where
  proof : ((∀ (D : ℕ) (hD : Even D) (hbig : 12≤D)
        (F : Finset (Fin 33)) (hF : F.Nonempty),
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
          ∏ e∈F, boolSign (pairBool X e))) primeInfinity (nhds 0)))

theorem pairBool_moment_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0929] : ((∀ (D : ℕ) (hD : Even D) (hbig : 12≤D)
      (F : Finset (Fin 33)) (hF : F.Nonempty),
  Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
        ∏ e∈F, boolSign (pairBool X e))) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0929.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Graph
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
noncomputable def fullGraphIntersection (B C : LinearMap.BilinForm K V) :
    (B-C).ker ≃ₗ[K] ↥(B.graph⊓C.graph) where
  toFun x := ⟨(x.val,B x.val),by
    constructor
    · rfl
    · apply (C.mem_graph_iff _).mpr
      exact sub_eq_zero.mp (show B x.val-C x.val=0 from x.property)⟩
  invFun x := ⟨x.val.1,by
    have hb := (B.mem_graph_iff _).mp x.property.1
    have hc := (C.mem_graph_iff _).mp x.property.2
    change B x.val.1-C x.val.1=0
    rw [←hb,←hc,sub_self]⟩
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl ((B.mem_graph_iff _).mp x.property.1).symm
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198]
noncomputable def matrixLagrangian {D : ℕ} (M : SymMatrix K D) :
    SymplecticLagrangian (canonicalSymplectic (K := K) (V := Fin D → K)) :=
  ⟨M.val.toBilin'.graph, fullGraph_selforthogonal _ (Matrix.isSymm_toBilin'_iff_isSymm.mpr M.property)⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0930 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K], (∀ (D : ℕ),
    Function.Injective (matrixLagrangian (K := K) (D := D))))

theorem matrixLagrangian_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0930] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K], (∀ (D : ℕ),
  Function.Injective (matrixLagrangian (K := K) (D := D)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0930.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0931 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K], (∀ (D : ℕ) (A B : SymMatrix K D),
    finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)+(A-B).val.rank=D))

theorem matrixLagrangian_pair_rank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0931] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K], (∀ (D : ℕ) (A B : SymMatrix K D),
  finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)+(A-B).val.rank=D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0931.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0932 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K], (∀ (D : ℕ) (A B : SymMatrix K D),
    finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)=0 ↔ (A-B).val.det≠0))

theorem matrixLagrangian_pair_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0932] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K], (∀ (D : ℕ) (A B : SymMatrix K D),
  finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)=0 ↔ (A-B).val.det≠0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0932.proof certificateEvidence
end

end Graph
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Mean
variable {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
section
attribute [local instance] certificateFintype
class ProofCertificate_0933 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B] [inst : Nonempty B], (∀ (i : A → B) (hi : Function.Injective i) (f : B → ℝ)
        (hf : ∀ b,0≤f b),
    uniformMean (f ∘ i) ≤
          ((Fintype.card B : ℝ)/Fintype.card A)*uniformMean f))

theorem uniformMean_injection [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0933] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B] [inst : Nonempty B], (∀ (i : A → B) (hi : Function.Injective i) (f : B → ℝ)
      (hf : ∀ b,0≤f b),
  uniformMean (f ∘ i) ≤
        ((Fintype.card B : ℝ)/Fintype.card A)*uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0933.proof certificateEvidence
end

end Mean
section Norm
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def canonicalStratumMass (D r : ℕ) : ℝ :=
  (Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)/
    Nat.card (Lagrangian (K := K) (V := Fin D → K))

noncomputable def chartRatio (D : ℕ) : ℝ :=
  (Nat.card (Lagrangian (K := K) (V := Fin D → K)) : ℝ)/
    Fintype.card (SymMatrix K D)

section
attribute [local instance] certificateFintype
class ProofCertificate_0934 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D : ℕ),
    0≤chartRatio (K := K) D))

theorem chartRatio_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0934] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D : ℕ),
  0≤chartRatio (K := K) D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0934.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0935 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D : ℕ),
    chartRatio (K := K) D≤lagrangianConstant D))

theorem chartRatio_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0935] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D : ℕ),
  chartRatio (K := K) D≤lagrangianConstant D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0935.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0936 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D r : ℕ) (hr : r≤D),
    Nat.card (CenterStratum (K := K) (V := Fin D → K) r) =
          Nat.card (DimSubspace K (Fin D → K) (D-r)) * (Fintype.card K)^((D-r+1).choose 2)))

theorem canonicalStratum_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0936] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D r : ℕ) (hr : r≤D),
  Nat.card (CenterStratum (K := K) (V := Fin D → K) r) =
        Nat.card (DimSubspace K (Fin D → K) (D-r)) * (Fintype.card K)^((D-r+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0936.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0937 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D : ℕ),
    (0 : ℝ)<Nat.card (Lagrangian (K := K) (V := Fin D → K))))

theorem canonicalLag_card_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0937] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D : ℕ),
  (0 : ℝ)<Nat.card (Lagrangian (K := K) (V := Fin D → K)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0937.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0938 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D r : ℕ) (hr : r≤D),
    0<canonicalStratumMass (K := K) D r))

theorem canonicalStratumMass_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0938] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D r : ℕ) (hr : r≤D),
  0<canonicalStratumMass (K := K) D r)) := @OAI.SidorenkoCounterexample.ProofCertificate_0938.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0939 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D r : ℕ) (hr : r≤D),
    canonicalStratumMass (K := K) D r*(Fintype.card K : ℝ)^((r+1).choose 2)≤2^(D-r)))

theorem canonicalStratumMass_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0939] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (D r : ℕ) (hr : r≤D),
  canonicalStratumMass (K := K) D r*(Fintype.card K : ℝ)^((r+1).choose 2)≤2^(D-r))) := @OAI.SidorenkoCounterexample.ProofCertificate_0939.proof certificateEvidence
end

end Norm
section
attribute [local instance] certificateFintype
class ProofCertificate_0940 : Prop where
  proof : ((∀ (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
    ∀ᶠ q : OddPrime in primeInfinity,
          canonicalStratumMass (K := ZMod q.val) (2*r) r /
            layerMass (ZMod q.val) (2*r) r ξ ≤ 4*2^r))

theorem signed_normalization_eventually [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0940] : ((∀ (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1),
  ∀ᶠ q : OddPrime in primeInfinity,
        canonicalStratumMass (K := ZMod q.val) (2*r) r /
          layerMass (ZMod q.val) (2*r) r ξ ≤ 4*2^r)) := @OAI.SidorenkoCounterexample.ProofCertificate_0940.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Face
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def faceLocal (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun Y => ∏ k∈T, rankKernel K (2*r) r (ξ k) (X k-Y))

section
attribute [local instance] certificateFintype
class ProofCertificate_0941 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)),
    faceLocal r ∅ ξ X=1))

@[simp]
theorem faceLocal_empty [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0941] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)),
  faceLocal r ∅ ξ X=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0941.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0942 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
        (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)) (k : Fin 3),
    faceLocal r {k} ξ X=1))

theorem faceLocal_singleton [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0942] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
      (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)) (k : Fin 3),
  faceLocal r {k} ξ X=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0942.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0943 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r))
        (k l : Fin 3) (hkl : k≠l),
    faceLocal r {k,l} ξ X=pairLocal r (ξ k) (ξ l) (X k-X l)))

theorem faceLocal_pair [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0943] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r))
      (k l : Fin 3) (hkl : k≠l),
  faceLocal r {k,l} ξ X=pairLocal r (ξ k) (ξ l) (X k-X l))) := @OAI.SidorenkoCounterexample.ProofCertificate_0943.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0944 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)),
    faceLocal r Finset.univ ξ X=tripleLocal r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)))

theorem faceLocal_full [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0944] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)),
  faceLocal r Finset.univ ξ X=tripleLocal r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0944.proof certificateEvidence
end

noncomputable def pairPolynomial (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  1+(quadraticChar K ((-1 : K)^r) : ℝ)*(quadraticChar K B.val.det : ℝ)*(ξ : ℝ)*(ζ : ℝ)

section
attribute [local instance] certificateFintype
class ProofCertificate_0945 : Prop where
  proof : ((∀ (c x ξ ζ : ℤ) (hc : c=1 ∨ c= -1) (hx : x=1 ∨ x= -1)
        (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1),
    (1+(c : ℝ)*(x : ℝ)*(ξ : ℝ)*(ζ : ℝ))=(if x=c*ξ*ζ then 2 else 0)))

theorem signs_polynomial [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0945] : ((∀ (c x ξ ζ : ℤ) (hc : c=1 ∨ c= -1) (hx : x=1 ∨ x= -1)
      (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1),
  (1+(c : ℝ)*(x : ℝ)*(ξ : ℝ)*(ζ : ℝ))=(if x=c*ξ*ζ then 2 else 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0945.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0946 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
        (B : SymMatrix K (2*r)) (hB : B.val.det≠0),
    pairPolynomial r ξ ζ B=if pairMatch r ξ ζ B then 2 else 0))

theorem pairPolynomial_eq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0946] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
      (B : SymMatrix K (2*r)) (hB : B.val.det≠0),
  pairPolynomial r ξ ζ B=if pairMatch r ξ ζ B then 2 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0946.proof certificateEvidence
end

noncomputable def facePolynomial (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  (if 0∈T ∧ 1∈T then pairPolynomial r (ξ 0) (ξ 1) (X 0-X 1) else 1)*
  (if 0∈T ∧ 2∈T then pairPolynomial r (ξ 0) (ξ 2) (X 0-X 2) else 1)*
  (if 1∈T ∧ 2∈T then pairPolynomial r (ξ 1) (ξ 2) (X 1-X 2) else 1)

def faceTransverse (r : ℕ) (X : Fin 3 → SymMatrix K (2*r)) : Prop :=
  (X 0-X 1).val.det≠0 ∧ (X 0-X 2).val.det≠0 ∧ (X 1-X 2).val.det≠0

section
attribute [local instance] certificateFintype
class ProofCertificate_0947 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
        (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X),
    facePolynomial r Finset.univ ξ X=
          if tripleMatch r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) then 8 else 0))

theorem facePolynomial_full [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0947] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
      (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X),
  facePolynomial r Finset.univ ξ X=
        if tripleMatch r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) then 8 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0947.proof certificateEvidence
end

noncomputable def faceError (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  pairError r (ξ 0) (ξ 1) (X 0-X 1)+pairError r (ξ 0) (ξ 2) (X 0-X 2)+
    pairError r (ξ 1) (ξ 2) (X 1-X 2)+tripleError r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)

section
attribute [local instance] certificateFintype
class ProofCertificate_0948 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)),
    0≤faceError r ξ X))

theorem faceError_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0948] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)),
  0≤faceError r ξ X)) := @OAI.SidorenkoCounterexample.ProofCertificate_0948.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0949 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r) (T : Finset (Fin 3))
        (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
        (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X),
    |faceLocal r T ξ X-facePolynomial r T ξ X|≤faceError r ξ X))

theorem faceLocal_error [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0949] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r) (T : Finset (Fin 3))
      (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
      (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X),
  |faceLocal r T ξ X-facePolynomial r T ξ X|≤faceError r ξ X)) := @OAI.SidorenkoCounterexample.ProofCertificate_0949.proof certificateEvidence
end

end Face
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Boolean
variable {I : Type} [Fintype I] [DecidableEq I]
noncomputable def boolMonomial (F : Finset I) (η : I → Bool) : ℝ := ∏ i∈F, boolSign (η i)

section
attribute [local instance] certificateFintype
class ProofCertificate_0950 : Prop where
  proof : (∀ {I : Type}, (∀ (η : I → Bool),
    boolMonomial ∅ η=1))

@[simp]
theorem boolMonomial_empty [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0950] : (∀ {I : Type}, (∀ (η : I → Bool),
  boolMonomial ∅ η=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0950.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0951 : Prop where
  proof : ((∀ (a b : Bool),
    1+boolSign a*boolSign b=if a=b then 2 else 0))

theorem bool_factor [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0951] : ((∀ (a b : Bool),
  1+boolSign a*boolSign b=if a=b then 2 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0951.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0952 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I], (∀ (η ε : I → Bool),
    (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
          ∏ i, (1+boolSign (η i)*boolSign (ε i))))

theorem bool_indicator_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0952] : (∀ {I : Type} [inst : Fintype I], (∀ (η ε : I → Bool),
  (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
        ∏ i, (1+boolSign (η i)*boolSign (ε i)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0952.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0953 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I], (∀ (η ε : I → Bool),
    (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
          ∑ F : Finset I, boolMonomial F η * boolMonomial F ε))

theorem bool_indicator_expansion [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0953] : (∀ {I : Type} [inst : Fintype I], (∀ (η ε : I → Bool),
  (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
        ∑ F : Finset I, boolMonomial F η * boolMonomial F ε)) := @OAI.SidorenkoCounterexample.ProofCertificate_0953.proof certificateEvidence
end

variable {A : Type} [Fintype A]
section
attribute [local instance] certificateFintype
class ProofCertificate_0954 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I] {A : Type} [inst : Fintype A], (∀ (T : A → I → Bool) (ε : I → Bool),
    uniformMean (fun a => if T a=ε then 1 else 0)=
          (2^Fintype.card I : ℝ)⁻¹ * ∑ F : Finset I,
            (uniformMean fun a => boolMonomial F (T a))*boolMonomial F ε))

theorem bool_law_expansion [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0954] : (∀ {I : Type} [inst : Fintype I] {A : Type} [inst : Fintype A], (∀ (T : A → I → Bool) (ε : I → Bool),
  uniformMean (fun a => if T a=ε then 1 else 0)=
        (2^Fintype.card I : ℝ)⁻¹ * ∑ F : Finset I,
          (uniformMean fun a => boolMonomial F (T a))*boolMonomial F ε)) := @OAI.SidorenkoCounterexample.ProofCertificate_0954.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0955 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I] [inst : DecidableEq I] {A : Type} [inst : Fintype A], (∀ (T : A → I → Bool) (g : (I → Bool) → ℝ),
    uniformMean (fun a => g (T a))=
          ∑ ε : I → Bool, g ε * uniformMean (fun a => if T a=ε then 1 else 0)))

theorem uniformMean_test_fibers [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0955] : (∀ {I : Type} [inst : Fintype I] [inst : DecidableEq I] {A : Type} [inst : Fintype A], (∀ (T : A → I → Bool) (g : (I → Bool) → ℝ),
  uniformMean (fun a => g (T a))=
        ∑ ε : I → Bool, g ε * uniformMean (fun a => if T a=ε then 1 else 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0955.proof certificateEvidence
end

end Boolean
section Convergence
variable {I Q : Type} [Fintype I] [DecidableEq I] {l : Filter Q}
  {A : Q → Type} [∀ q, Fintype (A q)] [∀ q, Nonempty (A q)]
section
attribute [local instance] certificateFintype
class ProofCertificate_0956 : Prop where
  proof : (∀ {I Q : Type} [inst : Fintype I] [inst : DecidableEq I] {l : Filter Q} {A : (a : Q) → Type}
      [inst : (q : Q) → Fintype (A q)] [inst : ∀ (q : Q), Nonempty (A q)], (∀ (T : (q : Q) → A q → I → Bool)
        (h : ∀ F : Finset I, F.Nonempty → Tendsto
          (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
        (ε : I → Bool),
    Tendsto
          (fun q => uniformMean (fun a => if T q a=ε then 1 else 0)) l
            (nhds ((Fintype.card (I → Bool) : ℝ)⁻¹))))

theorem boolean_law_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0956] : (∀ {I Q : Type} [inst : Fintype I] [inst : DecidableEq I] {l : Filter Q} {A : (a : Q) → Type}
    [inst : (q : Q) → Fintype (A q)] [inst : ∀ (q : Q), Nonempty (A q)], (∀ (T : (q : Q) → A q → I → Bool)
      (h : ∀ F : Finset I, F.Nonempty → Tendsto
        (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
      (ε : I → Bool),
  Tendsto
        (fun q => uniformMean (fun a => if T q a=ε then 1 else 0)) l
          (nhds ((Fintype.card (I → Bool) : ℝ)⁻¹)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0956.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0957 : Prop where
  proof : (∀ {I Q : Type} [inst : Fintype I] [inst : DecidableEq I] {l : Filter Q} {A : (a : Q) → Type}
      [inst : (q : Q) → Fintype (A q)] [inst : ∀ (q : Q), Nonempty (A q)], (∀ (T : (q : Q) → A q → I → Bool)
        (h : ∀ F : Finset I, F.Nonempty → Tendsto
          (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
        (g : (I → Bool) → ℝ),
    Tendsto
          (fun q => uniformMean (fun a => g (T q a))) l (nhds (uniformMean g))))

theorem boolean_test_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0957] : (∀ {I Q : Type} [inst : Fintype I] [inst : DecidableEq I] {l : Filter Q} {A : (a : Q) → Type}
    [inst : (q : Q) → Fintype (A q)] [inst : ∀ (q : Q), Nonempty (A q)], (∀ (T : (q : Q) → A q → I → Bool)
      (h : ∀ F : Finset I, F.Nonempty → Tendsto
        (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
      (g : (I → Bool) → ℝ),
  Tendsto
        (fun q => uniformMean (fun a => g (T q a))) l (nhds (uniformMean g)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0957.proof certificateEvidence
end

end Convergence
section
attribute [local instance] certificateFintype
class ProofCertificate_0958 : Prop where
  proof : ((∀ (D : ℕ) (hD : Even D) (hbig : 12≤D) (g : (Fin 33 → Bool) → ℝ),
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
          g (pairBool X))) primeInfinity (nhds (uniformMean g))))

theorem pairBool_test_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0958] : ((∀ (D : ℕ) (hD : Even D) (hbig : 12≤D) (g : (Fin 33 → Bool) → ℝ),
  Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
        g (pairBool X))) primeInfinity (nhds (uniformMean g)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0958.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Means
variable {K I W : Type} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
section
attribute [local instance] certificateFintype
class ProofCertificate_0959 : Prop where
  proof : (∀ {K I W : Type} [inst : Field K] [inst_1 : Fintype I] [inst_2 : DecidableEq I] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _] [inst : Fintype W], (∀ (v : Fin 3 → I) (hv : Function.Injective v) (f : W → W → ℝ),
    uniformMean (fun X : I → W => f (X (v 0)-X (v 1)) (X (v 0)-X (v 2)))=
          uniformMean (fun B : W => uniformMean (f B))))

theorem uniformMean_two_differences [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0959] : (∀ {K I W : Type} [inst : Field K] [inst_1 : Fintype I] [inst_2 : DecidableEq I] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _] [inst : Fintype W], (∀ (v : Fin 3 → I) (hv : Function.Injective v) (f : W → W → ℝ),
  uniformMean (fun X : I → W => f (X (v 0)-X (v 1)) (X (v 0)-X (v 2)))=
        uniformMean (fun B : W => uniformMean (f B)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0959.proof certificateEvidence
end

end Means
section Bounds
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def faceBound (r : ℕ) (ξ : Fin 3 → ℤ) : ℝ := 1+
  pairCoefficient (K := K) r (ξ 0) (ξ 1)+pairCoefficient (K := K) r (ξ 0) (ξ 2)+
  pairCoefficient (K := K) r (ξ 1) (ξ 2)+tripleCoefficient (K := K) r (ξ 0) (ξ 1) (ξ 2)

section
attribute [local instance] certificateFintype
class ProofCertificate_0960 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ),
    1≤faceBound (K := K) r ξ))

theorem faceBound_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0960] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 3 → ℤ),
  1≤faceBound (K := K) r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0960.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0961 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
        (X : Fin 3 → SymMatrix K (2*r)),
    0≤faceLocal r T ξ X))

theorem faceLocal_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0961] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
      (X : Fin 3 → SymMatrix K (2*r)),
  0≤faceLocal r T ξ X)) := @OAI.SidorenkoCounterexample.ProofCertificate_0961.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0962 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
        (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
        (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X),
    faceLocal r T ξ X≤faceBound (K := K) r ξ))

theorem faceLocal_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0962] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
      (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
      (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X),
  faceLocal r T ξ X≤faceBound (K := K) r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0962.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0963 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
        (B : SymMatrix K (2*r)),
    |pairPolynomial r ξ ζ B|≤2))

theorem pairPolynomial_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0963] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
      (B : SymMatrix K (2*r)),
  |pairPolynomial r ξ ζ B|≤2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0963.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0964 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
        (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)),
    |facePolynomial r T ξ X|≤8))

theorem facePolynomial_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0964] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
      (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)),
  |facePolynomial r T ξ X|≤8)) := @OAI.SidorenkoCounterexample.ProofCertificate_0964.proof certificateEvidence
end

end Bounds
section
attribute [local instance] certificateFintype
class ProofCertificate_0965 : Prop where
  proof : ((∀ (r : ℕ) (hr : 0<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1),
    Tendsto (fun q : OddPrime => faceBound (K := ZMod q.val) r ξ) primeInfinity (nhds 29)))

theorem faceBound_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0965] : ((∀ (r : ℕ) (hr : 0<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1),
  Tendsto (fun q : OddPrime => faceBound (K := ZMod q.val) r ξ) primeInfinity (nhds 29))) := @OAI.SidorenkoCounterexample.ProofCertificate_0965.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0966 : Prop where
  proof : ((∀ (r : ℕ) (hr : 1<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
        (v : Fin 3 → Fin 13) (hv : Function.Injective v),
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
          faceError r ξ (X ∘ v))) primeInfinity (nhds 0)))

theorem faceError_mean_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0966] : ((∀ (r : ℕ) (hr : 1<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
      (v : Fin 3 → Fin 13) (hv : Function.Injective v),
  Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
        faceError r ξ (X ∘ v))) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0966.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section ChartFace
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
abbrev CanonicalLag (D : ℕ) := Lagrangian (K := K) (V := Fin D → K)

instance canonicalDual_finite (D : ℕ) : Finite (Module.Dual K (Fin D → K)) :=
  Finite.of_injective (fun f : Module.Dual K (Fin D → K) => (f : (Fin D → K) → K)) DFunLike.coe_injective

noncomputable def canonicalKernel (D r : ℕ) (A Y : CanonicalLag (K := K) D) : ℝ :=
  if finrank K ↥(A.val⊓Y.val)=r then (canonicalStratumMass (K := K) D r)⁻¹ else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0967 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ (D r : ℕ) (A Y : CanonicalLag (K := K) D),
    0≤canonicalKernel D r A Y))

theorem canonicalKernel_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0967] : (∀ {K : Type} [inst : Field K], (∀ (D r : ℕ) (A Y : CanonicalLag (K := K) D),
  0≤canonicalKernel D r A Y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0967.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0968 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K] [inst : Fintype K]
      [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (A Y : SymMatrix K (2*r)) {C : ℝ}
        (hC : 0≤C) (hξ : canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r ξ≤C),
    rankKernel K (2*r) r ξ (A-Y) ≤ C*canonicalKernel (2*r) r (matrixLagrangian A) (matrixLagrangian Y)))

theorem rankKernel_chart_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0968] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K] [inst : Fintype K]
    [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (A Y : SymMatrix K (2*r)) {C : ℝ}
      (hC : 0≤C) (hξ : canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r ξ≤C),
  rankKernel K (2*r) r ξ (A-Y) ≤ C*canonicalKernel (2*r) r (matrixLagrangian A) (matrixLagrangian Y))) := @OAI.SidorenkoCounterexample.ProofCertificate_0968.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0969 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ (D r : ℕ) (L : Fin 3 → CanonicalLag (K := K) D)
        (T : Finset (Fin 3)) (Y : CanonicalLag (K := K) D),
    (∏ i∈T, canonicalKernel D r (L i) Y)=
          (if ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r then 1 else 0)*
            ((canonicalStratumMass (K := K) D r)⁻¹)^T.card))

theorem canonicalKernel_prod [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0969] : (∀ {K : Type} [inst : Field K], (∀ (D r : ℕ) (L : Fin 3 → CanonicalLag (K := K) D)
      (T : Finset (Fin 3)) (Y : CanonicalLag (K := K) D),
  (∏ i∈T, canonicalKernel D r (L i) Y)=
        (if ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r then 1 else 0)*
          ((canonicalStratumMass (K := K) D r)⁻¹)^T.card)) := @OAI.SidorenkoCounterexample.ProofCertificate_0969.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0970 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
      {K : Type} [inst : Field K], (∀ (D r : ℕ) [Fintype (CanonicalLag (K := K) D)]
        (L : Fin 3 → CanonicalLag (K := K) D) (T : Finset (Fin 3)),
    uniformMean (fun Y => ∏ i∈T, canonicalKernel D r (L i) Y)=
          activeFaceDensity (canonicalSymplectic (K := K) (V := Fin D → K)) r
            (verticalLagrangian (K := K) (V := Fin D → K)) L T))

theorem canonicalKernel_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0970] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
    {K : Type} [inst : Field K], (∀ (D r : ℕ) [Fintype (CanonicalLag (K := K) D)]
      (L : Fin 3 → CanonicalLag (K := K) D) (T : Finset (Fin 3)),
  uniformMean (fun Y => ∏ i∈T, canonicalKernel D r (L i) Y)=
        activeFaceDensity (canonicalSymplectic (K := K) (V := Fin D → K)) r
          (verticalLagrangian (K := K) (V := Fin D → K)) L T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0970.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0971 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K] [inst : Fintype K]
      [inst : DecidableEq K], (∀ (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
        (X : Fin 3 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
        (hξ : ∀ i∈T, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ i)≤C),
    faceLocal r T ξ X ≤ C^3 * lagrangianConstant (2*r) *
          activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
            (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (matrixLagrangian ∘ X) T))

theorem faceLocal_chart_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0971] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K] [inst : Fintype K]
    [inst : DecidableEq K], (∀ (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
      (X : Fin 3 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
      (hξ : ∀ i∈T, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ i)≤C),
  faceLocal r T ξ X ≤ C^3 * lagrangianConstant (2*r) *
        activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
          (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (matrixLagrangian ∘ X) T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0971.proof certificateEvidence
end

end ChartFace
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
def slotLeft : Fin 3 → Fin 3 := ![0,0,1]

def slotRight : Fin 3 → Fin 3 := ![1,2,2]

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0972 : Prop where
  proof : ((∀ j k,
        pairLeft (facePair j k)=faceVertex j (slotLeft k) ∧
        pairRight (facePair j k)=faceVertex j (slotRight k)))

theorem facePair_endpoints [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0972] : ((∀ j k,
      pairLeft (facePair j k)=faceVertex j (slotLeft k) ∧
      pairRight (facePair j k)=faceVertex j (slotRight k))) := @OAI.SidorenkoCounterexample.ProofCertificate_0972.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0973 : Prop where
  proof : ((∀ (e : Fin 33),
    pairVertices e∈modelPointPairs))

theorem modelPair_mem [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0973] : ((∀ (e : Fin 33),
  pairVertices e∈modelPointPairs)) := @OAI.SidorenkoCounterexample.ProofCertificate_0973.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0974 : Prop where
  proof : ((∀ j, (faces j).powersetCard 2 =
        Finset.univ.image (fun k => pairVertices (facePair j k))))

theorem face_pairs_image [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0974] : ((∀ j, (faces j).powersetCard 2 =
      Finset.univ.image (fun k => pairVertices (facePair j k)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0974.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0975 : Prop where
  proof : ((∀ (e : Finset (Fin 13)) (he : e∈modelPointPairs),
    ∃ k,pairVertices k=e))

theorem modelPair_all [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0975] : ((∀ (e : Finset (Fin 13)) (he : e∈modelPointPairs),
  ∃ k,pairVertices k=e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0975.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0973] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0373] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0975]
noncomputable def pairModelEquiv : Fin 33 ≃ ModelPair :=
  Equiv.ofBijective (fun e => ⟨pairVertices e,modelPair_mem e⟩) ⟨
    fun _ _ h => pairVertices_injective (congrArg Subtype.val h),
    fun e => by obtain ⟨k,hk⟩ := modelPair_all e.val e.property; exact ⟨k,Subtype.ext hk⟩⟩
end

def faceActive (B : Finset (Fin 13 × Fin 22)) (j : Fin 22) : Finset (Fin 3) :=
  Finset.univ.filter fun k => (faceVertex j k,j)∈B

noncomputable def faceSigns (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ)
    (j : Fin 22) (k : Fin 3) : ℤ := if (faceVertex j k,j)∈B then ξ (faceVertex j k,j) else 1

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0976 : Prop where
  proof : ((∀ {K : Type} [Field K] {r : ℕ} (X : Fin 13 → SymMatrix K (2*r))
        (hX : fullTransverse X) (j : Fin 22),
    faceTransverse r (X ∘ faceVertex j)))

theorem fullTransverse_face [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0976] : ((∀ {K : Type} [Field K] {r : ℕ} (X : Fin 13 → SymMatrix K (2*r))
      (hX : fullTransverse X) (j : Fin 22),
  faceTransverse r (X ∘ faceVertex j))) := @OAI.SidorenkoCounterexample.ProofCertificate_0976.proof certificateEvidence
end

noncomputable def boolFacePolynomial (c : ℝ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (j : Fin 22) (η : Fin 33 → Bool) : ℝ :=
  ∏ k : Fin 3, if slotLeft k∈T ∧ slotRight k∈T then
    1+c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ) else 1

section FaceGraph
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0977 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {D : ℕ} (X : Fin 13 → SymMatrix K D) (hX : fullTransverse X) (e : Fin 33),
    boolSign (pairBool X e)=pairSign X e))

theorem pairBool_eq_sign [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0977] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ {D : ℕ} (X : Fin 13 → SymMatrix K D) (hX : fullTransverse X) (e : Fin 33),
  boolSign (pairBool X e)=pairSign X e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0977.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0978 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
        (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) (j : Fin 22),
    facePolynomial r T ξ (X ∘ faceVertex j)=
          boolFacePolynomial (quadraticChar K ((-1 : K)^r)) T ξ j (pairBool X)))

theorem facePolynomial_bool [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0978] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
      (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) (j : Fin 22),
  facePolynomial r T ξ (X ∘ faceVertex j)=
        boolFacePolynomial (quadraticChar K ((-1 : K)^r)) T ξ j (pairBool X))) := @OAI.SidorenkoCounterexample.ProofCertificate_0978.proof certificateEvidence
end

end FaceGraph
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Global
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def configurationProduct (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) : ℝ :=
  ∏ j,faceLocal r (T j) (ξ j) (X ∘ faceVertex j)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0979 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)),
    0≤configurationProduct r T ξ X))

theorem configurationProduct_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0979] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)),
  0≤configurationProduct r T ξ X)) := @OAI.SidorenkoCounterexample.ProofCertificate_0979.proof certificateEvidence
end

noncomputable def matrixSingularTail (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) =>
    if fullTransverse X then 0 else configurationProduct r T ξ X

def canonicalSingular (D : ℕ) (L : Fin 13 → CanonicalLag (K := K) D) : Prop :=
  ∃ e, finrank K ↥((pairVertices e).inf fun i => (L i).val)≠0

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0980 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K], (∀ (r : ℕ) (X : Fin 13 → SymMatrix K (2*r)),
    canonicalSingular (2*r) (matrixLagrangian ∘ X) ↔ ¬fullTransverse X))

theorem canonicalSingular_chart [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0980] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K], (∀ (r : ℕ) (X : Fin 13 → SymMatrix K (2*r)),
  canonicalSingular (2*r) (matrixLagrangian ∘ X) ↔ ¬fullTransverse X)) := @OAI.SidorenkoCounterexample.ProofCertificate_0980.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
noncomputable def canonicalConfiguration (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (L : Fin 13 → CanonicalLag (K := K) (2*r)) : ℝ :=
  ∏ j,activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
    (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (L ∘ faceVertex j) (T j)
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0981 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
      {K : Type} [inst : Field K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (L : Fin 13 → CanonicalLag (K := K) (2*r)),
    0≤canonicalConfiguration r T L))

theorem canonicalConfiguration_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0981] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
    {K : Type} [inst : Field K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (L : Fin 13 → CanonicalLag (K := K) (2*r)),
  0≤canonicalConfiguration r T L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0981.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0982 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K] [inst : Fintype K]
      [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
        (hξ : ∀ j i, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ j i)≤C),
    configurationProduct r T ξ X ≤ (C^3*lagrangianConstant (2*r))^22 *
          canonicalConfiguration r T (matrixLagrangian ∘ X)))

theorem configuration_chart_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0982] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0198] {K : Type} [inst : Field K] [inst : Fintype K]
    [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
      (hξ : ∀ j i, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ j i)≤C),
  configurationProduct r T ξ X ≤ (C^3*lagrangianConstant (2*r))^22 *
        canonicalConfiguration r T (matrixLagrangian ∘ X))) := @OAI.SidorenkoCounterexample.ProofCertificate_0982.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0983 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
      {K : Type} [inst : Field K] [inst : Fintype K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        [Fintype (CanonicalLag (K := K) (2*r))],
    actualSingularTail (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
          (verticalLagrangian (K := K) (V := Fin (2*r) → K)) T =
          uniformMean (fun L : Fin 13 → CanonicalLag (K := K) (2*r) =>
            if canonicalSingular (2*r) L then canonicalConfiguration r T L else 0)))

theorem actualSingularTail_uniform [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0983] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
    {K : Type} [inst : Field K] [inst : Fintype K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      [Fintype (CanonicalLag (K := K) (2*r))],
  actualSingularTail (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K)) T =
        uniformMean (fun L : Fin 13 → CanonicalLag (K := K) (2*r) =>
          if canonicalSingular (2*r) L then canonicalConfiguration r T L else 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0983.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0984 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
      {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) {C : ℝ} (hC : 1≤C)
        (hξ : ∀ j i, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ j i)≤C),
    matrixSingularTail (K := K) r T ξ ≤
          ((C^3*lagrangianConstant (2*r))^22*lagrangianConstant (2*r)^13)*
            actualSingularTail (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
              (verticalLagrangian (K := K) (V := Fin (2*r) → K)) T))

theorem matrixSingularTail_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0984] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
    {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) {C : ℝ} (hC : 1≤C)
      (hξ : ∀ j i, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ j i)≤C),
  matrixSingularTail (K := K) r T ξ ≤
        ((C^3*lagrangianConstant (2*r))^22*lagrangianConstant (2*r)^13)*
          actualSingularTail (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
            (verticalLagrangian (K := K) (V := Fin (2*r) → K)) T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0984.proof certificateEvidence
end

end Global
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0985 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0034]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0014], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (hlarge : singularTailThreshold≤2*r),
    Tendsto
          (fun q : OddPrime => actualSingularTail (canonicalSymplectic (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)) r
            (verticalLagrangian (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)) T)
          primeInfinity (nhds 0)))

theorem canonicalTail_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0985] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0034]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0014], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (hlarge : singularTailThreshold≤2*r),
  Tendsto
        (fun q : OddPrime => actualSingularTail (canonicalSymplectic (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)) r
          (verticalLagrangian (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)) T)
        primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0985.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0986 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i, ξ j i=1 ∨ ξ j i= -1)
        (hlarge : singularTailThreshold≤2*r),
    Tendsto
          (fun q : OddPrime => matrixSingularTail (K := ZMod q.val) r T ξ) primeInfinity (nhds 0)))

theorem matrixSingularTail_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0986] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i, ξ j i=1 ∨ ξ j i= -1)
      (hlarge : singularTailThreshold≤2*r),
  Tendsto
        (fun q : OddPrime => matrixSingularTail (K := ZMod q.val) r T ξ) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0986.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section GlobalProduct
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def configurationPolynomial (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) : ℝ :=
  ∏ j,facePolynomial r (T j) (ξ j) (X ∘ faceVertex j)

noncomputable def globalBound (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  8+∑ j,faceBound (K := K) r (ξ j)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0987 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ),
    8≤globalBound (K := K) r ξ))

theorem globalBound_eight [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0987] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ),
  8≤globalBound (K := K) r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0987.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0988 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) (j : Fin 22),
    faceBound (K := K) r (ξ j)≤globalBound (K := K) r ξ))

theorem faceBound_le_global [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0988] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) (j : Fin 22),
  faceBound (K := K) r (ξ j)≤globalBound (K := K) r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0988.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0989 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
        (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
        (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X),
    |configurationProduct r T ξ X-configurationPolynomial r T ξ X|≤
          globalBound (K := K) r ξ^22*∑ j,faceError r (ξ j) (X ∘ faceVertex j)))

theorem configuration_difference_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0989] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
      (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
      (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X),
  |configurationProduct r T ξ X-configurationPolynomial r T ξ X|≤
        globalBound (K := K) r ξ^22*∑ j,faceError r (ξ j) (X ∘ faceVertex j))) := @OAI.SidorenkoCounterexample.ProofCertificate_0989.proof certificateEvidence
end

noncomputable def transverseDifference (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) =>
    if fullTransverse X then configurationProduct r T ξ X-configurationPolynomial r T ξ X else 0

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0990 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
        (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
        (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
    |transverseDifference (K := K) r T ξ|≤globalBound (K := K) r ξ^22*
          ∑ j,uniformMean (fun X : Fin 13 → SymMatrix K (2*r) => faceError r (ξ j) (X ∘ faceVertex j))))

theorem transverseDifference_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0990] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
      (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
      (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
  |transverseDifference (K := K) r T ξ|≤globalBound (K := K) r ξ^22*
        ∑ j,uniformMean (fun X : Fin 13 → SymMatrix K (2*r) => faceError r (ξ j) (X ∘ faceVertex j)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0990.proof certificateEvidence
end

end GlobalProduct
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0991 : Prop where
  proof : ((∀ (r : ℕ) (hr : 0<r) (ξ : Fin 22 → Fin 3 → ℤ)
        (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
    Tendsto
        (fun q : OddPrime => globalBound (K := ZMod q.val) r ξ) primeInfinity (nhds 646)))

theorem globalBound_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0991] : ((∀ (r : ℕ) (hr : 0<r) (ξ : Fin 22 → Fin 3 → ℤ)
      (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
  Tendsto
      (fun q : OddPrime => globalBound (K := ZMod q.val) r ξ) primeInfinity (nhds 646))) := @OAI.SidorenkoCounterexample.ProofCertificate_0991.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0992 : Prop where
  proof : ((∀ (r : ℕ) (hr : 1<r)
        (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
        (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
    Tendsto
        (fun q : OddPrime => transverseDifference (K := ZMod q.val) r T ξ) primeInfinity (nhds 0)))

theorem transverseDifference_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0992] : ((∀ (r : ℕ) (hr : 1<r)
      (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
      (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
  Tendsto
      (fun q : OddPrime => transverseDifference (K := ZMod q.val) r T ξ) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0992.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
noncomputable def boolConfiguration (c : ℝ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (η : Fin 33 → Bool) : ℝ :=
  ∏ j,boolFacePolynomial c (T j) (ξ j) j η

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0993 : Prop where
  proof : ((∀ (c : ℝ) (hc : |c|≤1) (T : Finset (Fin 3))
        (ξ : Fin 3 → ℤ) (hξ : ∀ i,ξ i=1 ∨ ξ i= -1) (j : Fin 22) (η : Fin 33 → Bool),
    |boolFacePolynomial c T ξ j η|≤8))

theorem boolFacePolynomial_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0993] : ((∀ (c : ℝ) (hc : |c|≤1) (T : Finset (Fin 3))
      (ξ : Fin 3 → ℤ) (hξ : ∀ i,ξ i=1 ∨ ξ i= -1) (j : Fin 22) (η : Fin 33 → Bool),
  |boolFacePolynomial c T ξ j η|≤8)) := @OAI.SidorenkoCounterexample.ProofCertificate_0993.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0994 : Prop where
  proof : ((∀ (c : ℝ) (hc : |c|≤1) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (η : Fin 33 → Bool),
    |boolConfiguration c T ξ η|≤8^22))

theorem boolConfiguration_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0994] : ((∀ (c : ℝ) (hc : |c|≤1) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (η : Fin 33 → Bool),
  |boolConfiguration c T ξ η|≤8^22)) := @OAI.SidorenkoCounterexample.ProofCertificate_0994.proof certificateEvidence
end

section GlobalBool
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0995 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X),
    configurationPolynomial r T ξ X=
          boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)))

theorem configurationPolynomial_bool [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0995] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X),
  configurationPolynomial r T ξ X=
        boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X))) := @OAI.SidorenkoCounterexample.ProofCertificate_0995.proof certificateEvidence
end

noncomputable def boolSingular (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) => if fullTransverse X then 0 else
    boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0996 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
    |boolSingular (K := K) r T ξ|≤8^22*(33*((2*r : ℕ):ℝ)/Fintype.card K)))

theorem boolSingular_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0996] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
  |boolSingular (K := K) r T ξ|≤8^22*(33*((2*r : ℕ):ℝ)/Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0996.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0997 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ),
    uniformMean (configurationProduct (K := K) r T ξ)-uniformMean
          (fun X : Fin 13 → SymMatrix K (2*r) => boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)) =
          transverseDifference (K := K) r T ξ+matrixSingularTail (K := K) r T ξ-boolSingular (K := K) r T ξ))

theorem configuration_mean_identity [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0997] : (∀ {K : Type} [inst : Field K] [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ),
  uniformMean (configurationProduct (K := K) r T ξ)-uniformMean
        (fun X : Fin 13 → SymMatrix K (2*r) => boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)) =
        transverseDifference (K := K) r T ξ+matrixSingularTail (K := K) r T ξ-boolSingular (K := K) r T ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0997.proof certificateEvidence
end

end GlobalBool
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0998 : Prop where
  proof : ((∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
    Tendsto
        (fun q : OddPrime => boolSingular (K := ZMod q.val) r T ξ) primeInfinity (nhds 0)))

theorem boolSingular_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0998] : ((∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1),
  Tendsto
      (fun q : OddPrime => boolSingular (K := ZMod q.val) r T ξ) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0998.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_0999 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1)
        (hlarge : singularTailThreshold≤2*r),
    Tendsto
        (fun q : OddPrime => uniformMean (configurationProduct (K := ZMod q.val) r T ξ)-uniformMean
          (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
            boolConfiguration (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) T ξ (pairBool X))) primeInfinity (nhds 0)))

theorem configuration_bool_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0999] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1)
      (hlarge : singularTailThreshold≤2*r),
  Tendsto
      (fun q : OddPrime => uniformMean (configurationProduct (K := ZMod q.val) r T ξ)-uniformMean
        (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
          boolConfiguration (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) T ξ (pairBool X))) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0999.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
structure FiniteLaw (A : Type) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a,0≤weight a
  total : ∑ a,weight a=1

namespace FiniteLaw
variable {A B C I : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]
noncomputable def mean (p : FiniteLaw A) (f : A → ℝ) : ℝ := ∑ a,p.weight a*f a

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1000 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a=g a),
    p.mean f=p.mean g))

theorem mean_congr [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1000] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a=g a),
  p.mean f=p.mean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_1000.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1001 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (c : ℝ),
    p.mean (fun _ => c)=c))

@[simp]
theorem mean_const [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1001] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (c : ℝ),
  p.mean (fun _ => c)=c)) := @OAI.SidorenkoCounterexample.ProofCertificate_1001.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1002 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f g : A → ℝ),
    p.mean (fun a => f a+g a)=p.mean f+p.mean g))

theorem mean_add [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1002] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f g : A → ℝ),
  p.mean (fun a => f a+g a)=p.mean f+p.mean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_1002.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1003 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f g : A → ℝ),
    p.mean (fun a => f a-g a)=p.mean f-p.mean g))

theorem mean_sub [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1003] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f g : A → ℝ),
  p.mean (fun a => f a-g a)=p.mean f-p.mean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_1003.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1004 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (c : ℝ) (f : A → ℝ),
    p.mean (fun a => c*f a)=c*p.mean f))

theorem mean_mul [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1004] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (c : ℝ) (f : A → ℝ),
  p.mean (fun a => c*f a)=c*p.mean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1004.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1005 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f : A → ℝ) (c : ℝ),
    p.mean (fun a => f a*c)=p.mean f*c))

theorem mean_mul_right [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1005] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f : A → ℝ) (c : ℝ),
  p.mean (fun a => f a*c)=p.mean f*c)) := @OAI.SidorenkoCounterexample.ProofCertificate_1005.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1006 : Prop where
  proof : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I], (∀ (p : FiniteLaw A) (f : I → A → ℝ),
    p.mean (fun a => ∑ i,f i a)=∑ i,p.mean (f i)))

theorem mean_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1006] : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I], (∀ (p : FiniteLaw A) (f : I → A → ℝ),
  p.mean (fun a => ∑ i,f i a)=∑ i,p.mean (f i))) := @OAI.SidorenkoCounterexample.ProofCertificate_1006.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1007 : Prop where
  proof : (∀ {A I : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (s : Finset I) (f : I → A → ℝ),
    p.mean (fun a => ∑ i∈s,f i a)=∑ i∈s,p.mean (f i)))

theorem mean_finset_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1007] : (∀ {A I : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (s : Finset I) (f : I → A → ℝ),
  p.mean (fun a => ∑ i∈s,f i a)=∑ i∈s,p.mean (f i))) := @OAI.SidorenkoCounterexample.ProofCertificate_1007.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1008 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f : A → ℝ} (hf : ∀ a,0≤f a),
    0≤p.mean f))

theorem mean_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1008] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f : A → ℝ} (hf : ∀ a,0≤f a),
  0≤p.mean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1008.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1009 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a≤g a),
    p.mean f≤p.mean g))

theorem mean_mono [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1009] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a≤g a),
  p.mean f≤p.mean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_1009.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1010 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f : A → ℝ} {c : ℝ} (h : ∀ a,f a≤c),
    p.mean f≤c))

theorem mean_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1010] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f : A → ℝ} {c : ℝ} (h : ∀ a,f a≤c),
  p.mean f≤c)) := @OAI.SidorenkoCounterexample.ProofCertificate_1010.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1011 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f : A → ℝ),
    |p.mean f|≤p.mean (fun a => |f a|)))

theorem abs_mean_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1011] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f : A → ℝ),
  |p.mean f|≤p.mean (fun a => |f a|))) := @OAI.SidorenkoCounterexample.ProofCertificate_1011.proof certificateEvidence
end

noncomputable def dirac (a : A) : FiniteLaw A where
  weight b := if b=a then 1 else 0
  nonneg b := by split <;> norm_num
  total := by simp

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1012 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (a : A) (f : A → ℝ),
    (dirac a).mean f=f a))

@[simp]
theorem mean_dirac [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1012] : (∀ {A : Type} [inst : Fintype A], (∀ (a : A) (f : A → ℝ),
  (dirac a).mean f=f a)) := @OAI.SidorenkoCounterexample.ProofCertificate_1012.proof certificateEvidence
end

noncomputable def uniform [Nonempty A] : FiniteLaw A where
  weight _ := (Fintype.card A : ℝ)⁻¹
  nonneg _ := by positivity
  total := by simp [nsmul_eq_mul,ne_of_gt (Fintype.card_pos (α := A))]

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1013 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ [Nonempty A] (f : A → ℝ),
    uniform.mean f=uniformMean f))

theorem mean_uniform [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1013] : (∀ {A : Type} [inst : Fintype A], (∀ [Nonempty A] (f : A → ℝ),
  uniform.mean f=uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1013.proof certificateEvidence
end

noncomputable def prod (p : FiniteLaw A) (q : FiniteLaw B) : FiniteLaw (A × B) where
  weight x := p.weight x.1*q.weight x.2
  nonneg _ := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp_rw [←Finset.mul_sum,q.total,mul_one]; exact p.total

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1014 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (q : FiniteLaw B) (f : A × B → ℝ),
    (p.prod q).mean f=p.mean (fun a => q.mean (fun b => f (a,b)))))

@[simp]
theorem mean_prod [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1014] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (q : FiniteLaw B) (f : A × B → ℝ),
  (p.prod q).mean f=p.mean (fun a => q.mean (fun b => f (a,b))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1014.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1015 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (q : FiniteLaw B) (f : A → B → ℝ),
    p.mean (fun a => q.mean (f a))=q.mean (fun b => p.mean (fun a => f a b))))

theorem mean_swap [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1015] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (q : FiniteLaw B) (f : A → B → ℝ),
  p.mean (fun a => q.mean (f a))=q.mean (fun b => p.mean (fun a => f a b)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1015.proof certificateEvidence
end

noncomputable def independent (p : I → FiniteLaw A) : FiniteLaw (I → A) where
  weight x := ∏ i,(p i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (p i).nonneg (x i))
  total := by rw [←Fintype.prod_sum]; simp only [(p _).total,Finset.prod_const_one]

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1016 : Prop where
  proof : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I] [inst : DecidableEq I], (∀ (p : I → FiniteLaw A) (f : I → A → ℝ),
    (independent p).mean (fun x => ∏ i,f i (x i))=∏ i,(p i).mean (f i)))

theorem independent_mean_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1016] : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I] [inst : DecidableEq I], (∀ (p : I → FiniteLaw A) (f : I → A → ℝ),
  (independent p).mean (fun x => ∏ i,f i (x i))=∏ i,(p i).mean (f i))) := @OAI.SidorenkoCounterexample.ProofCertificate_1016.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1017 : Prop where
  proof : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I] [inst : DecidableEq I], (∀ (p : I → FiniteLaw A) (f : I → A → ℝ),
    (∏ i,(p i).mean (f i))=∑ x : I → A,∏ i,(p i).weight (x i)*f i (x i)))

theorem mean_map_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1017] : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I] [inst : DecidableEq I], (∀ (p : I → FiniteLaw A) (f : I → A → ℝ),
  (∏ i,(p i).mean (f i))=∑ x : I → A,∏ i,(p i).weight (x i)*f i (x i))) := @OAI.SidorenkoCounterexample.ProofCertificate_1017.proof certificateEvidence
end

noncomputable def mixture (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : FiniteLaw A where
  weight a := t*p.weight a+(1-t)*q.weight a
  nonneg a := add_nonneg (mul_nonneg ht (p.nonneg a)) (mul_nonneg (by linarith) (q.nonneg a))
  total := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,p.total,q.total]; ring

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1018 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (f : A → ℝ),
    (mixture p q t ht ht1).mean f=t*p.mean f+(1-t)*q.mean f))

theorem mean_mixture [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1018] : (∀ {A : Type} [inst : Fintype A], (∀ (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (f : A → ℝ),
  (mixture p q t ht ht1).mean f=t*p.mean f+(1-t)*q.mean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1018.proof certificateEvidence
end

noncomputable def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B where
  weight b := ∑ a,if f a=b then p.weight a else 0
  nonneg b := Finset.sum_nonneg (fun a _ => by split <;> simp only [p.nonneg,le_refl])
  total := by rw [Finset.sum_comm]; simpa using p.total

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1019 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (f : A → B) (g : B → ℝ),
    (p.map f).mean g=p.mean (g ∘ f)))

theorem mean_map [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1019] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (f : A → B) (g : B → ℝ),
  (p.map f).mean g=p.mean (g ∘ f))) := @OAI.SidorenkoCounterexample.ProofCertificate_1019.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1020 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ {Q : Type} {l : Filter Q} (p : FiniteLaw A) (f : Q → A → ℝ)
        (g : A → ℝ) (h : ∀ a,Filter.Tendsto (fun q => f q a) l (nhds (g a))),
    Filter.Tendsto (fun q => p.mean (f q)) l (nhds (p.mean g))))

theorem mean_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1020] : (∀ {A : Type} [inst : Fintype A], (∀ {Q : Type} {l : Filter Q} (p : FiniteLaw A) (f : Q → A → ℝ)
      (g : A → ℝ) (h : ∀ a,Filter.Tendsto (fun q => f q a) l (nhds (g a))),
  Filter.Tendsto (fun q => p.mean (f q)) l (nhds (p.mean g)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1020.proof certificateEvidence
end

end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section BooleanMoments
variable {K : Type} [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1021 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s : Finset K) (η : K → Bool),
    boolMonomial s η=∏ k,if k∈s then boolSign (η k) else 1))

theorem boolMonomial_asprod [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1021] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s : Finset K) (η : K → Bool),
  boolMonomial s η=∏ k,if k∈s then boolSign (η k) else 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1021.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1022 : Prop where
  proof : (∀ {K : Type}, (∀ (s : Finset K) (η : K → Bool),
    |boolMonomial s η|=1))

theorem boolMonomial_abs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1022] : (∀ {K : Type}, (∀ (s : Finset K) (η : K → Bool),
  |boolMonomial s η|=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1022.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1023 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s t : Finset K) (η : K → Bool),
    boolMonomial s η*boolMonomial t η=boolMonomial (s ∆ t) η))

theorem boolMonomial_mul [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1023] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s t : Finset K) (η : K → Bool),
  boolMonomial s η*boolMonomial t η=boolMonomial (s ∆ t) η)) := @OAI.SidorenkoCounterexample.ProofCertificate_1023.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1024 : Prop where
  proof : ((uniformMean boolSign=0))

theorem boolSign_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1024] : ((uniformMean boolSign=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1024.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1025 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s : Finset K),
    uniformMean (boolMonomial s)=if s=∅ then 1 else 0))

theorem boolMonomial_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1025] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s : Finset K),
  uniformMean (boolMonomial s)=if s=∅ then 1 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1025.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1026 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s t : Finset K),
    uniformMean (fun η => boolMonomial s η*boolMonomial t η)=if s=t then 1 else 0))

theorem boolMonomial_orthog [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1026] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s t : Finset K),
  uniformMean (fun η => boolMonomial s η*boolMonomial t η)=if s=t then 1 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1026.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025]
noncomputable def tiltLaw (s : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (K → Bool) where
  weight η := (Fintype.card (K → Bool):ℝ)⁻¹*(1+a*boolMonomial s η)
  nonneg η := by
    apply mul_nonneg (by positivity)
    have hab : |a*boolMonomial s η|≤1 := by simpa only [abs_mul,boolMonomial_abs,mul_one] using ha
    have := neg_abs_le (a*boolMonomial s η); linarith
  total := by
    simp only [←div_eq_inv_mul]
    rw [←Finset.sum_div]
    change uniformMean (fun η : K → Bool => 1+a*boolMonomial s η)=1
    rw [uniformMean_add,uniformMean_const,uniformMean_mul,boolMonomial_mean,if_neg hs]; ring
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1027 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) (f : (K → Bool) → ℝ),
    (tiltLaw s hs a ha).mean f=uniformMean (fun η => (1+a*boolMonomial s η)*f η)))

theorem tiltLaw_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1027] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) (f : (K → Bool) → ℝ),
  (tiltLaw s hs a ha).mean f=uniformMean (fun η => (1+a*boolMonomial s η)*f η))) := @OAI.SidorenkoCounterexample.ProofCertificate_1027.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1028 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s t : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1),
    (tiltLaw s hs a ha).mean (boolMonomial t)=(if t=∅ then 1 else 0)+a*(if t=s then 1 else 0)))

theorem tiltLaw_monomial [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1028] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (s t : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1),
  (tiltLaw s hs a ha).mean (boolMonomial t)=(if t=∅ then 1 else 0)+a*(if t=s then 1 else 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_1028.proof certificateEvidence
end

abbrev Activation (K : Type) := Finset K × (K → Bool)

noncomputable def activationPhi (α : Finset K) (z : Activation K) : ℝ :=
  if α⊆z.1 then boolMonomial α z.2 else 0

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1029 : Prop where
  proof : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : Activation K),
    activationPhi ∅ z=1))

@[simp]
theorem activationPhi_empty [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1029] : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : Activation K),
  activationPhi ∅ z=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1029.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1030 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α β : Finset K) (z : Activation K),
    activationPhi α z*activationPhi β z=
          if α∪β⊆z.1 then boolMonomial (α ∆ β) z.2 else 0))

theorem activationPhi_mul [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1030] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α β : Finset K) (z : Activation K),
  activationPhi α z*activationPhi β z=
        if α∪β⊆z.1 then boolMonomial (α ∆ β) z.2 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1030.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1031 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α β : Finset K) (h : Disjoint α β) (z : Activation K),
    activationPhi α z*activationPhi β z=activationPhi (α∪β) z))

theorem activationPhi_disjoint [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1031] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α β : Finset K) (h : Disjoint α β) (z : Activation K),
  activationPhi α z*activationPhi β z=activationPhi (α∪β) z)) := @OAI.SidorenkoCounterexample.ProofCertificate_1031.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025]
noncomputable def branchLaw (S Γ : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (Activation K) :=
  (FiniteLaw.dirac S).prod (tiltLaw Γ hΓ a ha)
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1032 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (S Γ α : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1),
    (branchLaw S Γ hΓ a ha).mean (activationPhi α)=
          if α⊆S then (if α=∅ then 1 else 0)+a*(if α=Γ then 1 else 0) else 0))

theorem branchLaw_phi [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1032] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (S Γ α : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1),
  (branchLaw S Γ hΓ a ha).mean (activationPhi α)=
        if α⊆S then (if α=∅ then 1 else 0)+a*(if α=Γ then 1 else 0) else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1032.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1033 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (S Γ α β : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1),
    (branchLaw S Γ hΓ a ha).mean (fun z => activationPhi α z*activationPhi β z)=
          if α∪β⊆S then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0))

theorem branchLaw_second [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1033] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (S Γ α β : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1),
  (branchLaw S Γ hΓ a ha).mean (fun z => activationPhi α z*activationPhi β z)=
        if α∪β⊆S then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1033.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025]
noncomputable def baseActivation (M Γ : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (Activation K) :=
  FiniteLaw.mixture (branchLaw M Γ hΓ a ha) (branchLaw Γ Γ hΓ (-a) (by simpa using ha))
    (1/2) (by norm_num) (by norm_num)
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1034 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (M Γ α : Finset K) (hΓ : Γ≠∅) (hΓM : Γ⊆M)
        (a : ℝ) (ha : |a|≤1) (hα : α≠∅),
    (baseActivation M Γ hΓ a ha).mean (activationPhi α)=0))

theorem baseActivation_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1034] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (M Γ α : Finset K) (hΓ : Γ≠∅) (hΓM : Γ⊆M)
      (a : ℝ) (ha : |a|≤1) (hα : α≠∅),
  (baseActivation M Γ hΓ a ha).mean (activationPhi α)=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1034.proof certificateEvidence
end

noncomputable def activationMoment (p : FiniteLaw (Activation K)) (α β : Finset K) : ℝ :=
  p.mean (fun z => activationPhi α z*activationPhi β z)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1035 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : FiniteLaw (Activation K)),
    activationMoment p ∅ ∅=1))

@[simp]
theorem activationMoment_empty [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1035] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : FiniteLaw (Activation K)),
  activationMoment p ∅ ∅=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1035.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1036 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : FiniteLaw (Activation K))
        (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0) (α β : Finset K)
        (hd : Disjoint α β) (hn : α∪β≠∅),
    activationMoment p α β=0))

theorem activationMoment_disjoint [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1036] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : FiniteLaw (Activation K))
      (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0) (α β : Finset K)
      (hd : Disjoint α β) (hn : α∪β≠∅),
  activationMoment p α β=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1036.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1037 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (M Γ α β : Finset K) (hΓ : Γ≠∅)
        (a : ℝ) (ha : |a|≤1),
    activationMoment (baseActivation M Γ hΓ a ha) α β=
        (1/2)*(if α∪β⊆M then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0)+
        (1/2)*(if α∪β⊆Γ then (if α=β then 1 else 0)-a*(if α ∆ β=Γ then 1 else 0) else 0)))

theorem baseActivation_moment [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1037] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (M Γ α β : Finset K) (hΓ : Γ≠∅)
      (a : ℝ) (ha : |a|≤1),
  activationMoment (baseActivation M Γ hΓ a ha) α β=
      (1/2)*(if α∪β⊆M then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0)+
      (1/2)*(if α∪β⊆Γ then (if α=β then 1 else 0)-a*(if α ∆ β=Γ then 1 else 0) else 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_1037.proof certificateEvidence
end

end BooleanMoments
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
def cornerPairL (k : ActCorner) : Fin 33 := facePair k.1 (slotLeft k.2)

def cornerPairR (k : ActCorner) : Fin 33 := facePair k.1 (slotRight k.2)

def pairCorners (e : Fin 33) : Finset ActCorner :=
  Finset.univ.filter fun k => cornerPairL k=e ∨ cornerPairR k=e

def cornerMax (k : ActCorner) : Finset ActCorner := pairCorners (cornerPairL k) ∪ pairCorners (cornerPairR k)

def cornerGamma (k : ActCorner) : Finset ActCorner := pairCorners (cornerPairL k) ∆ pairCorners (cornerPairR k)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1038 : Prop where
  proof : ((∀ (k : ActCorner) (e : Fin 33),
    k∈pairCorners e ↔ cornerPairL k=e ∨ cornerPairR k=e))

theorem pairCorners_mem [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1038] : ((∀ (k : ActCorner) (e : Fin 33),
  k∈pairCorners e ↔ cornerPairL k=e ∨ cornerPairR k=e)) := @OAI.SidorenkoCounterexample.ProofCertificate_1038.proof certificateEvidence
end

def pairCornerTable : Fin 33 → Finset ActCorner := ![{(2,0), (2,1), (3,0), (3,1)},
  {(0,0), (0,2), (2,0), (2,2)},
  {(2,1), (2,2), (8,0), (8,1)},
  {(1,0), (1,2), (3,0), (3,2)},
  {(3,1), (3,2), (9,0), (9,2)},
  {(0,0), (0,1), (1,0), (1,1)},
  {(0,1), (0,2), (4,0), (4,1)},
  {(8,0), (8,2), (9,0), (9,1)},
  {(8,1), (8,2), (10,0), (10,1)},
  {(1,1), (1,2), (7,0), (7,1)},
  {(9,1), (9,2), (12,0), (12,2)},
  {(4,0), (4,2), (5,0), (5,2)},
  {(4,1), (4,2), (11,0), (11,1)},
  {(10,0), (10,2), (11,0), (11,2)},
  {(10,1), (10,2), (13,0), (13,2)},
  {(6,0), (6,2), (7,0), (7,2)},
  {(7,1), (7,2), (21,1), (21,2)},
  {(12,0), (12,1), (13,0), (13,1)},
  {(12,1), (12,2), (21,0), (21,1)},
  {(5,0), (5,1), (6,0), (6,1)},
  {(5,1), (5,2), (16,1), (16,2)},
  {(11,1), (11,2), (17,1), (17,2)},
  {(13,1), (13,2), (19,1), (19,2)},
  {(6,1), (6,2), (18,1), (18,2)},
  {(20,1), (20,2), (21,0), (21,2)},
  {(14,0), (14,2), (16,0), (16,1)},
  {(16,0), (16,2), (17,0), (17,1)},
  {(15,0), (15,2), (17,0), (17,2)},
  {(19,0), (19,1), (20,0), (20,1)},
  {(15,1), (15,2), (19,0), (19,2)},
  {(14,1), (14,2), (18,0), (18,1)},
  {(18,0), (18,2), (20,0), (20,2)},
  {(14,0), (14,1), (15,0), (15,1)}]

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1039 : Prop where
  proof : ((pairCorners 0=pairCornerTable 0))

theorem pairCorners_table_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1039] : ((pairCorners 0=pairCornerTable 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1039.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1040 : Prop where
  proof : ((pairCorners 1=pairCornerTable 1))

theorem pairCorners_table_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1040] : ((pairCorners 1=pairCornerTable 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1040.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1041 : Prop where
  proof : ((pairCorners 2=pairCornerTable 2))

theorem pairCorners_table_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1041] : ((pairCorners 2=pairCornerTable 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_1041.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1042 : Prop where
  proof : ((pairCorners 3=pairCornerTable 3))

theorem pairCorners_table_3 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1042] : ((pairCorners 3=pairCornerTable 3)) := @OAI.SidorenkoCounterexample.ProofCertificate_1042.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1043 : Prop where
  proof : ((pairCorners 4=pairCornerTable 4))

theorem pairCorners_table_4 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1043] : ((pairCorners 4=pairCornerTable 4)) := @OAI.SidorenkoCounterexample.ProofCertificate_1043.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1044 : Prop where
  proof : ((pairCorners 5=pairCornerTable 5))

theorem pairCorners_table_5 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1044] : ((pairCorners 5=pairCornerTable 5)) := @OAI.SidorenkoCounterexample.ProofCertificate_1044.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1045 : Prop where
  proof : ((pairCorners 6=pairCornerTable 6))

theorem pairCorners_table_6 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1045] : ((pairCorners 6=pairCornerTable 6)) := @OAI.SidorenkoCounterexample.ProofCertificate_1045.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1046 : Prop where
  proof : ((pairCorners 7=pairCornerTable 7))

theorem pairCorners_table_7 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1046] : ((pairCorners 7=pairCornerTable 7)) := @OAI.SidorenkoCounterexample.ProofCertificate_1046.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1047 : Prop where
  proof : ((pairCorners 8=pairCornerTable 8))

theorem pairCorners_table_8 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1047] : ((pairCorners 8=pairCornerTable 8)) := @OAI.SidorenkoCounterexample.ProofCertificate_1047.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1048 : Prop where
  proof : ((pairCorners 9=pairCornerTable 9))

theorem pairCorners_table_9 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1048] : ((pairCorners 9=pairCornerTable 9)) := @OAI.SidorenkoCounterexample.ProofCertificate_1048.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1049 : Prop where
  proof : ((pairCorners 10=pairCornerTable 10))

theorem pairCorners_table_10 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1049] : ((pairCorners 10=pairCornerTable 10)) := @OAI.SidorenkoCounterexample.ProofCertificate_1049.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1050 : Prop where
  proof : ((pairCorners 11=pairCornerTable 11))

theorem pairCorners_table_11 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1050] : ((pairCorners 11=pairCornerTable 11)) := @OAI.SidorenkoCounterexample.ProofCertificate_1050.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1051 : Prop where
  proof : ((pairCorners 12=pairCornerTable 12))

theorem pairCorners_table_12 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1051] : ((pairCorners 12=pairCornerTable 12)) := @OAI.SidorenkoCounterexample.ProofCertificate_1051.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1052 : Prop where
  proof : ((pairCorners 13=pairCornerTable 13))

theorem pairCorners_table_13 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1052] : ((pairCorners 13=pairCornerTable 13)) := @OAI.SidorenkoCounterexample.ProofCertificate_1052.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1053 : Prop where
  proof : ((pairCorners 14=pairCornerTable 14))

theorem pairCorners_table_14 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1053] : ((pairCorners 14=pairCornerTable 14)) := @OAI.SidorenkoCounterexample.ProofCertificate_1053.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1054 : Prop where
  proof : ((pairCorners 15=pairCornerTable 15))

theorem pairCorners_table_15 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1054] : ((pairCorners 15=pairCornerTable 15)) := @OAI.SidorenkoCounterexample.ProofCertificate_1054.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1055 : Prop where
  proof : ((pairCorners 16=pairCornerTable 16))

theorem pairCorners_table_16 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1055] : ((pairCorners 16=pairCornerTable 16)) := @OAI.SidorenkoCounterexample.ProofCertificate_1055.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1056 : Prop where
  proof : ((pairCorners 17=pairCornerTable 17))

theorem pairCorners_table_17 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1056] : ((pairCorners 17=pairCornerTable 17)) := @OAI.SidorenkoCounterexample.ProofCertificate_1056.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1057 : Prop where
  proof : ((pairCorners 18=pairCornerTable 18))

theorem pairCorners_table_18 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1057] : ((pairCorners 18=pairCornerTable 18)) := @OAI.SidorenkoCounterexample.ProofCertificate_1057.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1058 : Prop where
  proof : ((pairCorners 19=pairCornerTable 19))

theorem pairCorners_table_19 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1058] : ((pairCorners 19=pairCornerTable 19)) := @OAI.SidorenkoCounterexample.ProofCertificate_1058.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1059 : Prop where
  proof : ((pairCorners 20=pairCornerTable 20))

theorem pairCorners_table_20 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1059] : ((pairCorners 20=pairCornerTable 20)) := @OAI.SidorenkoCounterexample.ProofCertificate_1059.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1060 : Prop where
  proof : ((pairCorners 21=pairCornerTable 21))

theorem pairCorners_table_21 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1060] : ((pairCorners 21=pairCornerTable 21)) := @OAI.SidorenkoCounterexample.ProofCertificate_1060.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1061 : Prop where
  proof : ((pairCorners 22=pairCornerTable 22))

theorem pairCorners_table_22 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1061] : ((pairCorners 22=pairCornerTable 22)) := @OAI.SidorenkoCounterexample.ProofCertificate_1061.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1062 : Prop where
  proof : ((pairCorners 23=pairCornerTable 23))

theorem pairCorners_table_23 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1062] : ((pairCorners 23=pairCornerTable 23)) := @OAI.SidorenkoCounterexample.ProofCertificate_1062.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1063 : Prop where
  proof : ((pairCorners 24=pairCornerTable 24))

theorem pairCorners_table_24 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1063] : ((pairCorners 24=pairCornerTable 24)) := @OAI.SidorenkoCounterexample.ProofCertificate_1063.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1064 : Prop where
  proof : ((pairCorners 25=pairCornerTable 25))

theorem pairCorners_table_25 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1064] : ((pairCorners 25=pairCornerTable 25)) := @OAI.SidorenkoCounterexample.ProofCertificate_1064.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1065 : Prop where
  proof : ((pairCorners 26=pairCornerTable 26))

theorem pairCorners_table_26 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1065] : ((pairCorners 26=pairCornerTable 26)) := @OAI.SidorenkoCounterexample.ProofCertificate_1065.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1066 : Prop where
  proof : ((pairCorners 27=pairCornerTable 27))

theorem pairCorners_table_27 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1066] : ((pairCorners 27=pairCornerTable 27)) := @OAI.SidorenkoCounterexample.ProofCertificate_1066.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1067 : Prop where
  proof : ((pairCorners 28=pairCornerTable 28))

theorem pairCorners_table_28 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1067] : ((pairCorners 28=pairCornerTable 28)) := @OAI.SidorenkoCounterexample.ProofCertificate_1067.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1068 : Prop where
  proof : ((pairCorners 29=pairCornerTable 29))

theorem pairCorners_table_29 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1068] : ((pairCorners 29=pairCornerTable 29)) := @OAI.SidorenkoCounterexample.ProofCertificate_1068.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1069 : Prop where
  proof : ((pairCorners 30=pairCornerTable 30))

theorem pairCorners_table_30 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1069] : ((pairCorners 30=pairCornerTable 30)) := @OAI.SidorenkoCounterexample.ProofCertificate_1069.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1070 : Prop where
  proof : ((pairCorners 31=pairCornerTable 31))

theorem pairCorners_table_31 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1070] : ((pairCorners 31=pairCornerTable 31)) := @OAI.SidorenkoCounterexample.ProofCertificate_1070.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1071 : Prop where
  proof : ((pairCorners 32=pairCornerTable 32))

theorem pairCorners_table_32 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1071] : ((pairCorners 32=pairCornerTable 32)) := @OAI.SidorenkoCounterexample.ProofCertificate_1071.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1072 : Prop where
  proof : ((∀ (e : Fin 33),
    pairCorners e=pairCornerTable e))

theorem pairCorners_table [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1072] : ((∀ (e : Fin 33),
  pairCorners e=pairCornerTable e)) := @OAI.SidorenkoCounterexample.ProofCertificate_1072.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1073 : Prop where
  proof : ((∀ (k : ActCorner),
    cornerPairL k≠cornerPairR k))

theorem cornerPair_ne [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1073] : ((∀ (k : ActCorner),
  cornerPairL k≠cornerPairR k)) := @OAI.SidorenkoCounterexample.ProofCertificate_1073.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1074 : Prop where
  proof : ((pairCorners (cornerPairL (0,0)) ∩ pairCorners (cornerPairR (0,0))={(0,0)}))

theorem pairCorners_inter_0_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1074] : ((pairCorners (cornerPairL (0,0)) ∩ pairCorners (cornerPairR (0,0))={(0,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1074.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1075 : Prop where
  proof : ((pairCorners (cornerPairL (0,1)) ∩ pairCorners (cornerPairR (0,1))={(0,1)}))

theorem pairCorners_inter_0_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1075] : ((pairCorners (cornerPairL (0,1)) ∩ pairCorners (cornerPairR (0,1))={(0,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1075.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1076 : Prop where
  proof : ((pairCorners (cornerPairL (0,2)) ∩ pairCorners (cornerPairR (0,2))={(0,2)}))

theorem pairCorners_inter_0_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1076] : ((pairCorners (cornerPairL (0,2)) ∩ pairCorners (cornerPairR (0,2))={(0,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1076.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1077 : Prop where
  proof : ((pairCorners (cornerPairL (1,0)) ∩ pairCorners (cornerPairR (1,0))={(1,0)}))

theorem pairCorners_inter_1_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1077] : ((pairCorners (cornerPairL (1,0)) ∩ pairCorners (cornerPairR (1,0))={(1,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1077.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1078 : Prop where
  proof : ((pairCorners (cornerPairL (1,1)) ∩ pairCorners (cornerPairR (1,1))={(1,1)}))

theorem pairCorners_inter_1_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1078] : ((pairCorners (cornerPairL (1,1)) ∩ pairCorners (cornerPairR (1,1))={(1,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1078.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1079 : Prop where
  proof : ((pairCorners (cornerPairL (1,2)) ∩ pairCorners (cornerPairR (1,2))={(1,2)}))

theorem pairCorners_inter_1_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1079] : ((pairCorners (cornerPairL (1,2)) ∩ pairCorners (cornerPairR (1,2))={(1,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1079.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1080 : Prop where
  proof : ((pairCorners (cornerPairL (2,0)) ∩ pairCorners (cornerPairR (2,0))={(2,0)}))

theorem pairCorners_inter_2_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1080] : ((pairCorners (cornerPairL (2,0)) ∩ pairCorners (cornerPairR (2,0))={(2,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1080.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1081 : Prop where
  proof : ((pairCorners (cornerPairL (2,1)) ∩ pairCorners (cornerPairR (2,1))={(2,1)}))

theorem pairCorners_inter_2_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1081] : ((pairCorners (cornerPairL (2,1)) ∩ pairCorners (cornerPairR (2,1))={(2,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1081.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1082 : Prop where
  proof : ((pairCorners (cornerPairL (2,2)) ∩ pairCorners (cornerPairR (2,2))={(2,2)}))

theorem pairCorners_inter_2_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1082] : ((pairCorners (cornerPairL (2,2)) ∩ pairCorners (cornerPairR (2,2))={(2,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1082.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1083 : Prop where
  proof : ((pairCorners (cornerPairL (3,0)) ∩ pairCorners (cornerPairR (3,0))={(3,0)}))

theorem pairCorners_inter_3_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1083] : ((pairCorners (cornerPairL (3,0)) ∩ pairCorners (cornerPairR (3,0))={(3,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1083.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1084 : Prop where
  proof : ((pairCorners (cornerPairL (3,1)) ∩ pairCorners (cornerPairR (3,1))={(3,1)}))

theorem pairCorners_inter_3_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1084] : ((pairCorners (cornerPairL (3,1)) ∩ pairCorners (cornerPairR (3,1))={(3,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1084.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1085 : Prop where
  proof : ((pairCorners (cornerPairL (3,2)) ∩ pairCorners (cornerPairR (3,2))={(3,2)}))

theorem pairCorners_inter_3_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1085] : ((pairCorners (cornerPairL (3,2)) ∩ pairCorners (cornerPairR (3,2))={(3,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1085.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1086 : Prop where
  proof : ((pairCorners (cornerPairL (4,0)) ∩ pairCorners (cornerPairR (4,0))={(4,0)}))

theorem pairCorners_inter_4_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1086] : ((pairCorners (cornerPairL (4,0)) ∩ pairCorners (cornerPairR (4,0))={(4,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1086.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1087 : Prop where
  proof : ((pairCorners (cornerPairL (4,1)) ∩ pairCorners (cornerPairR (4,1))={(4,1)}))

theorem pairCorners_inter_4_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1087] : ((pairCorners (cornerPairL (4,1)) ∩ pairCorners (cornerPairR (4,1))={(4,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1087.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1088 : Prop where
  proof : ((pairCorners (cornerPairL (4,2)) ∩ pairCorners (cornerPairR (4,2))={(4,2)}))

theorem pairCorners_inter_4_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1088] : ((pairCorners (cornerPairL (4,2)) ∩ pairCorners (cornerPairR (4,2))={(4,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1088.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1089 : Prop where
  proof : ((pairCorners (cornerPairL (5,0)) ∩ pairCorners (cornerPairR (5,0))={(5,0)}))

theorem pairCorners_inter_5_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1089] : ((pairCorners (cornerPairL (5,0)) ∩ pairCorners (cornerPairR (5,0))={(5,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1089.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1090 : Prop where
  proof : ((pairCorners (cornerPairL (5,1)) ∩ pairCorners (cornerPairR (5,1))={(5,1)}))

theorem pairCorners_inter_5_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1090] : ((pairCorners (cornerPairL (5,1)) ∩ pairCorners (cornerPairR (5,1))={(5,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1090.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1091 : Prop where
  proof : ((pairCorners (cornerPairL (5,2)) ∩ pairCorners (cornerPairR (5,2))={(5,2)}))

theorem pairCorners_inter_5_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1091] : ((pairCorners (cornerPairL (5,2)) ∩ pairCorners (cornerPairR (5,2))={(5,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1091.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1092 : Prop where
  proof : ((pairCorners (cornerPairL (6,0)) ∩ pairCorners (cornerPairR (6,0))={(6,0)}))

theorem pairCorners_inter_6_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1092] : ((pairCorners (cornerPairL (6,0)) ∩ pairCorners (cornerPairR (6,0))={(6,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1092.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1093 : Prop where
  proof : ((pairCorners (cornerPairL (6,1)) ∩ pairCorners (cornerPairR (6,1))={(6,1)}))

theorem pairCorners_inter_6_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1093] : ((pairCorners (cornerPairL (6,1)) ∩ pairCorners (cornerPairR (6,1))={(6,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1093.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1094 : Prop where
  proof : ((pairCorners (cornerPairL (6,2)) ∩ pairCorners (cornerPairR (6,2))={(6,2)}))

theorem pairCorners_inter_6_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1094] : ((pairCorners (cornerPairL (6,2)) ∩ pairCorners (cornerPairR (6,2))={(6,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1094.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1095 : Prop where
  proof : ((pairCorners (cornerPairL (7,0)) ∩ pairCorners (cornerPairR (7,0))={(7,0)}))

theorem pairCorners_inter_7_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1095] : ((pairCorners (cornerPairL (7,0)) ∩ pairCorners (cornerPairR (7,0))={(7,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1095.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1096 : Prop where
  proof : ((pairCorners (cornerPairL (7,1)) ∩ pairCorners (cornerPairR (7,1))={(7,1)}))

theorem pairCorners_inter_7_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1096] : ((pairCorners (cornerPairL (7,1)) ∩ pairCorners (cornerPairR (7,1))={(7,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1096.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1097 : Prop where
  proof : ((pairCorners (cornerPairL (7,2)) ∩ pairCorners (cornerPairR (7,2))={(7,2)}))

theorem pairCorners_inter_7_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1097] : ((pairCorners (cornerPairL (7,2)) ∩ pairCorners (cornerPairR (7,2))={(7,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1097.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1098 : Prop where
  proof : ((pairCorners (cornerPairL (8,0)) ∩ pairCorners (cornerPairR (8,0))={(8,0)}))

theorem pairCorners_inter_8_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1098] : ((pairCorners (cornerPairL (8,0)) ∩ pairCorners (cornerPairR (8,0))={(8,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1098.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1099 : Prop where
  proof : ((pairCorners (cornerPairL (8,1)) ∩ pairCorners (cornerPairR (8,1))={(8,1)}))

theorem pairCorners_inter_8_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1099] : ((pairCorners (cornerPairL (8,1)) ∩ pairCorners (cornerPairR (8,1))={(8,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1099.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1100 : Prop where
  proof : ((pairCorners (cornerPairL (8,2)) ∩ pairCorners (cornerPairR (8,2))={(8,2)}))

theorem pairCorners_inter_8_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1100] : ((pairCorners (cornerPairL (8,2)) ∩ pairCorners (cornerPairR (8,2))={(8,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1100.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1101 : Prop where
  proof : ((pairCorners (cornerPairL (9,0)) ∩ pairCorners (cornerPairR (9,0))={(9,0)}))

theorem pairCorners_inter_9_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1101] : ((pairCorners (cornerPairL (9,0)) ∩ pairCorners (cornerPairR (9,0))={(9,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1101.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1102 : Prop where
  proof : ((pairCorners (cornerPairL (9,1)) ∩ pairCorners (cornerPairR (9,1))={(9,1)}))

theorem pairCorners_inter_9_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1102] : ((pairCorners (cornerPairL (9,1)) ∩ pairCorners (cornerPairR (9,1))={(9,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1102.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1103 : Prop where
  proof : ((pairCorners (cornerPairL (9,2)) ∩ pairCorners (cornerPairR (9,2))={(9,2)}))

theorem pairCorners_inter_9_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1103] : ((pairCorners (cornerPairL (9,2)) ∩ pairCorners (cornerPairR (9,2))={(9,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1103.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1104 : Prop where
  proof : ((pairCorners (cornerPairL (10,0)) ∩ pairCorners (cornerPairR (10,0))={(10,0)}))

theorem pairCorners_inter_10_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1104] : ((pairCorners (cornerPairL (10,0)) ∩ pairCorners (cornerPairR (10,0))={(10,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1104.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1105 : Prop where
  proof : ((pairCorners (cornerPairL (10,1)) ∩ pairCorners (cornerPairR (10,1))={(10,1)}))

theorem pairCorners_inter_10_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1105] : ((pairCorners (cornerPairL (10,1)) ∩ pairCorners (cornerPairR (10,1))={(10,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1105.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1106 : Prop where
  proof : ((pairCorners (cornerPairL (10,2)) ∩ pairCorners (cornerPairR (10,2))={(10,2)}))

theorem pairCorners_inter_10_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1106] : ((pairCorners (cornerPairL (10,2)) ∩ pairCorners (cornerPairR (10,2))={(10,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1106.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1107 : Prop where
  proof : ((pairCorners (cornerPairL (11,0)) ∩ pairCorners (cornerPairR (11,0))={(11,0)}))

theorem pairCorners_inter_11_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1107] : ((pairCorners (cornerPairL (11,0)) ∩ pairCorners (cornerPairR (11,0))={(11,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1107.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1108 : Prop where
  proof : ((pairCorners (cornerPairL (11,1)) ∩ pairCorners (cornerPairR (11,1))={(11,1)}))

theorem pairCorners_inter_11_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1108] : ((pairCorners (cornerPairL (11,1)) ∩ pairCorners (cornerPairR (11,1))={(11,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1108.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1109 : Prop where
  proof : ((pairCorners (cornerPairL (11,2)) ∩ pairCorners (cornerPairR (11,2))={(11,2)}))

theorem pairCorners_inter_11_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1109] : ((pairCorners (cornerPairL (11,2)) ∩ pairCorners (cornerPairR (11,2))={(11,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1109.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1110 : Prop where
  proof : ((pairCorners (cornerPairL (12,0)) ∩ pairCorners (cornerPairR (12,0))={(12,0)}))

theorem pairCorners_inter_12_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1110] : ((pairCorners (cornerPairL (12,0)) ∩ pairCorners (cornerPairR (12,0))={(12,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1110.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1111 : Prop where
  proof : ((pairCorners (cornerPairL (12,1)) ∩ pairCorners (cornerPairR (12,1))={(12,1)}))

theorem pairCorners_inter_12_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1111] : ((pairCorners (cornerPairL (12,1)) ∩ pairCorners (cornerPairR (12,1))={(12,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1111.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1112 : Prop where
  proof : ((pairCorners (cornerPairL (12,2)) ∩ pairCorners (cornerPairR (12,2))={(12,2)}))

theorem pairCorners_inter_12_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1112] : ((pairCorners (cornerPairL (12,2)) ∩ pairCorners (cornerPairR (12,2))={(12,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1112.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1113 : Prop where
  proof : ((pairCorners (cornerPairL (13,0)) ∩ pairCorners (cornerPairR (13,0))={(13,0)}))

theorem pairCorners_inter_13_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1113] : ((pairCorners (cornerPairL (13,0)) ∩ pairCorners (cornerPairR (13,0))={(13,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1113.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1114 : Prop where
  proof : ((pairCorners (cornerPairL (13,1)) ∩ pairCorners (cornerPairR (13,1))={(13,1)}))

theorem pairCorners_inter_13_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1114] : ((pairCorners (cornerPairL (13,1)) ∩ pairCorners (cornerPairR (13,1))={(13,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1114.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1115 : Prop where
  proof : ((pairCorners (cornerPairL (13,2)) ∩ pairCorners (cornerPairR (13,2))={(13,2)}))

theorem pairCorners_inter_13_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1115] : ((pairCorners (cornerPairL (13,2)) ∩ pairCorners (cornerPairR (13,2))={(13,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1115.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1116 : Prop where
  proof : ((pairCorners (cornerPairL (14,0)) ∩ pairCorners (cornerPairR (14,0))={(14,0)}))

theorem pairCorners_inter_14_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1116] : ((pairCorners (cornerPairL (14,0)) ∩ pairCorners (cornerPairR (14,0))={(14,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1116.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1117 : Prop where
  proof : ((pairCorners (cornerPairL (14,1)) ∩ pairCorners (cornerPairR (14,1))={(14,1)}))

theorem pairCorners_inter_14_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1117] : ((pairCorners (cornerPairL (14,1)) ∩ pairCorners (cornerPairR (14,1))={(14,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1117.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1118 : Prop where
  proof : ((pairCorners (cornerPairL (14,2)) ∩ pairCorners (cornerPairR (14,2))={(14,2)}))

theorem pairCorners_inter_14_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1118] : ((pairCorners (cornerPairL (14,2)) ∩ pairCorners (cornerPairR (14,2))={(14,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1118.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1119 : Prop where
  proof : ((pairCorners (cornerPairL (15,0)) ∩ pairCorners (cornerPairR (15,0))={(15,0)}))

theorem pairCorners_inter_15_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1119] : ((pairCorners (cornerPairL (15,0)) ∩ pairCorners (cornerPairR (15,0))={(15,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1119.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1120 : Prop where
  proof : ((pairCorners (cornerPairL (15,1)) ∩ pairCorners (cornerPairR (15,1))={(15,1)}))

theorem pairCorners_inter_15_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1120] : ((pairCorners (cornerPairL (15,1)) ∩ pairCorners (cornerPairR (15,1))={(15,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1120.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1121 : Prop where
  proof : ((pairCorners (cornerPairL (15,2)) ∩ pairCorners (cornerPairR (15,2))={(15,2)}))

theorem pairCorners_inter_15_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1121] : ((pairCorners (cornerPairL (15,2)) ∩ pairCorners (cornerPairR (15,2))={(15,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1121.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1122 : Prop where
  proof : ((pairCorners (cornerPairL (16,0)) ∩ pairCorners (cornerPairR (16,0))={(16,0)}))

theorem pairCorners_inter_16_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1122] : ((pairCorners (cornerPairL (16,0)) ∩ pairCorners (cornerPairR (16,0))={(16,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1122.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1123 : Prop where
  proof : ((pairCorners (cornerPairL (16,1)) ∩ pairCorners (cornerPairR (16,1))={(16,1)}))

theorem pairCorners_inter_16_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1123] : ((pairCorners (cornerPairL (16,1)) ∩ pairCorners (cornerPairR (16,1))={(16,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1123.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1124 : Prop where
  proof : ((pairCorners (cornerPairL (16,2)) ∩ pairCorners (cornerPairR (16,2))={(16,2)}))

theorem pairCorners_inter_16_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1124] : ((pairCorners (cornerPairL (16,2)) ∩ pairCorners (cornerPairR (16,2))={(16,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1124.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1125 : Prop where
  proof : ((pairCorners (cornerPairL (17,0)) ∩ pairCorners (cornerPairR (17,0))={(17,0)}))

theorem pairCorners_inter_17_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1125] : ((pairCorners (cornerPairL (17,0)) ∩ pairCorners (cornerPairR (17,0))={(17,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1125.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1126 : Prop where
  proof : ((pairCorners (cornerPairL (17,1)) ∩ pairCorners (cornerPairR (17,1))={(17,1)}))

theorem pairCorners_inter_17_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1126] : ((pairCorners (cornerPairL (17,1)) ∩ pairCorners (cornerPairR (17,1))={(17,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1126.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1127 : Prop where
  proof : ((pairCorners (cornerPairL (17,2)) ∩ pairCorners (cornerPairR (17,2))={(17,2)}))

theorem pairCorners_inter_17_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1127] : ((pairCorners (cornerPairL (17,2)) ∩ pairCorners (cornerPairR (17,2))={(17,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1127.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1128 : Prop where
  proof : ((pairCorners (cornerPairL (18,0)) ∩ pairCorners (cornerPairR (18,0))={(18,0)}))

theorem pairCorners_inter_18_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1128] : ((pairCorners (cornerPairL (18,0)) ∩ pairCorners (cornerPairR (18,0))={(18,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1128.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1129 : Prop where
  proof : ((pairCorners (cornerPairL (18,1)) ∩ pairCorners (cornerPairR (18,1))={(18,1)}))

theorem pairCorners_inter_18_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1129] : ((pairCorners (cornerPairL (18,1)) ∩ pairCorners (cornerPairR (18,1))={(18,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1129.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1130 : Prop where
  proof : ((pairCorners (cornerPairL (18,2)) ∩ pairCorners (cornerPairR (18,2))={(18,2)}))

theorem pairCorners_inter_18_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1130] : ((pairCorners (cornerPairL (18,2)) ∩ pairCorners (cornerPairR (18,2))={(18,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1130.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1131 : Prop where
  proof : ((pairCorners (cornerPairL (19,0)) ∩ pairCorners (cornerPairR (19,0))={(19,0)}))

theorem pairCorners_inter_19_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1131] : ((pairCorners (cornerPairL (19,0)) ∩ pairCorners (cornerPairR (19,0))={(19,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1131.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1132 : Prop where
  proof : ((pairCorners (cornerPairL (19,1)) ∩ pairCorners (cornerPairR (19,1))={(19,1)}))

theorem pairCorners_inter_19_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1132] : ((pairCorners (cornerPairL (19,1)) ∩ pairCorners (cornerPairR (19,1))={(19,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1132.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1133 : Prop where
  proof : ((pairCorners (cornerPairL (19,2)) ∩ pairCorners (cornerPairR (19,2))={(19,2)}))

theorem pairCorners_inter_19_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1133] : ((pairCorners (cornerPairL (19,2)) ∩ pairCorners (cornerPairR (19,2))={(19,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1133.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1134 : Prop where
  proof : ((pairCorners (cornerPairL (20,0)) ∩ pairCorners (cornerPairR (20,0))={(20,0)}))

theorem pairCorners_inter_20_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1134] : ((pairCorners (cornerPairL (20,0)) ∩ pairCorners (cornerPairR (20,0))={(20,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1134.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1135 : Prop where
  proof : ((pairCorners (cornerPairL (20,1)) ∩ pairCorners (cornerPairR (20,1))={(20,1)}))

theorem pairCorners_inter_20_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1135] : ((pairCorners (cornerPairL (20,1)) ∩ pairCorners (cornerPairR (20,1))={(20,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1135.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1136 : Prop where
  proof : ((pairCorners (cornerPairL (20,2)) ∩ pairCorners (cornerPairR (20,2))={(20,2)}))

theorem pairCorners_inter_20_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1136] : ((pairCorners (cornerPairL (20,2)) ∩ pairCorners (cornerPairR (20,2))={(20,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1136.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1137 : Prop where
  proof : ((pairCorners (cornerPairL (21,0)) ∩ pairCorners (cornerPairR (21,0))={(21,0)}))

theorem pairCorners_inter_21_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1137] : ((pairCorners (cornerPairL (21,0)) ∩ pairCorners (cornerPairR (21,0))={(21,0)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1137.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1138 : Prop where
  proof : ((pairCorners (cornerPairL (21,1)) ∩ pairCorners (cornerPairR (21,1))={(21,1)}))

theorem pairCorners_inter_21_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1138] : ((pairCorners (cornerPairL (21,1)) ∩ pairCorners (cornerPairR (21,1))={(21,1)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1138.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1139 : Prop where
  proof : ((pairCorners (cornerPairL (21,2)) ∩ pairCorners (cornerPairR (21,2))={(21,2)}))

theorem pairCorners_inter_21_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1139] : ((pairCorners (cornerPairL (21,2)) ∩ pairCorners (cornerPairR (21,2))={(21,2)})) := @OAI.SidorenkoCounterexample.ProofCertificate_1139.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1140 : Prop where
  proof : ((∀ (k : ActCorner),
    pairCorners (cornerPairL k) ∩ pairCorners (cornerPairR k)={k}))

theorem pairCorners_inter [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1140] : ((∀ (k : ActCorner),
  pairCorners (cornerPairL k) ∩ pairCorners (cornerPairR k)={k})) := @OAI.SidorenkoCounterexample.ProofCertificate_1140.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1141 : Prop where
  proof : ((∀ (e : Fin 33),
    (pairCorners e).card=4))

theorem pairCorners_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1141] : ((∀ (e : Fin 33),
  (pairCorners e).card=4)) := @OAI.SidorenkoCounterexample.ProofCertificate_1141.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1142 : Prop where
  proof : ((∀ (k : ActCorner),
    k∈pairCorners (cornerPairL k)))

theorem cornerPairL_mem [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1142] : ((∀ (k : ActCorner),
  k∈pairCorners (cornerPairL k))) := @OAI.SidorenkoCounterexample.ProofCertificate_1142.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1143 : Prop where
  proof : ((∀ (k : ActCorner),
    k∈pairCorners (cornerPairR k)))

theorem cornerPairR_mem [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1143] : ((∀ (k : ActCorner),
  k∈pairCorners (cornerPairR k))) := @OAI.SidorenkoCounterexample.ProofCertificate_1143.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1144 : Prop where
  proof : ((∀ (k : ActCorner),
    cornerGamma k≠∅))

theorem cornerGamma_nonempty [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1144] : ((∀ (k : ActCorner),
  cornerGamma k≠∅)) := @OAI.SidorenkoCounterexample.ProofCertificate_1144.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1145 : Prop where
  proof : ((∀ (k : ActCorner),
    ¬cornerMax k⊆cornerGamma k))

theorem cornerMax_not_sub [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1145] : ((∀ (k : ActCorner),
  ¬cornerMax k⊆cornerGamma k)) := @OAI.SidorenkoCounterexample.ProofCertificate_1145.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1146 : Prop where
  proof : ((cornerMax (2,0) ∩ cornerMax (2,1) ∩ cornerMax (3,0) ∩ cornerMax (3,1)=pairCorners 0))

theorem supportIntersect_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1146] : ((cornerMax (2,0) ∩ cornerMax (2,1) ∩ cornerMax (3,0) ∩ cornerMax (3,1)=pairCorners 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1146.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1147 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 0,k∈cornerMax b) ↔ k∈pairCorners 0))

theorem corner_support_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1147] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 0,k∈cornerMax b) ↔ k∈pairCorners 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1147.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1148 : Prop where
  proof : ((cornerMax (0,0) ∩ cornerMax (0,2) ∩ cornerMax (2,0) ∩ cornerMax (2,2)=pairCorners 1))

theorem supportIntersect_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1148] : ((cornerMax (0,0) ∩ cornerMax (0,2) ∩ cornerMax (2,0) ∩ cornerMax (2,2)=pairCorners 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1148.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1149 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 1,k∈cornerMax b) ↔ k∈pairCorners 1))

theorem corner_support_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1149] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 1,k∈cornerMax b) ↔ k∈pairCorners 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1149.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1150 : Prop where
  proof : ((cornerMax (2,1) ∩ cornerMax (2,2) ∩ cornerMax (8,0) ∩ cornerMax (8,1)=pairCorners 2))

theorem supportIntersect_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1150] : ((cornerMax (2,1) ∩ cornerMax (2,2) ∩ cornerMax (8,0) ∩ cornerMax (8,1)=pairCorners 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_1150.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1151 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 2,k∈cornerMax b) ↔ k∈pairCorners 2))

theorem corner_support_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1151] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 2,k∈cornerMax b) ↔ k∈pairCorners 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_1151.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1152 : Prop where
  proof : ((cornerMax (1,0) ∩ cornerMax (1,2) ∩ cornerMax (3,0) ∩ cornerMax (3,2)=pairCorners 3))

theorem supportIntersect_3 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1152] : ((cornerMax (1,0) ∩ cornerMax (1,2) ∩ cornerMax (3,0) ∩ cornerMax (3,2)=pairCorners 3)) := @OAI.SidorenkoCounterexample.ProofCertificate_1152.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1153 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 3,k∈cornerMax b) ↔ k∈pairCorners 3))

theorem corner_support_3 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1153] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 3,k∈cornerMax b) ↔ k∈pairCorners 3)) := @OAI.SidorenkoCounterexample.ProofCertificate_1153.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1154 : Prop where
  proof : ((cornerMax (3,1) ∩ cornerMax (3,2) ∩ cornerMax (9,0) ∩ cornerMax (9,2)=pairCorners 4))

theorem supportIntersect_4 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1154] : ((cornerMax (3,1) ∩ cornerMax (3,2) ∩ cornerMax (9,0) ∩ cornerMax (9,2)=pairCorners 4)) := @OAI.SidorenkoCounterexample.ProofCertificate_1154.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1155 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 4,k∈cornerMax b) ↔ k∈pairCorners 4))

theorem corner_support_4 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1155] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 4,k∈cornerMax b) ↔ k∈pairCorners 4)) := @OAI.SidorenkoCounterexample.ProofCertificate_1155.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1156 : Prop where
  proof : ((cornerMax (0,0) ∩ cornerMax (0,1) ∩ cornerMax (1,0) ∩ cornerMax (1,1)=pairCorners 5))

theorem supportIntersect_5 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1156] : ((cornerMax (0,0) ∩ cornerMax (0,1) ∩ cornerMax (1,0) ∩ cornerMax (1,1)=pairCorners 5)) := @OAI.SidorenkoCounterexample.ProofCertificate_1156.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1157 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 5,k∈cornerMax b) ↔ k∈pairCorners 5))

theorem corner_support_5 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1157] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 5,k∈cornerMax b) ↔ k∈pairCorners 5)) := @OAI.SidorenkoCounterexample.ProofCertificate_1157.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1158 : Prop where
  proof : ((cornerMax (0,1) ∩ cornerMax (0,2) ∩ cornerMax (4,0) ∩ cornerMax (4,1)=pairCorners 6))

theorem supportIntersect_6 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1158] : ((cornerMax (0,1) ∩ cornerMax (0,2) ∩ cornerMax (4,0) ∩ cornerMax (4,1)=pairCorners 6)) := @OAI.SidorenkoCounterexample.ProofCertificate_1158.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1159 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 6,k∈cornerMax b) ↔ k∈pairCorners 6))

theorem corner_support_6 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1159] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 6,k∈cornerMax b) ↔ k∈pairCorners 6)) := @OAI.SidorenkoCounterexample.ProofCertificate_1159.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1160 : Prop where
  proof : ((cornerMax (8,0) ∩ cornerMax (8,2) ∩ cornerMax (9,0) ∩ cornerMax (9,1)=pairCorners 7))

theorem supportIntersect_7 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1160] : ((cornerMax (8,0) ∩ cornerMax (8,2) ∩ cornerMax (9,0) ∩ cornerMax (9,1)=pairCorners 7)) := @OAI.SidorenkoCounterexample.ProofCertificate_1160.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1161 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 7,k∈cornerMax b) ↔ k∈pairCorners 7))

theorem corner_support_7 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1161] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 7,k∈cornerMax b) ↔ k∈pairCorners 7)) := @OAI.SidorenkoCounterexample.ProofCertificate_1161.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1162 : Prop where
  proof : ((cornerMax (8,1) ∩ cornerMax (8,2) ∩ cornerMax (10,0) ∩ cornerMax (10,1)=pairCorners 8))

theorem supportIntersect_8 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1162] : ((cornerMax (8,1) ∩ cornerMax (8,2) ∩ cornerMax (10,0) ∩ cornerMax (10,1)=pairCorners 8)) := @OAI.SidorenkoCounterexample.ProofCertificate_1162.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1163 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 8,k∈cornerMax b) ↔ k∈pairCorners 8))

theorem corner_support_8 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1163] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 8,k∈cornerMax b) ↔ k∈pairCorners 8)) := @OAI.SidorenkoCounterexample.ProofCertificate_1163.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1164 : Prop where
  proof : ((cornerMax (1,1) ∩ cornerMax (1,2) ∩ cornerMax (7,0) ∩ cornerMax (7,1)=pairCorners 9))

theorem supportIntersect_9 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1164] : ((cornerMax (1,1) ∩ cornerMax (1,2) ∩ cornerMax (7,0) ∩ cornerMax (7,1)=pairCorners 9)) := @OAI.SidorenkoCounterexample.ProofCertificate_1164.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1165 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 9,k∈cornerMax b) ↔ k∈pairCorners 9))

theorem corner_support_9 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1165] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 9,k∈cornerMax b) ↔ k∈pairCorners 9)) := @OAI.SidorenkoCounterexample.ProofCertificate_1165.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1166 : Prop where
  proof : ((cornerMax (9,1) ∩ cornerMax (9,2) ∩ cornerMax (12,0) ∩ cornerMax (12,2)=pairCorners 10))

theorem supportIntersect_10 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1166] : ((cornerMax (9,1) ∩ cornerMax (9,2) ∩ cornerMax (12,0) ∩ cornerMax (12,2)=pairCorners 10)) := @OAI.SidorenkoCounterexample.ProofCertificate_1166.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1167 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 10,k∈cornerMax b) ↔ k∈pairCorners 10))

theorem corner_support_10 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1167] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 10,k∈cornerMax b) ↔ k∈pairCorners 10)) := @OAI.SidorenkoCounterexample.ProofCertificate_1167.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1168 : Prop where
  proof : ((cornerMax (4,0) ∩ cornerMax (4,2) ∩ cornerMax (5,0) ∩ cornerMax (5,2)=pairCorners 11))

theorem supportIntersect_11 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1168] : ((cornerMax (4,0) ∩ cornerMax (4,2) ∩ cornerMax (5,0) ∩ cornerMax (5,2)=pairCorners 11)) := @OAI.SidorenkoCounterexample.ProofCertificate_1168.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1169 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 11,k∈cornerMax b) ↔ k∈pairCorners 11))

theorem corner_support_11 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1169] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 11,k∈cornerMax b) ↔ k∈pairCorners 11)) := @OAI.SidorenkoCounterexample.ProofCertificate_1169.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1170 : Prop where
  proof : ((cornerMax (4,1) ∩ cornerMax (4,2) ∩ cornerMax (11,0) ∩ cornerMax (11,1)=pairCorners 12))

theorem supportIntersect_12 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1170] : ((cornerMax (4,1) ∩ cornerMax (4,2) ∩ cornerMax (11,0) ∩ cornerMax (11,1)=pairCorners 12)) := @OAI.SidorenkoCounterexample.ProofCertificate_1170.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1171 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 12,k∈cornerMax b) ↔ k∈pairCorners 12))

theorem corner_support_12 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1171] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 12,k∈cornerMax b) ↔ k∈pairCorners 12)) := @OAI.SidorenkoCounterexample.ProofCertificate_1171.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1172 : Prop where
  proof : ((cornerMax (10,0) ∩ cornerMax (10,2) ∩ cornerMax (11,0) ∩ cornerMax (11,2)=pairCorners 13))

theorem supportIntersect_13 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1172] : ((cornerMax (10,0) ∩ cornerMax (10,2) ∩ cornerMax (11,0) ∩ cornerMax (11,2)=pairCorners 13)) := @OAI.SidorenkoCounterexample.ProofCertificate_1172.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1173 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 13,k∈cornerMax b) ↔ k∈pairCorners 13))

theorem corner_support_13 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1173] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 13,k∈cornerMax b) ↔ k∈pairCorners 13)) := @OAI.SidorenkoCounterexample.ProofCertificate_1173.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1174 : Prop where
  proof : ((cornerMax (10,1) ∩ cornerMax (10,2) ∩ cornerMax (13,0) ∩ cornerMax (13,2)=pairCorners 14))

theorem supportIntersect_14 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1174] : ((cornerMax (10,1) ∩ cornerMax (10,2) ∩ cornerMax (13,0) ∩ cornerMax (13,2)=pairCorners 14)) := @OAI.SidorenkoCounterexample.ProofCertificate_1174.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1175 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 14,k∈cornerMax b) ↔ k∈pairCorners 14))

theorem corner_support_14 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1175] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 14,k∈cornerMax b) ↔ k∈pairCorners 14)) := @OAI.SidorenkoCounterexample.ProofCertificate_1175.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1176 : Prop where
  proof : ((cornerMax (6,0) ∩ cornerMax (6,2) ∩ cornerMax (7,0) ∩ cornerMax (7,2)=pairCorners 15))

theorem supportIntersect_15 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1176] : ((cornerMax (6,0) ∩ cornerMax (6,2) ∩ cornerMax (7,0) ∩ cornerMax (7,2)=pairCorners 15)) := @OAI.SidorenkoCounterexample.ProofCertificate_1176.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1177 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 15,k∈cornerMax b) ↔ k∈pairCorners 15))

theorem corner_support_15 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1177] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 15,k∈cornerMax b) ↔ k∈pairCorners 15)) := @OAI.SidorenkoCounterexample.ProofCertificate_1177.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1178 : Prop where
  proof : ((cornerMax (7,1) ∩ cornerMax (7,2) ∩ cornerMax (21,1) ∩ cornerMax (21,2)=pairCorners 16))

theorem supportIntersect_16 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1178] : ((cornerMax (7,1) ∩ cornerMax (7,2) ∩ cornerMax (21,1) ∩ cornerMax (21,2)=pairCorners 16)) := @OAI.SidorenkoCounterexample.ProofCertificate_1178.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1179 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 16,k∈cornerMax b) ↔ k∈pairCorners 16))

theorem corner_support_16 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1179] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 16,k∈cornerMax b) ↔ k∈pairCorners 16)) := @OAI.SidorenkoCounterexample.ProofCertificate_1179.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1180 : Prop where
  proof : ((cornerMax (12,0) ∩ cornerMax (12,1) ∩ cornerMax (13,0) ∩ cornerMax (13,1)=pairCorners 17))

theorem supportIntersect_17 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1180] : ((cornerMax (12,0) ∩ cornerMax (12,1) ∩ cornerMax (13,0) ∩ cornerMax (13,1)=pairCorners 17)) := @OAI.SidorenkoCounterexample.ProofCertificate_1180.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1181 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 17,k∈cornerMax b) ↔ k∈pairCorners 17))

theorem corner_support_17 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1181] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 17,k∈cornerMax b) ↔ k∈pairCorners 17)) := @OAI.SidorenkoCounterexample.ProofCertificate_1181.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1182 : Prop where
  proof : ((cornerMax (12,1) ∩ cornerMax (12,2) ∩ cornerMax (21,0) ∩ cornerMax (21,1)=pairCorners 18))

theorem supportIntersect_18 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1182] : ((cornerMax (12,1) ∩ cornerMax (12,2) ∩ cornerMax (21,0) ∩ cornerMax (21,1)=pairCorners 18)) := @OAI.SidorenkoCounterexample.ProofCertificate_1182.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1183 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 18,k∈cornerMax b) ↔ k∈pairCorners 18))

theorem corner_support_18 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1183] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 18,k∈cornerMax b) ↔ k∈pairCorners 18)) := @OAI.SidorenkoCounterexample.ProofCertificate_1183.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1184 : Prop where
  proof : ((cornerMax (5,0) ∩ cornerMax (5,1) ∩ cornerMax (6,0) ∩ cornerMax (6,1)=pairCorners 19))

theorem supportIntersect_19 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1184] : ((cornerMax (5,0) ∩ cornerMax (5,1) ∩ cornerMax (6,0) ∩ cornerMax (6,1)=pairCorners 19)) := @OAI.SidorenkoCounterexample.ProofCertificate_1184.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1185 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 19,k∈cornerMax b) ↔ k∈pairCorners 19))

theorem corner_support_19 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1185] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 19,k∈cornerMax b) ↔ k∈pairCorners 19)) := @OAI.SidorenkoCounterexample.ProofCertificate_1185.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1186 : Prop where
  proof : ((cornerMax (5,1) ∩ cornerMax (5,2) ∩ cornerMax (16,1) ∩ cornerMax (16,2)=pairCorners 20))

theorem supportIntersect_20 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1186] : ((cornerMax (5,1) ∩ cornerMax (5,2) ∩ cornerMax (16,1) ∩ cornerMax (16,2)=pairCorners 20)) := @OAI.SidorenkoCounterexample.ProofCertificate_1186.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1187 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 20,k∈cornerMax b) ↔ k∈pairCorners 20))

theorem corner_support_20 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1187] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 20,k∈cornerMax b) ↔ k∈pairCorners 20)) := @OAI.SidorenkoCounterexample.ProofCertificate_1187.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1188 : Prop where
  proof : ((cornerMax (11,1) ∩ cornerMax (11,2) ∩ cornerMax (17,1) ∩ cornerMax (17,2)=pairCorners 21))

theorem supportIntersect_21 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1188] : ((cornerMax (11,1) ∩ cornerMax (11,2) ∩ cornerMax (17,1) ∩ cornerMax (17,2)=pairCorners 21)) := @OAI.SidorenkoCounterexample.ProofCertificate_1188.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1189 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 21,k∈cornerMax b) ↔ k∈pairCorners 21))

theorem corner_support_21 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1189] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 21,k∈cornerMax b) ↔ k∈pairCorners 21)) := @OAI.SidorenkoCounterexample.ProofCertificate_1189.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1190 : Prop where
  proof : ((cornerMax (13,1) ∩ cornerMax (13,2) ∩ cornerMax (19,1) ∩ cornerMax (19,2)=pairCorners 22))

theorem supportIntersect_22 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1190] : ((cornerMax (13,1) ∩ cornerMax (13,2) ∩ cornerMax (19,1) ∩ cornerMax (19,2)=pairCorners 22)) := @OAI.SidorenkoCounterexample.ProofCertificate_1190.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1191 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 22,k∈cornerMax b) ↔ k∈pairCorners 22))

theorem corner_support_22 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1191] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 22,k∈cornerMax b) ↔ k∈pairCorners 22)) := @OAI.SidorenkoCounterexample.ProofCertificate_1191.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1192 : Prop where
  proof : ((cornerMax (6,1) ∩ cornerMax (6,2) ∩ cornerMax (18,1) ∩ cornerMax (18,2)=pairCorners 23))

theorem supportIntersect_23 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1192] : ((cornerMax (6,1) ∩ cornerMax (6,2) ∩ cornerMax (18,1) ∩ cornerMax (18,2)=pairCorners 23)) := @OAI.SidorenkoCounterexample.ProofCertificate_1192.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1193 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 23,k∈cornerMax b) ↔ k∈pairCorners 23))

theorem corner_support_23 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1193] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 23,k∈cornerMax b) ↔ k∈pairCorners 23)) := @OAI.SidorenkoCounterexample.ProofCertificate_1193.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1194 : Prop where
  proof : ((cornerMax (20,1) ∩ cornerMax (20,2) ∩ cornerMax (21,0) ∩ cornerMax (21,2)=pairCorners 24))

theorem supportIntersect_24 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1194] : ((cornerMax (20,1) ∩ cornerMax (20,2) ∩ cornerMax (21,0) ∩ cornerMax (21,2)=pairCorners 24)) := @OAI.SidorenkoCounterexample.ProofCertificate_1194.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1195 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 24,k∈cornerMax b) ↔ k∈pairCorners 24))

theorem corner_support_24 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1195] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 24,k∈cornerMax b) ↔ k∈pairCorners 24)) := @OAI.SidorenkoCounterexample.ProofCertificate_1195.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1196 : Prop where
  proof : ((cornerMax (14,0) ∩ cornerMax (14,2) ∩ cornerMax (16,0) ∩ cornerMax (16,1)=pairCorners 25))

theorem supportIntersect_25 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1196] : ((cornerMax (14,0) ∩ cornerMax (14,2) ∩ cornerMax (16,0) ∩ cornerMax (16,1)=pairCorners 25)) := @OAI.SidorenkoCounterexample.ProofCertificate_1196.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1197 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 25,k∈cornerMax b) ↔ k∈pairCorners 25))

theorem corner_support_25 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1197] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 25,k∈cornerMax b) ↔ k∈pairCorners 25)) := @OAI.SidorenkoCounterexample.ProofCertificate_1197.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1198 : Prop where
  proof : ((cornerMax (16,0) ∩ cornerMax (16,2) ∩ cornerMax (17,0) ∩ cornerMax (17,1)=pairCorners 26))

theorem supportIntersect_26 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1198] : ((cornerMax (16,0) ∩ cornerMax (16,2) ∩ cornerMax (17,0) ∩ cornerMax (17,1)=pairCorners 26)) := @OAI.SidorenkoCounterexample.ProofCertificate_1198.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1199 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 26,k∈cornerMax b) ↔ k∈pairCorners 26))

theorem corner_support_26 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1199] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 26,k∈cornerMax b) ↔ k∈pairCorners 26)) := @OAI.SidorenkoCounterexample.ProofCertificate_1199.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1200 : Prop where
  proof : ((cornerMax (15,0) ∩ cornerMax (15,2) ∩ cornerMax (17,0) ∩ cornerMax (17,2)=pairCorners 27))

theorem supportIntersect_27 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1200] : ((cornerMax (15,0) ∩ cornerMax (15,2) ∩ cornerMax (17,0) ∩ cornerMax (17,2)=pairCorners 27)) := @OAI.SidorenkoCounterexample.ProofCertificate_1200.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1201 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 27,k∈cornerMax b) ↔ k∈pairCorners 27))

theorem corner_support_27 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1201] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 27,k∈cornerMax b) ↔ k∈pairCorners 27)) := @OAI.SidorenkoCounterexample.ProofCertificate_1201.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1202 : Prop where
  proof : ((cornerMax (19,0) ∩ cornerMax (19,1) ∩ cornerMax (20,0) ∩ cornerMax (20,1)=pairCorners 28))

theorem supportIntersect_28 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1202] : ((cornerMax (19,0) ∩ cornerMax (19,1) ∩ cornerMax (20,0) ∩ cornerMax (20,1)=pairCorners 28)) := @OAI.SidorenkoCounterexample.ProofCertificate_1202.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1203 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 28,k∈cornerMax b) ↔ k∈pairCorners 28))

theorem corner_support_28 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1203] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 28,k∈cornerMax b) ↔ k∈pairCorners 28)) := @OAI.SidorenkoCounterexample.ProofCertificate_1203.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1204 : Prop where
  proof : ((cornerMax (15,1) ∩ cornerMax (15,2) ∩ cornerMax (19,0) ∩ cornerMax (19,2)=pairCorners 29))

theorem supportIntersect_29 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1204] : ((cornerMax (15,1) ∩ cornerMax (15,2) ∩ cornerMax (19,0) ∩ cornerMax (19,2)=pairCorners 29)) := @OAI.SidorenkoCounterexample.ProofCertificate_1204.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1205 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 29,k∈cornerMax b) ↔ k∈pairCorners 29))

theorem corner_support_29 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1205] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 29,k∈cornerMax b) ↔ k∈pairCorners 29)) := @OAI.SidorenkoCounterexample.ProofCertificate_1205.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1206 : Prop where
  proof : ((cornerMax (14,1) ∩ cornerMax (14,2) ∩ cornerMax (18,0) ∩ cornerMax (18,1)=pairCorners 30))

theorem supportIntersect_30 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1206] : ((cornerMax (14,1) ∩ cornerMax (14,2) ∩ cornerMax (18,0) ∩ cornerMax (18,1)=pairCorners 30)) := @OAI.SidorenkoCounterexample.ProofCertificate_1206.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1207 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 30,k∈cornerMax b) ↔ k∈pairCorners 30))

theorem corner_support_30 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1207] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 30,k∈cornerMax b) ↔ k∈pairCorners 30)) := @OAI.SidorenkoCounterexample.ProofCertificate_1207.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1208 : Prop where
  proof : ((cornerMax (18,0) ∩ cornerMax (18,2) ∩ cornerMax (20,0) ∩ cornerMax (20,2)=pairCorners 31))

theorem supportIntersect_31 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1208] : ((cornerMax (18,0) ∩ cornerMax (18,2) ∩ cornerMax (20,0) ∩ cornerMax (20,2)=pairCorners 31)) := @OAI.SidorenkoCounterexample.ProofCertificate_1208.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1209 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 31,k∈cornerMax b) ↔ k∈pairCorners 31))

theorem corner_support_31 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1209] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 31,k∈cornerMax b) ↔ k∈pairCorners 31)) := @OAI.SidorenkoCounterexample.ProofCertificate_1209.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1210 : Prop where
  proof : ((cornerMax (14,0) ∩ cornerMax (14,1) ∩ cornerMax (15,0) ∩ cornerMax (15,1)=pairCorners 32))

theorem supportIntersect_32 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1210] : ((cornerMax (14,0) ∩ cornerMax (14,1) ∩ cornerMax (15,0) ∩ cornerMax (15,1)=pairCorners 32)) := @OAI.SidorenkoCounterexample.ProofCertificate_1210.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1211 : Prop where
  proof : ((∀ (k : ActCorner),
    (∀ b∈pairCorners 32,k∈cornerMax b) ↔ k∈pairCorners 32))

theorem corner_support_32 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1211] : ((∀ (k : ActCorner),
  (∀ b∈pairCorners 32,k∈cornerMax b) ↔ k∈pairCorners 32)) := @OAI.SidorenkoCounterexample.ProofCertificate_1211.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1212 : Prop where
  proof : ((∀ (e : Fin 33) (k : ActCorner),
    (∀ b∈pairCorners e,k∈cornerMax b) ↔ k∈pairCorners e))

theorem corner_support [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1212] : ((∀ (e : Fin 33) (k : ActCorner),
  (∀ b∈pairCorners e,k∈cornerMax b) ↔ k∈pairCorners e)) := @OAI.SidorenkoCounterexample.ProofCertificate_1212.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1213 : Prop where
  proof : ((∀ (k : ActCorner),
    cornerGamma k⊆cornerMax k))

theorem cornerGamma_sub [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1213] : ((∀ (k : ActCorner),
  cornerGamma k⊆cornerMax k)) := @OAI.SidorenkoCounterexample.ProofCertificate_1213.proof certificateEvidence
end

def cornerSigma (k : ActCorner) : ℝ := if k=(0,0) then -1 else 1

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1214 : Prop where
  proof : ((∀ (k : ActCorner),
    |cornerSigma k|=1))

theorem cornerSigma_abs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1214] : ((∀ (k : ActCorner),
  |cornerSigma k|=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1214.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214]
noncomputable def cornerLaw (k : ActCorner) : FiniteLaw (Activation ActCorner) :=
  baseActivation (cornerMax k) (cornerGamma k) (cornerGamma_nonempty k) (cornerSigma k/2)
    (by rw [abs_div,cornerSigma_abs]; norm_num)
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1215 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner) (α : Finset ActCorner) (hα : α≠∅),
    (cornerLaw k).mean (activationPhi α)=0))

theorem cornerLaw_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1215] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner) (α : Finset ActCorner) (hα : α≠∅),
  (cornerLaw k).mean (activationPhi α)=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1215.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1216 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner) (α β : Finset ActCorner),
    activationMoment (cornerLaw k) α β=
        (1/2)*(if α∪β⊆cornerMax k then (if α=β then 1 else 0)+(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0)+
        (1/2)*(if α∪β⊆cornerGamma k then (if α=β then 1 else 0)-(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0)))

theorem cornerLaw_moment [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1216] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner) (α β : Finset ActCorner),
  activationMoment (cornerLaw k) α β=
      (1/2)*(if α∪β⊆cornerMax k then (if α=β then 1 else 0)+(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0)+
      (1/2)*(if α∪β⊆cornerGamma k then (if α=β then 1 else 0)-(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_1216.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1217 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner) (α β : Finset ActCorner)
        (h : activationMoment (cornerLaw k) α β≠0),
    α∪β⊆cornerMax k))

theorem cornerLaw_support [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1217] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner) (α β : Finset ActCorner)
      (h : activationMoment (cornerLaw k) α β≠0),
  α∪β⊆cornerMax k)) := @OAI.SidorenkoCounterexample.ProofCertificate_1217.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1218 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner) (α β : Finset ActCorner)
        (hd : Disjoint α β) (hn : α∪β≠∅),
    activationMoment (cornerLaw k) α β=0))

theorem cornerLaw_disjoint [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1218] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner) (α β : Finset ActCorner)
      (hd : Disjoint α β) (hn : α∪β≠∅),
  activationMoment (cornerLaw k) α β=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1218.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1219 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner),
    activationMoment (cornerLaw k) (pairCorners (cornerPairL k)) (pairCorners (cornerPairR k))=cornerSigma k/4))

theorem cornerLaw_value [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1219] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner),
  activationMoment (cornerLaw k) (pairCorners (cornerPairL k)) (pairCorners (cornerPairR k))=cornerSigma k/4)) := @OAI.SidorenkoCounterexample.ProofCertificate_1219.proof certificateEvidence
end

end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section Coefficients
variable {K : Type} [Fintype K] [DecidableEq K]
noncomputable def labelProduct (A : ActCorner → Finset K → Finset K → ℝ) (α : Fin 33 → Finset K) : ℝ :=
  ∏ k,A k (α (cornerPairL k)) (α (cornerPairR k))

noncomputable def nonemptyLabels : Finset (Fin 33 → Finset K) := Finset.univ.filter (fun α => ∀ e,α e≠∅)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1220 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α : Fin 33 → Finset K),
    α∈nonemptyLabels ↔ ∀ e,α e≠∅))

theorem mem_nonemptyLabels [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1220] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α : Fin 33 → Finset K),
  α∈nonemptyLabels ↔ ∀ e,α e≠∅)) := @OAI.SidorenkoCounterexample.ProofCertificate_1220.proof certificateEvidence
end

noncomputable def activeCoefficient (A : ActCorner → Finset K → Finset K → ℝ) : ℝ :=
  ∑ α∈nonemptyLabels,labelProduct A α

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1221 : Prop where
  proof : (∀ {K : Type}, (∀ (A : ActCorner → Finset K → Finset K → ℝ) (α : Fin 33 → Finset K)
        (h : labelProduct A α≠0) (k : ActCorner),
    A k (α (cornerPairL k)) (α (cornerPairR k))≠0))

theorem labelProduct_nonzero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1221] : (∀ {K : Type}, (∀ (A : ActCorner → Finset K → Finset K → ℝ) (α : Fin 33 → Finset K)
      (h : labelProduct A α≠0) (k : ActCorner),
  A k (α (cornerPairL k)) (α (cornerPairR k))≠0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1221.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1222 : Prop where
  proof : ((∀ (P : Fin 33 → Prop) (hs : ∀ j p q,P (facePair j p) ↔ P (facePair j q)),
    ∀ e,P e ↔ P 0))

theorem empty_propagation [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1222] : ((∀ (P : Fin 33 → Prop) (hs : ∀ j p q,P (facePair j p) ↔ P (facePair j q)),
  ∀ e,P e ↔ P 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1222.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1223 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K))
        (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) (α : Fin 33 → Finset K)
        (h : labelProduct (fun k => activationMoment (p k)) α≠0),
    (∀ e,α e=∅) ∨ (∀ e,α e≠∅)))

theorem labelProduct_empty_dichotomy [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1223] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K))
      (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) (α : Fin 33 → Finset K)
      (h : labelProduct (fun k => activationMoment (p k)) α≠0),
  (∀ e,α e=∅) ∨ (∀ e,α e≠∅))) := @OAI.SidorenkoCounterexample.ProofCertificate_1223.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1224 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K))
        (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0),
    (∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α)=
          1+activeCoefficient (fun k => activationMoment (p k))))

theorem allCoefficient_eq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1224] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K))
      (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0),
  (∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α)=
        1+activeCoefficient (fun k => activationMoment (p k)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1224.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1225 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (A : ActCorner → Finset K → Finset K → ℝ)
        (α₀ : Fin 33 → Finset K) (h₀ : ∀ e,α₀ e≠∅)
        (hu : ∀ α,(∀ e,α e≠∅) → labelProduct A α≠0 → α=α₀),
    activeCoefficient A=labelProduct A α₀))

theorem activeCoefficient_unique [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1225] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (A : ActCorner → Finset K → Finset K → ℝ)
      (α₀ : Fin 33 → Finset K) (h₀ : ∀ e,α₀ e≠∅)
      (hu : ∀ α,(∀ e,α e≠∅) → labelProduct A α≠0 → α=α₀),
  activeCoefficient A=labelProduct A α₀)) := @OAI.SidorenkoCounterexample.ProofCertificate_1225.proof certificateEvidence
end

end Coefficients
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1226 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (α : Fin 33 → Finset ActCorner) (hne : ∀ e,α e≠∅)
        (h : labelProduct (fun k => activationMoment (cornerLaw k)) α≠0),
    α=pairCorners))

theorem identity_labels_forced [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1226] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (α : Fin 33 → Finset ActCorner) (hne : ∀ e,α e≠∅)
      (h : labelProduct (fun k => activationMoment (cornerLaw k)) α≠0),
  α=pairCorners)) := @OAI.SidorenkoCounterexample.ProofCertificate_1226.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1227 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (labelProduct (fun k => activationMoment (cornerLaw k)) pairCorners= -(1/4:ℝ)^66))

theorem identity_labelProduct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1227] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (labelProduct (fun k => activationMoment (cornerLaw k)) pairCorners= -(1/4:ℝ)^66)) := @OAI.SidorenkoCounterexample.ProofCertificate_1227.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1228 : Prop where
  proof : ((∀ (e : Fin 33),
    pairCorners e≠∅))

theorem pairCorners_nonempty [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1228] : ((∀ (e : Fin 33),
  pairCorners e≠∅)) := @OAI.SidorenkoCounterexample.ProofCertificate_1228.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1229 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (activeCoefficient (fun k => activationMoment (cornerLaw k))= -(1/4:ℝ)^66))

theorem identity_activeCoefficient [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1229] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (activeCoefficient (fun k => activationMoment (cornerLaw k))= -(1/4:ℝ)^66)) := @OAI.SidorenkoCounterexample.ProofCertificate_1229.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type} [Fintype K] [DecidableEq K]
noncomputable def activationEntry (z : Activation K) (k : K) : ℝ := if k∈z.1 then boolSign (z.2 k) else 0

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1230 : Prop where
  proof : (∀ {K : Type} [inst : DecidableEq K], (∀ (α : Finset K) (z : Activation K),
    activationPhi α z=∏ k∈α,activationEntry z k))

theorem activationPhi_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1230] : (∀ {K : Type} [inst : DecidableEq K], (∀ (α : Finset K) (z : Activation K),
  activationPhi α z=∏ k∈α,activationEntry z k)) := @OAI.SidorenkoCounterexample.ProofCertificate_1230.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1231 : Prop where
  proof : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : Activation K) (k : K),
    |activationEntry z k|≤1))

theorem activationEntry_abs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1231] : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : Activation K) (k : K),
  |activationEntry z k|≤1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1231.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1232 : Prop where
  proof : ((∀ (a b : ℝ),
    uniformMean (fun η : Bool => (1+boolSign η*a)*(1+boolSign η*b))=1+a*b))

theorem bool_double_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1232] : ((∀ (a b : ℝ),
  uniformMean (fun η : Bool => (1+boolSign η*a)*(1+boolSign η*b))=1+a*b)) := @OAI.SidorenkoCounterexample.ProofCertificate_1232.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1233 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K], (∀ {I : Type} [Fintype I] [DecidableEq I] (f : I → K → ℝ),
    (∏ i,∏ k,(1+f i k))=∑ α : I → Finset K,∏ i,∏ k∈α i,f i k))

theorem product_one_add_expansion [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1233] : (∀ {K : Type} [inst : Fintype K], (∀ {I : Type} [Fintype I] [DecidableEq I] (f : I → K → ℝ),
  (∏ i,∏ k,(1+f i k))=∑ α : I → Finset K,∏ i,∏ k∈α i,f i k)) := @OAI.SidorenkoCounterexample.ProofCertificate_1233.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
def faceSlot : Fin 33 → Fin 2 → Fin 3 := ![![0, 0], ![1, 1], ![2, 0], ![1, 1], ![2, 1], ![0, 0], ![2, 0], ![1, 0], ![2, 0], ![2, 0], ![2, 1], ![1, 1], ![2, 0], ![1, 1], ![2, 1], ![1, 1], ![2, 2], ![0, 0], ![2, 0], ![0, 0], ![2, 2], ![2, 2], ![2, 2], ![2, 2], ![2, 1], ![1, 0], ![1, 0], ![1, 1], ![0, 0], ![2, 1], ![2, 0], ![1, 1], ![0, 0]]

def faceSide : Fin 22 → Fin 3 → Fin 2 := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 0, 0], ![1, 1, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 0], ![1, 1, 1]]

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1234 : Prop where
  proof : ((∀ e b,facePair (pairFace e b) (faceSlot e b)=e))

theorem faceSlot_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1234] : ((∀ e b,facePair (pairFace e b) (faceSlot e b)=e)) := @OAI.SidorenkoCounterexample.ProofCertificate_1234.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1235 : Prop where
  proof : ((∀ j k,pairFace (facePair j k) (faceSide j k)=j))

theorem faceSide_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1235] : ((∀ j k,pairFace (facePair j k) (faceSide j k)=j)) := @OAI.SidorenkoCounterexample.ProofCertificate_1235.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1236 : Prop where
  proof : ((∀ j k,faceSlot (facePair j k) (faceSide j k)=k))

theorem faceSlot_side [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1236] : ((∀ j k,faceSlot (facePair j k) (faceSide j k)=k)) := @OAI.SidorenkoCounterexample.ProofCertificate_1236.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1237 : Prop where
  proof : ((∀ e b,faceSide (pairFace e b) (faceSlot e b)=b))

theorem faceSide_slot [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1237] : ((∀ e b,faceSide (pairFace e b) (faceSlot e b)=b)) := @OAI.SidorenkoCounterexample.ProofCertificate_1237.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1235] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_1236] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_1234] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_1237]
def occurrencePairEquiv : (Fin 22 × Fin 3) ≃ (Fin 33 × Fin 2) where
  toFun a := (facePair a.1 a.2,faceSide a.1 a.2)
  invFun b := (pairFace b.1 b.2,faceSlot b.1 b.2)
  left_inv a := by simp only [faceSide_correct,faceSlot_side]
  right_inv b := by simp only [faceSlot_correct,faceSide_slot]
end

def pairCorner (e : Fin 33) (a : Fin 2 × Fin 2) : ActCorner :=
  (pairFace e a.1,if a.2=0 then slotLeft (faceSlot e a.1) else slotRight (faceSlot e a.1))

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1238 : Prop where
  proof : ((Finset.univ.image (pairCorner 0)=pairCorners 0))

theorem pairCorner_image_0 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1238] : ((Finset.univ.image (pairCorner 0)=pairCorners 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1238.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1239 : Prop where
  proof : ((Finset.univ.image (pairCorner 1)=pairCorners 1))

theorem pairCorner_image_1 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1239] : ((Finset.univ.image (pairCorner 1)=pairCorners 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1239.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1240 : Prop where
  proof : ((Finset.univ.image (pairCorner 2)=pairCorners 2))

theorem pairCorner_image_2 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1240] : ((Finset.univ.image (pairCorner 2)=pairCorners 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_1240.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1241 : Prop where
  proof : ((Finset.univ.image (pairCorner 3)=pairCorners 3))

theorem pairCorner_image_3 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1241] : ((Finset.univ.image (pairCorner 3)=pairCorners 3)) := @OAI.SidorenkoCounterexample.ProofCertificate_1241.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1242 : Prop where
  proof : ((Finset.univ.image (pairCorner 4)=pairCorners 4))

theorem pairCorner_image_4 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1242] : ((Finset.univ.image (pairCorner 4)=pairCorners 4)) := @OAI.SidorenkoCounterexample.ProofCertificate_1242.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1243 : Prop where
  proof : ((Finset.univ.image (pairCorner 5)=pairCorners 5))

theorem pairCorner_image_5 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1243] : ((Finset.univ.image (pairCorner 5)=pairCorners 5)) := @OAI.SidorenkoCounterexample.ProofCertificate_1243.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1244 : Prop where
  proof : ((Finset.univ.image (pairCorner 6)=pairCorners 6))

theorem pairCorner_image_6 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1244] : ((Finset.univ.image (pairCorner 6)=pairCorners 6)) := @OAI.SidorenkoCounterexample.ProofCertificate_1244.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1245 : Prop where
  proof : ((Finset.univ.image (pairCorner 7)=pairCorners 7))

theorem pairCorner_image_7 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1245] : ((Finset.univ.image (pairCorner 7)=pairCorners 7)) := @OAI.SidorenkoCounterexample.ProofCertificate_1245.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1246 : Prop where
  proof : ((Finset.univ.image (pairCorner 8)=pairCorners 8))

theorem pairCorner_image_8 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1246] : ((Finset.univ.image (pairCorner 8)=pairCorners 8)) := @OAI.SidorenkoCounterexample.ProofCertificate_1246.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1247 : Prop where
  proof : ((Finset.univ.image (pairCorner 9)=pairCorners 9))

theorem pairCorner_image_9 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1247] : ((Finset.univ.image (pairCorner 9)=pairCorners 9)) := @OAI.SidorenkoCounterexample.ProofCertificate_1247.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1248 : Prop where
  proof : ((Finset.univ.image (pairCorner 10)=pairCorners 10))

theorem pairCorner_image_10 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1248] : ((Finset.univ.image (pairCorner 10)=pairCorners 10)) := @OAI.SidorenkoCounterexample.ProofCertificate_1248.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1249 : Prop where
  proof : ((Finset.univ.image (pairCorner 11)=pairCorners 11))

theorem pairCorner_image_11 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1249] : ((Finset.univ.image (pairCorner 11)=pairCorners 11)) := @OAI.SidorenkoCounterexample.ProofCertificate_1249.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1250 : Prop where
  proof : ((Finset.univ.image (pairCorner 12)=pairCorners 12))

theorem pairCorner_image_12 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1250] : ((Finset.univ.image (pairCorner 12)=pairCorners 12)) := @OAI.SidorenkoCounterexample.ProofCertificate_1250.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1251 : Prop where
  proof : ((Finset.univ.image (pairCorner 13)=pairCorners 13))

theorem pairCorner_image_13 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1251] : ((Finset.univ.image (pairCorner 13)=pairCorners 13)) := @OAI.SidorenkoCounterexample.ProofCertificate_1251.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1252 : Prop where
  proof : ((Finset.univ.image (pairCorner 14)=pairCorners 14))

theorem pairCorner_image_14 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1252] : ((Finset.univ.image (pairCorner 14)=pairCorners 14)) := @OAI.SidorenkoCounterexample.ProofCertificate_1252.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1253 : Prop where
  proof : ((Finset.univ.image (pairCorner 15)=pairCorners 15))

theorem pairCorner_image_15 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1253] : ((Finset.univ.image (pairCorner 15)=pairCorners 15)) := @OAI.SidorenkoCounterexample.ProofCertificate_1253.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1254 : Prop where
  proof : ((Finset.univ.image (pairCorner 16)=pairCorners 16))

theorem pairCorner_image_16 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1254] : ((Finset.univ.image (pairCorner 16)=pairCorners 16)) := @OAI.SidorenkoCounterexample.ProofCertificate_1254.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1255 : Prop where
  proof : ((Finset.univ.image (pairCorner 17)=pairCorners 17))

theorem pairCorner_image_17 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1255] : ((Finset.univ.image (pairCorner 17)=pairCorners 17)) := @OAI.SidorenkoCounterexample.ProofCertificate_1255.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1256 : Prop where
  proof : ((Finset.univ.image (pairCorner 18)=pairCorners 18))

theorem pairCorner_image_18 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1256] : ((Finset.univ.image (pairCorner 18)=pairCorners 18)) := @OAI.SidorenkoCounterexample.ProofCertificate_1256.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1257 : Prop where
  proof : ((Finset.univ.image (pairCorner 19)=pairCorners 19))

theorem pairCorner_image_19 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1257] : ((Finset.univ.image (pairCorner 19)=pairCorners 19)) := @OAI.SidorenkoCounterexample.ProofCertificate_1257.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1258 : Prop where
  proof : ((Finset.univ.image (pairCorner 20)=pairCorners 20))

theorem pairCorner_image_20 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1258] : ((Finset.univ.image (pairCorner 20)=pairCorners 20)) := @OAI.SidorenkoCounterexample.ProofCertificate_1258.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1259 : Prop where
  proof : ((Finset.univ.image (pairCorner 21)=pairCorners 21))

theorem pairCorner_image_21 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1259] : ((Finset.univ.image (pairCorner 21)=pairCorners 21)) := @OAI.SidorenkoCounterexample.ProofCertificate_1259.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1260 : Prop where
  proof : ((Finset.univ.image (pairCorner 22)=pairCorners 22))

theorem pairCorner_image_22 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1260] : ((Finset.univ.image (pairCorner 22)=pairCorners 22)) := @OAI.SidorenkoCounterexample.ProofCertificate_1260.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1261 : Prop where
  proof : ((Finset.univ.image (pairCorner 23)=pairCorners 23))

theorem pairCorner_image_23 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1261] : ((Finset.univ.image (pairCorner 23)=pairCorners 23)) := @OAI.SidorenkoCounterexample.ProofCertificate_1261.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1262 : Prop where
  proof : ((Finset.univ.image (pairCorner 24)=pairCorners 24))

theorem pairCorner_image_24 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1262] : ((Finset.univ.image (pairCorner 24)=pairCorners 24)) := @OAI.SidorenkoCounterexample.ProofCertificate_1262.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1263 : Prop where
  proof : ((Finset.univ.image (pairCorner 25)=pairCorners 25))

theorem pairCorner_image_25 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1263] : ((Finset.univ.image (pairCorner 25)=pairCorners 25)) := @OAI.SidorenkoCounterexample.ProofCertificate_1263.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1264 : Prop where
  proof : ((Finset.univ.image (pairCorner 26)=pairCorners 26))

theorem pairCorner_image_26 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1264] : ((Finset.univ.image (pairCorner 26)=pairCorners 26)) := @OAI.SidorenkoCounterexample.ProofCertificate_1264.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1265 : Prop where
  proof : ((Finset.univ.image (pairCorner 27)=pairCorners 27))

theorem pairCorner_image_27 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1265] : ((Finset.univ.image (pairCorner 27)=pairCorners 27)) := @OAI.SidorenkoCounterexample.ProofCertificate_1265.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1266 : Prop where
  proof : ((Finset.univ.image (pairCorner 28)=pairCorners 28))

theorem pairCorner_image_28 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1266] : ((Finset.univ.image (pairCorner 28)=pairCorners 28)) := @OAI.SidorenkoCounterexample.ProofCertificate_1266.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1267 : Prop where
  proof : ((Finset.univ.image (pairCorner 29)=pairCorners 29))

theorem pairCorner_image_29 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1267] : ((Finset.univ.image (pairCorner 29)=pairCorners 29)) := @OAI.SidorenkoCounterexample.ProofCertificate_1267.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1268 : Prop where
  proof : ((Finset.univ.image (pairCorner 30)=pairCorners 30))

theorem pairCorner_image_30 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1268] : ((Finset.univ.image (pairCorner 30)=pairCorners 30)) := @OAI.SidorenkoCounterexample.ProofCertificate_1268.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1269 : Prop where
  proof : ((Finset.univ.image (pairCorner 31)=pairCorners 31))

theorem pairCorner_image_31 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1269] : ((Finset.univ.image (pairCorner 31)=pairCorners 31)) := @OAI.SidorenkoCounterexample.ProofCertificate_1269.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1270 : Prop where
  proof : ((Finset.univ.image (pairCorner 32)=pairCorners 32))

theorem pairCorner_image_32 [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1270] : ((Finset.univ.image (pairCorner 32)=pairCorners 32)) := @OAI.SidorenkoCounterexample.ProofCertificate_1270.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1271 : Prop where
  proof : ((∀ (e : Fin 33),
    Finset.univ.image (pairCorner e)=pairCorners e))

theorem pairCorner_image [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1271] : ((∀ (e : Fin 33),
  Finset.univ.image (pairCorner e)=pairCorners e)) := @OAI.SidorenkoCounterexample.ProofCertificate_1271.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1272 : Prop where
  proof : ((∀ (e : Fin 33),
    Function.Injective (pairCorner e)))

theorem pairCorner_inj [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1272] : ((∀ (e : Fin 33),
  Function.Injective (pairCorner e))) := @OAI.SidorenkoCounterexample.ProofCertificate_1272.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1273 : Prop where
  proof : ((∀ (e : Fin 33) (f : ActCorner → ℝ),
    (∏ k∈pairCorners e,f k)=∏ b : Fin 2,
          f (pairFace e b,slotLeft (faceSlot e b))*f (pairFace e b,slotRight (faceSlot e b))))

theorem pairCorners_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1273] : ((∀ (e : Fin 33) (f : ActCorner → ℝ),
  (∏ k∈pairCorners e,f k)=∏ b : Fin 2,
        f (pairFace e b,slotLeft (faceSlot e b))*f (pairFace e b,slotRight (faceSlot e b)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1273.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section
variable {I L A : Type} [Fintype I] [DecidableEq I] [Fintype L] [Fintype A]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1274 : Prop where
  proof : (∀ {I L A : Type} [inst : Fintype I] [inst : DecidableEq I] [inst : Fintype L] [inst : Fintype A], (∀ (p : I → FiniteLaw A) (f : L → I → A → ℝ)
        (g : (I → A) → ℝ) (c : L → ℝ) (hg : ∀ z,g z=∑ l,∏ i,f l i (z i))
        (hc : ∀ l,(∏ i,(p i).mean (f l i))=c l),
    (FiniteLaw.independent p).mean g=∑ l,c l))

theorem FiniteLaw.mean_expansion_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1274] : (∀ {I L A : Type} [inst : Fintype I] [inst : DecidableEq I] [inst : Fintype L] [inst : Fintype A], (∀ (p : I → FiniteLaw A) (f : L → I → A → ℝ)
      (g : (I → A) → ℝ) (c : L → ℝ) (hg : ∀ z,g z=∑ l,∏ i,f l i (z i))
      (hc : ∀ l,(∏ i,(p i).mean (f l i))=c l),
  (FiniteLaw.independent p).mean g=∑ l,c l)) := @OAI.SidorenkoCounterexample.ProofCertificate_1274.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1275 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I] [inst : DecidableEq I], (∀ (a b : I → ℝ),
    uniformMean (fun η : I → Bool => ∏ i,(1+boolSign (η i)*a i)*(1+boolSign (η i)*b i))=
        ∏ i,(1+a i*b i)))

theorem uniformMean_double_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1275] : (∀ {I : Type} [inst : Fintype I] [inst : DecidableEq I], (∀ (a b : I → ℝ),
  uniformMean (fun η : I → Bool => ∏ i,(1+boolSign (η i)*a i)*(1+boolSign (η i)*b i))=
      ∏ i,(1+a i*b i))) := @OAI.SidorenkoCounterexample.ProofCertificate_1275.proof certificateEvidence
end

end
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type} [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1276 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K)) (α : Fin 33 → Finset K),
    (∏ k,(p k).mean (fun z => activationPhi (α (cornerPairL k)) z*activationPhi (α (cornerPairR k)) z))=
        labelProduct (fun k => activationMoment (p k)) α))

theorem activationMoment_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1276] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K)) (α : Fin 33 → Finset K),
  (∏ k,(p k).mean (fun z => activationPhi (α (cornerPairL k)) z*activationPhi (α (cornerPairR k)) z))=
      labelProduct (fun k => activationMoment (p k)) α)) := @OAI.SidorenkoCounterexample.ProofCertificate_1276.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1277 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K)) (g : (ActCorner → Activation K) → ℝ)
        (hg : ∀z,g z=∑ α : Fin 33 → Finset K,∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k)),
    (FiniteLaw.independent p).mean g=∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α))

theorem mean_activation_expansion [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1277] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K)) (g : (ActCorner → Activation K) → ℝ)
      (hg : ∀z,g z=∑ α : Fin 33 → Finset K,∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k)),
  (FiniteLaw.independent p).mean g=∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α)) := @OAI.SidorenkoCounterexample.ProofCertificate_1277.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Expansion
variable {K : Type} [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1278 : Prop where
  proof : (∀ {K : Type} [inst : DecidableEq K], (∀ (α : Fin 33 → Finset K) (z : ActCorner → Activation K),
    (∏ e,∏ κ∈α e,∏ k∈pairCorners e,activationEntry (z k) κ)=
        ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k)))

theorem labels_incidence_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1278] : (∀ {K : Type} [inst : DecidableEq K], (∀ (α : Fin 33 → Finset K) (z : ActCorner → Activation K),
  (∏ e,∏ κ∈α e,∏ k∈pairCorners e,activationEntry (z k) κ)=
      ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k))) := @OAI.SidorenkoCounterexample.ProofCertificate_1278.proof certificateEvidence
end

noncomputable def expandedModel (z : ActCorner → Activation K) : ℝ :=
  ∏ κ,∏ e,(1+∏ k∈pairCorners e,activationEntry (z k) κ)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1279 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (z : ActCorner → Activation K),
    expandedModel z=∑ α : Fin 33 → Finset K,
          ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k)))

theorem expandedModel_expansion [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1279] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (z : ActCorner → Activation K),
  expandedModel z=∑ α : Fin 33 → Finset K,
        ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k))) := @OAI.SidorenkoCounterexample.ProofCertificate_1279.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1280 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K))
        (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0),
    (FiniteLaw.independent p).mean expandedModel=1+activeCoefficient (fun k => activationMoment (p k))))

theorem expandedModel_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1280] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K))
      (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0),
  (FiniteLaw.independent p).mean expandedModel=1+activeCoefficient (fun k => activationMoment (p k)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1280.proof certificateEvidence
end

noncomputable def coordinateActive (z : ActCorner → Activation K) (κ : K) (j : Fin 22) : Finset (Fin 3) :=
  Finset.univ.filter (fun k => κ∈(z (j,k)).1)

def coordinateSigns (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) : ℤ :=
  if (z (j,k)).2 κ then 1 else -1

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1281 : Prop where
  proof : (∀ {K : Type}, (∀ (z : ActCorner → Activation K) (κ : K),
    ∀ j k,coordinateSigns z κ j k=1 ∨ coordinateSigns z κ j k= -1))

theorem coordinateSigns_good [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1281] : (∀ {K : Type}, (∀ (z : ActCorner → Activation K) (κ : K),
  ∀ j k,coordinateSigns z κ j k=1 ∨ coordinateSigns z κ j k= -1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1281.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1282 : Prop where
  proof : (∀ {K : Type}, (∀ (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3),
    (coordinateSigns z κ j k : ℝ)=boolSign ((z (j,k)).2 κ)))

theorem coordinateSigns_real [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1282] : (∀ {K : Type}, (∀ (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3),
  (coordinateSigns z κ j k : ℝ)=boolSign ((z (j,k)).2 κ))) := @OAI.SidorenkoCounterexample.ProofCertificate_1282.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1283 : Prop where
  proof : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) (η : Fin 33 → Bool),
    (if slotLeft k∈coordinateActive z κ j ∧ slotRight k∈coordinateActive z κ j then
          1+(1:ℝ)*boolSign (η (facePair j k))*(coordinateSigns z κ j (slotLeft k):ℝ)*
            (coordinateSigns z κ j (slotRight k):ℝ) else 1)=
          1+boolSign (η (facePair j k))*(activationEntry (z (j,slotLeft k)) κ*activationEntry (z (j,slotRight k)) κ)))

theorem coordinate_factor [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1283] : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) (η : Fin 33 → Bool),
  (if slotLeft k∈coordinateActive z κ j ∧ slotRight k∈coordinateActive z κ j then
        1+(1:ℝ)*boolSign (η (facePair j k))*(coordinateSigns z κ j (slotLeft k):ℝ)*
          (coordinateSigns z κ j (slotRight k):ℝ) else 1)=
        1+boolSign (η (facePair j k))*(activationEntry (z (j,slotLeft k)) κ*activationEntry (z (j,slotRight k)) κ))) := @OAI.SidorenkoCounterexample.ProofCertificate_1283.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1284 : Prop where
  proof : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : ActCorner → Activation K) (κ : K) (η : Fin 33 → Bool),
    boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ) η=
          ∏ e,∏ b : Fin 2,(1+boolSign (η e)*
            (activationEntry (z (pairFace e b,slotLeft (faceSlot e b))) κ*
             activationEntry (z (pairFace e b,slotRight (faceSlot e b))) κ))))

theorem coordinate_boolean_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1284] : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : ActCorner → Activation K) (κ : K) (η : Fin 33 → Bool),
  boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ) η=
        ∏ e,∏ b : Fin 2,(1+boolSign (η e)*
          (activationEntry (z (pairFace e b,slotLeft (faceSlot e b))) κ*
           activationEntry (z (pairFace e b,slotRight (faceSlot e b))) κ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1284.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1285 : Prop where
  proof : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : ActCorner → Activation K) (κ : K),
    uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ))=
          ∏ e,(1+∏ k∈pairCorners e,activationEntry (z k) κ)))

theorem coordinateModel_eq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1285] : (∀ {K : Type} [inst : DecidableEq K], (∀ (z : ActCorner → Activation K) (κ : K),
  uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ))=
        ∏ e,(1+∏ k∈pairCorners e,activationEntry (z k) κ))) := @OAI.SidorenkoCounterexample.ProofCertificate_1285.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1286 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (z : ActCorner → Activation K),
    (∏ κ,uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ)))=expandedModel z))

theorem coordinateModels_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1286] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (z : ActCorner → Activation K),
  (∏ κ,uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ)))=expandedModel z)) := @OAI.SidorenkoCounterexample.ProofCertificate_1286.proof certificateEvidence
end

end Expansion
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Fubini
variable {I J K A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]
noncomputable def coordinateArrayEquiv : ((I → K → A) × (J → K → B)) ≃ (K → (I → A) × (J → B)) where
  toFun x k := (fun i => x.1 i k,fun j => x.2 j k)
  invFun x := (fun i k => (x k).1 i,fun j k => (x k).2 j)
  left_inv _x := rfl
  right_inv _x := rfl

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1287 : Prop where
  proof : (∀ {I J K A B : Type} [inst : Fintype I] [inst : Fintype J] [inst : Fintype K] [inst : Fintype A] [inst : Fintype B]
      [inst : DecidableEq I] [inst : DecidableEq J] [inst : DecidableEq K], (∀ (f : K → (I → A) → (J → B) → ℝ),
    uniformMean (fun x : (I → K → A) × (J → K → B) =>
          ∏ k,f k (fun i => x.1 i k) (fun j => x.2 j k))=
          ∏ k,uniformMean (fun x : (I → A) × (J → B) => f k x.1 x.2)))

theorem uniformMean_coordinate_factor [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1287] : (∀ {I J K A B : Type} [inst : Fintype I] [inst : Fintype J] [inst : Fintype K] [inst : Fintype A] [inst : Fintype B]
    [inst : DecidableEq I] [inst : DecidableEq J] [inst : DecidableEq K], (∀ (f : K → (I → A) → (J → B) → ℝ),
  uniformMean (fun x : (I → K → A) × (J → K → B) =>
        ∏ k,f k (fun i => x.1 i k) (fun j => x.2 j k))=
        ∏ k,uniformMean (fun x : (I → A) × (J → B) => f k x.1 x.2))) := @OAI.SidorenkoCounterexample.ProofCertificate_1287.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1288 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (f : A → B → ℝ),
    uniformMean (fun b => p.mean (fun a => f a b))=p.mean (fun a => uniformMean (f a))))

theorem uniformMean_law_swap [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1288] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (f : A → B → ℝ),
  uniformMean (fun b => p.mean (fun a => f a b))=p.mean (fun a => uniformMean (f a)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1288.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1289 : Prop where
  proof : (∀ {I J : Type} [inst : Fintype I] [inst : Fintype J] [inst : DecidableEq I] [inst : DecidableEq J], (∀ {C : Type} [Fintype C]
        (e : I ≃ J) (p : J → FiniteLaw C) (f : (J → C) → ℝ),
    (FiniteLaw.independent (fun i => p (e i))).mean (fun x => f (fun j => x (e.symm j)))=
          (FiniteLaw.independent p).mean f))

theorem independent_mean_equiv [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1289] : (∀ {I J : Type} [inst : Fintype I] [inst : Fintype J] [inst : DecidableEq I] [inst : DecidableEq J], (∀ {C : Type} [Fintype C]
      (e : I ≃ J) (p : J → FiniteLaw C) (f : (J → C) → ℝ),
  (FiniteLaw.independent (fun i => p (e i))).mean (fun x => f (fun j => x (e.symm j)))=
        (FiniteLaw.independent p).mean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1289.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1290 : Prop where
  proof : (∀ {I A B : Type} [inst : Fintype I] [inst : Fintype A] [inst : Fintype B] [inst : DecidableEq I], (∀ (p : I → FiniteLaw A) (q : I → FiniteLaw B) (f : (I → A × B) → ℝ),
    (FiniteLaw.independent (fun i => (p i).prod (q i))).mean f=
          (FiniteLaw.independent p).mean (fun x => (FiniteLaw.independent q).mean (fun y => f (fun i => (x i,y i))))))

theorem independent_mean_prod [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1290] : (∀ {I A B : Type} [inst : Fintype I] [inst : Fintype A] [inst : Fintype B] [inst : DecidableEq I], (∀ (p : I → FiniteLaw A) (q : I → FiniteLaw B) (f : (I → A × B) → ℝ),
  (FiniteLaw.independent (fun i => (p i).prod (q i))).mean f=
        (FiniteLaw.independent p).mean (fun x => (FiniteLaw.independent q).mean (fun y => f (fun i => (x i,y i)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1290.proof certificateEvidence
end

end Fubini
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1291 : Prop where
  proof : ((∀ (j : Fin 22) (k : Fin 3),
    faceVertex j k∈faces j))

theorem faceVertex_mem [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1291] : ((∀ (j : Fin 22) (k : Fin 3),
  faceVertex j k∈faces j)) := @OAI.SidorenkoCounterexample.ProofCertificate_1291.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1292 : Prop where
  proof : ((∀ (j : Fin 22) (i : Fin 13) (hi : i∈faces j),
    ∃ k,faceVertex j k=i))

theorem faceVertex_surj [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1292] : ((∀ (j : Fin 22) (i : Fin 13) (hi : i∈faces j),
  ∃ k,faceVertex j k=i)) := @OAI.SidorenkoCounterexample.ProofCertificate_1292.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1293 : Prop where
  proof : ((∀ {M : Type} [CommMonoid M] (B : Finset (Fin 13 × Fin 22))
        (hB : B⊆corners) (f : Fin 13 × Fin 22 → M),
    (∏ c∈B,f c)=∏ j,∏ k∈faceActive B j,f (faceVertex j k,j)))

theorem corners_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1293] : ((∀ {M : Type} [CommMonoid M] (B : Finset (Fin 13 × Fin 22))
      (hB : B⊆corners) (f : Fin 13 × Fin 22 → M),
  (∏ c∈B,f c)=∏ j,∏ k∈faceActive B j,f (faceVertex j k,j))) := @OAI.SidorenkoCounterexample.ProofCertificate_1293.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1294 : Prop where
  proof : ((∀ (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ)
        (hξ : ∀ c∈B,ξ c=1 ∨ ξ c= -1),
    ∀ j k,faceSigns B ξ j k=1 ∨ faceSigns B ξ j k= -1))

theorem faceSigns_good [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1294] : ((∀ (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ)
      (hξ : ∀ c∈B,ξ c=1 ∨ ξ c= -1),
  ∀ j k,faceSigns B ξ j k=1 ∨ faceSigns B ξ j k= -1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1294.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1295 : Prop where
  proof : ((∀ (r : ℕ) (q : OddPrime)
        (B : Finset (Fin 13 × Fin 22)) (hB : B⊆corners) (ξ : Fin 13 × Fin 22 → ℤ),
    layerCorrelation (2*r) q B ξ=uniformMean (configurationProduct (K := ZMod q.val) r (faceActive B) (faceSigns B ξ))))

theorem layerCorrelation_configuration [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1295] : ((∀ (r : ℕ) (q : OddPrime)
      (B : Finset (Fin 13 × Fin 22)) (hB : B⊆corners) (ξ : Fin 13 × Fin 22 → ℤ),
  layerCorrelation (2*r) q B ξ=uniformMean (configurationProduct (K := ZMod q.val) r (faceActive B) (faceSigns B ξ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1295.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1296 : Prop where
  proof : ((∀ (j : Fin 22) (e : Fin 33),
        pairVertices e⊆faces j ↔ ∃ k,facePair j k=e))

theorem pair_sub_face_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1296] : ((∀ (j : Fin 22) (e : Fin 33),
      pairVertices e⊆faces j ↔ ∃ k,facePair j k=e)) := @OAI.SidorenkoCounterexample.ProofCertificate_1296.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1297 : Prop where
  proof : ((∀ (j : Fin 22) (f : Fin 33 → ℝ)
        (hf : ∀ e,¬pairVertices e⊆faces j → f e=1),
    (∏ e,f e)=∏ k,f (facePair j k)))

theorem product_facePair [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1297] : ((∀ (j : Fin 22) (f : Fin 33 → ℝ)
      (hf : ∀ e,¬pairVertices e⊆faces j → f e=1),
  (∏ e,f e)=∏ k,f (facePair j k))) := @OAI.SidorenkoCounterexample.ProofCertificate_1297.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1298 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0973] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0373]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0975], (∀ (c : ℝ) (B : Finset (Fin 13 × Fin 22))
        (ξ : Fin 13 × Fin 22 → ℤ) (η : Fin 33 → Bool) (j : Fin 22),
    (∏ e : ModelPair, if e.val⊆faces j ∧ (∀ i∈e.val,(i,j)∈B) then
          1+c*boolSign (η (pairModelEquiv.symm e))*∏ i∈e.val,(ξ (i,j):ℝ) else 1)=
        boolFacePolynomial c (faceActive B j) (faceSigns B ξ j) j η))

theorem modelFace_polynomial [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1298] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0973] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0373]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0975], (∀ (c : ℝ) (B : Finset (Fin 13 × Fin 22))
      (ξ : Fin 13 × Fin 22 → ℤ) (η : Fin 33 → Bool) (j : Fin 22),
  (∏ e : ModelPair, if e.val⊆faces j ∧ (∀ i∈e.val,(i,j)∈B) then
        1+c*boolSign (η (pairModelEquiv.symm e))*∏ i∈e.val,(ξ (i,j):ℝ) else 1)=
      boolFacePolynomial c (faceActive B j) (faceSigns B ξ j) j η)) := @OAI.SidorenkoCounterexample.ProofCertificate_1298.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0973] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0373] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0975]
noncomputable def pairBoolEquiv : (Fin 33 → Bool) ≃ (ModelPair → Bool) where
  toFun η := η ∘ pairModelEquiv.symm
  invFun η := η ∘ pairModelEquiv
  left_inv η := by funext e; simp
  right_inv η := by funext e; simp
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1299 : Prop where
  proof : ((∀ (r : ℕ) (q : OddPrime)
        (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ),
    signModelCorrelation (2*r) q B ξ=uniformMean
          (boolConfiguration (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) (faceActive B) (faceSigns B ξ))))

theorem signModelCorrelation_configuration [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1299] : ((∀ (r : ℕ) (q : OddPrime)
      (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ),
  signModelCorrelation (2*r) q B ξ=uniformMean
        (boolConfiguration (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) (faceActive B) (faceSigns B ξ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1299.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
noncomputable def boolTestError (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (c : ℝ) (q : OddPrime) : ℝ :=
  uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) => boolConfiguration c T ξ (pairBool X))-
    uniformMean (boolConfiguration c T ξ)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1300 : Prop where
  proof : ((∀ (r : ℕ) (hbig : 12≤2*r) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ) (c : ℝ),
    Tendsto
        (boolTestError r T ξ c) primeInfinity (nhds 0)))

theorem boolTestError_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1300] : ((∀ (r : ℕ) (hbig : 12≤2*r) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ) (c : ℝ),
  Tendsto
      (boolTestError r T ξ c) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_1300.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1301 : Prop where
  proof : ((∀ (r : ℕ) (hbig : 12≤2*r) (T : Fin 22 → Finset (Fin 3))
        (ξ : Fin 22 → Fin 3 → ℤ),
    Tendsto
        (fun q : OddPrime => boolTestError r T ξ
          (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) q) primeInfinity (nhds 0)))

theorem varyingBoolTestError_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1301] : ((∀ (r : ℕ) (hbig : 12≤2*r) (T : Fin 22 → Finset (Fin 3))
      (ξ : Fin 22 → Fin 3 → ℤ),
  Tendsto
      (fun q : OddPrime => boolTestError r T ξ
        (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) q) primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_1301.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1302 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (r : ℕ) (hlarge : singularTailThreshold≤2*r)
        (B : Finset (Fin 13 × Fin 22)) (hB : B⊆corners) (ξ : Fin 13 × Fin 22 → ℤ)
        (hξ : ∀ c∈B,ξ c=1 ∨ ξ c= -1),
    Tendsto
          (fun q : OddPrime => layerCorrelation (2*r) q B ξ-signModelCorrelation (2*r) q B ξ)
          primeInfinity (nhds 0)))

theorem rankLayerConvergence [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1302] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (r : ℕ) (hlarge : singularTailThreshold≤2*r)
      (B : Finset (Fin 13 × Fin 22)) (hB : B⊆corners) (ξ : Fin 13 × Fin 22 → ℤ)
      (hξ : ∀ c∈B,ξ c=1 ∨ ξ c= -1),
  Tendsto
        (fun q : OddPrime => layerCorrelation (2*r) q B ξ-signModelCorrelation (2*r) q B ξ)
        primeInfinity (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_1302.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1303 : Prop where
  proof : ((RankLayerLimit))

theorem rankLayerLimit_proved [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1303] : ((RankLayerLimit)) := @OAI.SidorenkoCounterexample.ProofCertificate_1303.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Filter
instance primeInfinity_neBot : NeBot primeInfinity := by
  apply Filter.comap_neBot
  intro s hs
  obtain ⟨N,hN⟩ := Filter.mem_atTop_sets.mp hs
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (max N 3)
  refine ⟨⟨q,hprime,by omega⟩,hN q (by omega)⟩

end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section MatrixActivation
variable {F K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
noncomputable def sampleMatrixKernel (r : ℕ) (z : Activation K)
    (x y : K → SymMatrix F (2*r)) : ℝ :=
  ∏ κ∈z.1,rankKernel F (2*r) r (if z.2 κ then 1 else -1) (x κ-y κ)

noncomputable def activationMatrixKernel (r : ℕ) (p : FiniteLaw (Activation K))
    (x y : K → SymMatrix F (2*r)) : ℝ := p.mean (fun z => sampleMatrixKernel r z x y)

noncomputable def matrixSampleProduct (r : ℕ) (z : ActCorner → Activation K)
    (x : Fin 13 → K → SymMatrix F (2*r)) (y : Fin 22 → K → SymMatrix F (2*r)) : ℝ :=
  ∏ k,sampleMatrixKernel r (z k) (x (cornerPoint k)) (y k.1)

noncomputable def conditionalMatrixMoment (r : ℕ) (p : ActCorner → FiniteLaw (Activation K)) : ℝ :=
  uniformMean (fun xy : (Fin 13 → K → SymMatrix F (2*r)) × (Fin 22 → K → SymMatrix F (2*r)) =>
    ∏ k,activationMatrixKernel r (p k) (xy.1 (cornerPoint k)) (xy.2 k.1))

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1304 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (r : ℕ) (z : ActCorner → Activation K)
        (x : Fin 13 → K → SymMatrix F (2*r)) (y : Fin 22 → K → SymMatrix F (2*r)),
    matrixSampleProduct r z x y=∏ κ,∏ j,∏ k∈coordinateActive z κ j,
          rankKernel F (2*r) r (coordinateSigns z κ j k) (x (faceVertex j k) κ-y j κ)))

theorem matrixSampleProduct_coordinates [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1304] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (r : ℕ) (z : ActCorner → Activation K)
      (x : Fin 13 → K → SymMatrix F (2*r)) (y : Fin 22 → K → SymMatrix F (2*r)),
  matrixSampleProduct r z x y=∏ κ,∏ j,∏ k∈coordinateActive z κ j,
        rankKernel F (2*r) r (coordinateSigns z κ j k) (x (faceVertex j k) κ-y j κ))) := @OAI.SidorenkoCounterexample.ProofCertificate_1304.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1305 : Prop where
  proof : (∀ {F : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ),
    uniformMean (fun xy : (Fin 13 → SymMatrix F (2*r)) × (Fin 22 → SymMatrix F (2*r)) =>
          ∏ j,∏ k∈T j,rankKernel F (2*r) r (ξ j k) (xy.1 (faceVertex j k)-xy.2 j))=
          uniformMean (configurationProduct (K := F) r T ξ)))

theorem coordinateMatrixIntegral [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1305] : (∀ {F : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ),
  uniformMean (fun xy : (Fin 13 → SymMatrix F (2*r)) × (Fin 22 → SymMatrix F (2*r)) =>
        ∏ j,∏ k∈T j,rankKernel F (2*r) r (ξ j k) (xy.1 (faceVertex j k)-xy.2 j))=
        uniformMean (configurationProduct (K := F) r T ξ))) := @OAI.SidorenkoCounterexample.ProofCertificate_1305.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1306 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (r : ℕ) (z : ActCorner → Activation K),
    uniformMean (fun xy : (Fin 13 → K → SymMatrix F (2*r)) × (Fin 22 → K → SymMatrix F (2*r)) =>
          matrixSampleProduct r z xy.1 xy.2)=
          ∏ κ,uniformMean (configurationProduct (K := F) r (coordinateActive z κ) (coordinateSigns z κ))))

theorem matrixSampleProduct_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1306] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (r : ℕ) (z : ActCorner → Activation K),
  uniformMean (fun xy : (Fin 13 → K → SymMatrix F (2*r)) × (Fin 22 → K → SymMatrix F (2*r)) =>
        matrixSampleProduct r z xy.1 xy.2)=
        ∏ κ,uniformMean (configurationProduct (K := F) r (coordinateActive z κ) (coordinateSigns z κ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1306.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1307 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (r : ℕ) (p : ActCorner → FiniteLaw (Activation K)),
    conditionalMatrixMoment (F := F) r p=(FiniteLaw.independent p).mean (fun z =>
          ∏ κ,uniformMean (configurationProduct (K := F) r (coordinateActive z κ) (coordinateSigns z κ)))))

theorem conditionalMatrixMoment_law [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1307] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (r : ℕ) (p : ActCorner → FiniteLaw (Activation K)),
  conditionalMatrixMoment (F := F) r p=(FiniteLaw.independent p).mean (fun z =>
        ∏ κ,uniformMean (configurationProduct (K := F) r (coordinateActive z κ) (coordinateSigns z κ))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1307.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1308 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (z : Activation K) (x y : K → SymMatrix F (2*r)),
    0≤ sampleMatrixKernel r z x y))

theorem sampleMatrixKernel_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1308] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (z : Activation K) (x y : K → SymMatrix F (2*r)),
  0≤ sampleMatrixKernel r z x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_1308.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1309 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (r : ℕ) (p : FiniteLaw (Activation K)) (x y : K → SymMatrix F (2*r)),
    0≤activationMatrixKernel r p x y))

theorem activationMatrixKernel_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1309] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (r : ℕ) (p : FiniteLaw (Activation K)) (x y : K → SymMatrix F (2*r)),
  0≤activationMatrixKernel r p x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_1309.proof certificateEvidence
end

end MatrixActivation
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1310 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (r : ℕ) (hl : singularTailThreshold≤2*(2*r))
        (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
        (hξ : ∀ j k,ξ j k=1 ∨ ξ j k= -1),
    Tendsto
        (fun q : OddPrime => uniformMean (configurationProduct (K := ZMod q.val) (2*r) T ξ))
        primeInfinity (nhds (uniformMean (boolConfiguration 1 T ξ)))))

theorem configuration_even_rank_limit [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1310] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (r : ℕ) (hl : singularTailThreshold≤2*(2*r))
      (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
      (hξ : ∀ j k,ξ j k=1 ∨ ξ j k= -1),
  Tendsto
      (fun q : OddPrime => uniformMean (configurationProduct (K := ZMod q.val) (2*r) T ξ))
      primeInfinity (nhds (uniformMean (boolConfiguration 1 T ξ))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1310.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1311 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ {K : Type} [Fintype K] [DecidableEq K]
        (r : ℕ) (hl : singularTailThreshold≤2*(2*r)) (p : ActCorner → FiniteLaw (Activation K))
        (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0),
    Tendsto
        (fun q : OddPrime => conditionalMatrixMoment (F := ZMod q.val) (2*r) p) primeInfinity
        (nhds (1+activeCoefficient (fun k => activationMoment (p k))))))

theorem conditionalMatrixMoment_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1311] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ {K : Type} [Fintype K] [DecidableEq K]
      (r : ℕ) (hl : singularTailThreshold≤2*(2*r)) (p : ActCorner → FiniteLaw (Activation K))
      (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0),
  Tendsto
      (fun q : OddPrime => conditionalMatrixMoment (F := ZMod q.val) (2*r) p) primeInfinity
      (nhds (1+activeCoefficient (fun k => activationMoment (p k)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1311.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Types
variable {K : Type} [Fintype K] [DecidableEq K]
noncomputable def inactiveLaw : FiniteLaw (Activation K) := FiniteLaw.dirac (∅,fun _ => false)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1312 : Prop where
  proof : (∀ {K : Type} [inst : DecidableEq K], (∀ (α : Finset K),
    activationPhi α (∅,fun _ => false)=if α=∅ then 1 else 0))

theorem inactivePhi [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1312] : (∀ {K : Type} [inst : DecidableEq K], (∀ (α : Finset K),
  activationPhi α (∅,fun _ => false)=if α=∅ then 1 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1312.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1313 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α : Finset K) (hα : α≠∅),
    inactiveLaw.mean (activationPhi α)=0))

theorem inactiveLaw_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1313] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α : Finset K) (hα : α≠∅),
  inactiveLaw.mean (activationPhi α)=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1313.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1314 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α β : Finset K),
    activationMoment inactiveLaw α β=if α=∅ ∧ β=∅ then 1 else 0))

theorem inactiveLaw_moment [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1314] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (α β : Finset K),
  activationMoment inactiveLaw α β=if α=∅ ∧ β=∅ then 1 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1314.proof certificateEvidence
end

noncomputable def thinnedLaw (p : FiniteLaw (Activation K)) (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) :=
  FiniteLaw.mixture p inactiveLaw lam hlam hlam1

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1315 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : FiniteLaw (Activation K)) (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0)
        (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) (α : Finset K) (hα : α≠∅),
    (thinnedLaw p lam hlam hlam1).mean (activationPhi α)=0))

theorem thinnedLaw_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1315] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : FiniteLaw (Activation K)) (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0)
      (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) (α : Finset K) (hα : α≠∅),
  (thinnedLaw p lam hlam hlam1).mean (activationPhi α)=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1315.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1316 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : FiniteLaw (Activation K)) (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1)
        (α β : Finset K) (hα : α≠∅),
    activationMoment (thinnedLaw p lam hlam hlam1) α β=lam*activationMoment p α β))

theorem thinnedLaw_active [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1316] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : FiniteLaw (Activation K)) (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1)
      (α β : Finset K) (hα : α≠∅),
  activationMoment (thinnedLaw p lam hlam hlam1) α β=lam*activationMoment p α β)) := @OAI.SidorenkoCounterexample.ProofCertificate_1316.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1317 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K)) (lam : ActCorner → ℝ)
        (hlam : ∀ k,0≤lam k) (hlam1 : ∀ k,lam k≤1),
    activeCoefficient (fun k => activationMoment (thinnedLaw (p k) (lam k) (hlam k) (hlam1 k)))=
          (∏ k,lam k)*activeCoefficient (fun k => activationMoment (p k))))

theorem activeCoefficient_scaling [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1317] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K)) (lam : ActCorner → ℝ)
      (hlam : ∀ k,0≤lam k) (hlam1 : ∀ k,lam k≤1),
  activeCoefficient (fun k => activationMoment (thinnedLaw (p k) (lam k) (hlam k) (hlam1 k)))=
        (∏ k,lam k)*activeCoefficient (fun k => activationMoment (p k)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1317.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1318 : Prop where
  proof : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K)) (k : ActCorner)
        (hk : p k=inactiveLaw),
    activeCoefficient (fun k => activationMoment (p k))=0))

theorem activeCoefficient_inactive [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1318] : (∀ {K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : ActCorner → FiniteLaw (Activation K)) (k : ActCorner)
      (hk : p k=inactiveLaw),
  activeCoefficient (fun k => activationMoment (p k))=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1318.proof certificateEvidence
end

end Types
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214]
noncomputable def basePairLaw (a : Fin 13) (b : Fin 22) : FiniteLaw (Activation ActCorner) :=
  if a=faceVertex b 0 then cornerLaw (b,0) else
    if a=faceVertex b 1 then cornerLaw (b,1) else
      if a=faceVertex b 2 then cornerLaw (b,2) else inactiveLaw
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1319 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner),
    basePairLaw (cornerPoint k) k.1=cornerLaw k))

theorem basePairLaw_corner [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1319] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (k : ActCorner),
  basePairLaw (cornerPoint k) k.1=cornerLaw k)) := @OAI.SidorenkoCounterexample.ProofCertificate_1319.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1320 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (a : Fin 13) (b : Fin 22) (α : Finset ActCorner) (hα : α≠∅),
    (basePairLaw a b).mean (activationPhi α)=0))

theorem basePairLaw_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1320] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (∀ (a : Fin 13) (b : Fin 22) (α : Finset ActCorner) (hα : α≠∅),
  (basePairLaw a b).mean (activationPhi α)=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1320.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1321 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (activeCoefficient (fun k => activationMoment (basePairLaw (cornerPoint k) k.1))= -(1/4:ℝ)^66))

theorem basePairLaw_identity [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1321] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1022] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0656] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_1025] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1214], (activeCoefficient (fun k => activationMoment (basePairLaw (cornerPoint k) k.1))= -(1/4:ℝ)^66)) := @OAI.SidorenkoCounterexample.ProofCertificate_1321.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1322 : Prop where
  proof : ((Function.Surjective cornerPoint))

theorem cornerPoint_surjective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1322] : ((Function.Surjective cornerPoint)) := @OAI.SidorenkoCounterexample.ProofCertificate_1322.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Typed
variable {A B K : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
noncomputable def typedCoefficient (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A) (b : Fin 22 → B) : ℝ :=
  activeCoefficient (fun k => activationMoment (p (a (cornerPoint k)) (b k.1)))

noncomputable def typeMapLaw (π : FiniteLaw A) (ν : FiniteLaw B) : FiniteLaw ((Fin 13 → A) × (Fin 22 → B)) :=
  (FiniteLaw.independent (fun _ => π)).prod (FiniteLaw.independent (fun _ => ν))

noncomputable def averagedCoefficient (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K)) : ℝ :=
  (typeMapLaw π ν).mean (fun ab => typedCoefficient p ab.1 ab.2)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1323 : Prop where
  proof : (∀ {A B K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : A → B → FiniteLaw (Activation K)) (lam : A → B → ℝ)
        (h0 : ∀ a b,0≤lam a b) (h1 : ∀ a b,lam a b≤1) (a : Fin 13 → A) (b : Fin 22 → B),
    typedCoefficient (fun a b => thinnedLaw (p a b) (lam a b) (h0 a b) (h1 a b)) a b=
          (∏ k : ActCorner,lam (a (cornerPoint k)) (b k.1))*typedCoefficient p a b))

theorem typedCoefficient_thinned [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1323] : (∀ {A B K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : A → B → FiniteLaw (Activation K)) (lam : A → B → ℝ)
      (h0 : ∀ a b,0≤lam a b) (h1 : ∀ a b,lam a b≤1) (a : Fin 13 → A) (b : Fin 22 → B),
  typedCoefficient (fun a b => thinnedLaw (p a b) (lam a b) (h0 a b) (h1 a b)) a b=
        (∏ k : ActCorner,lam (a (cornerPoint k)) (b k.1))*typedCoefficient p a b)) := @OAI.SidorenkoCounterexample.ProofCertificate_1323.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1324 : Prop where
  proof : (∀ {A B K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
        (b : Fin 22 → B) (i : Fin 13) (hi : ∀ j,p (a i) j=inactiveLaw),
    typedCoefficient p a b=0))

theorem typedCoefficient_inactive_left [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1324] : (∀ {A B K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
      (b : Fin 22 → B) (i : Fin 13) (hi : ∀ j,p (a i) j=inactiveLaw),
  typedCoefficient p a b=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1324.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1325 : Prop where
  proof : (∀ {A B K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
        (b : Fin 22 → B) (j : Fin 22) (hj : ∀ i,p i (b j)=inactiveLaw),
    typedCoefficient p a b=0))

theorem typedCoefficient_inactive_right [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1325] : (∀ {A B K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
      (b : Fin 22 → B) (j : Fin 22) (hj : ∀ i,p i (b j)=inactiveLaw),
  typedCoefficient p a b=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1325.proof certificateEvidence
end

end Typed
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Kernel
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
noncomputable def kernelMean (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  π.mean (fun x => ν.mean (W x))

noncomputable def bipartiteMoment (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  (FiniteLaw.independent (fun _ : Fin 13 => π)).mean (fun x =>
    (FiniteLaw.independent (fun _ : Fin 22 => ν)).mean (fun y =>
      ∏ k : ActCorner,W (x (cornerPoint k)) (y k.1)))

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1326 : Prop where
  proof : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ)
        (hW : ∀ x y,0≤W x y),
    0≤bipartiteMoment π ν W))

theorem bipartiteMoment_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1326] : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ)
      (hW : ∀ x y,0≤W x y),
  0≤bipartiteMoment π ν W)) := @OAI.SidorenkoCounterexample.ProofCertificate_1326.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1327 : Prop where
  proof : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) {W Z : X → Y → ℝ}
        (h : ∀ x y,W x y=Z x y),
    bipartiteMoment π ν W=bipartiteMoment π ν Z))

theorem bipartiteMoment_congr [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1327] : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) {W Z : X → Y → ℝ}
      (h : ∀ x y,W x y=Z x y),
  bipartiteMoment π ν W=bipartiteMoment π ν Z)) := @OAI.SidorenkoCounterexample.ProofCertificate_1327.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1328 : Prop where
  proof : (∀ {X Y A B : Type} [inst : Fintype X] [inst : Fintype Y] [inst : Fintype A] [inst : Fintype B], (∀ (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
        (W : A × X → B × Y → ℝ),
    bipartiteMoment (π.prod σ) (ν.prod τ) W=
          (typeMapLaw π ν).mean (fun ab => (FiniteLaw.independent (fun _ : Fin 13 => σ)).mean (fun x =>
            (FiniteLaw.independent (fun _ : Fin 22 => τ)).mean (fun y =>
              ∏ k : ActCorner,W (ab.1 (cornerPoint k),x (cornerPoint k)) (ab.2 k.1,y k.1))))))

theorem bipartiteMoment_typed [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1328] : (∀ {X Y A B : Type} [inst : Fintype X] [inst : Fintype Y] [inst : Fintype A] [inst : Fintype B], (∀ (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
      (W : A × X → B × Y → ℝ),
  bipartiteMoment (π.prod σ) (ν.prod τ) W=
        (typeMapLaw π ν).mean (fun ab => (FiniteLaw.independent (fun _ : Fin 13 => σ)).mean (fun x =>
          (FiniteLaw.independent (fun _ : Fin 22 => τ)).mean (fun y =>
            ∏ k : ActCorner,W (ab.1 (cornerPoint k),x (cornerPoint k)) (ab.2 k.1,y k.1)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1328.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1329 : Prop where
  proof : (∀ {X Y A B : Type} [inst : Fintype X] [inst : Fintype Y] [inst : Fintype A] [inst : Fintype B], (∀ (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
        (W : A × X → B × Y → ℝ),
    kernelMean (π.prod σ) (ν.prod τ) W=
          π.mean (fun a => ν.mean (fun b => σ.mean (fun x => τ.mean (fun y => W (a,x) (b,y)))))))

theorem kernelMean_prod [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1329] : (∀ {X Y A B : Type} [inst : Fintype X] [inst : Fintype Y] [inst : Fintype A] [inst : Fintype B], (∀ (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
      (W : A × X → B × Y → ℝ),
  kernelMean (π.prod σ) (ν.prod τ) W=
        π.mean (fun a => ν.mean (fun b => σ.mean (fun x => τ.mean (fun y => W (a,x) (b,y))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1329.proof certificateEvidence
end

end Kernel
namespace FiniteLaw
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1330 : Prop where
  proof : ((∀ {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
        (f : (I → A) → ℝ),
    (independent (fun _ : I => (uniform : FiniteLaw A))).mean f=uniformMean f))

theorem independent_uniform_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1330] : ((∀ {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
      (f : (I → A) → ℝ),
  (independent (fun _ : I => (uniform : FiniteLaw A))).mean f=uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1330.proof certificateEvidence
end

end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section MatrixMean
variable {F K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1331 : Prop where
  proof : ((∀ {A : Type} [AddGroup A] [Fintype A] (y : A) (f : A → ℝ),
    uniformMean (fun x => f (x-y))=uniformMean f))

theorem uniformMean_sub_right [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1331] : ((∀ {A : Type} [AddGroup A] [Fintype A] (y : A) (f : A → ℝ),
  uniformMean (fun x => f (x-y))=uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1331.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1332 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
        (z : Activation K) (y : K → SymMatrix F (2*r)),
    uniformMean (fun x => sampleMatrixKernel r z x y)=1))

theorem sampleMatrixKernel_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1332] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
      (z : Activation K) (y : K → SymMatrix F (2*r)),
  uniformMean (fun x => sampleMatrixKernel r z x y)=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1332.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1333 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
        (p : FiniteLaw (Activation K)) (y : K → SymMatrix F (2*r)),
    uniformMean (fun x => activationMatrixKernel r p x y)=1))

theorem activationMatrixKernel_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1333] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
      (p : FiniteLaw (Activation K)) (y : K → SymMatrix F (2*r)),
  uniformMean (fun x => activationMatrixKernel r p x y)=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1333.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1334 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (z : Activation K) (x y : K → SymMatrix F (2*(2*r))),
    sampleMatrixKernel (2*r) z x y=sampleMatrixKernel (2*r) z y x))

theorem sampleMatrixKernel_symm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1334] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (z : Activation K) (x y : K → SymMatrix F (2*(2*r))),
  sampleMatrixKernel (2*r) z x y=sampleMatrixKernel (2*r) z y x)) := @OAI.SidorenkoCounterexample.ProofCertificate_1334.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1335 : Prop where
  proof : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (r : ℕ) (p : FiniteLaw (Activation K)) (x y : K → SymMatrix F (2*(2*r))),
    activationMatrixKernel (2*r) p x y=activationMatrixKernel (2*r) p y x))

theorem activationMatrixKernel_symm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1335] : (∀ {F K : Type} [inst : Field F] [inst : Fintype F] [inst : DecidableEq F] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (r : ℕ) (p : FiniteLaw (Activation K)) (x y : K → SymMatrix F (2*(2*r))),
  activationMatrixKernel (2*r) p x y=activationMatrixKernel (2*r) p y x)) := @OAI.SidorenkoCounterexample.ProofCertificate_1335.proof certificateEvidence
end

end MatrixMean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section TypedMatrix
variable {A B K F : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
  [Field F] [Fintype F] [DecidableEq F]
noncomputable def typedMatrixLaw (r : ℕ) (π : FiniteLaw A) : FiniteLaw (A × (K → SymMatrix F (2*r))) :=
  π.prod FiniteLaw.uniform

noncomputable def typedMatrixKernel (r : ℕ) (p : A → B → FiniteLaw (Activation K))
    (x : A × (K → SymMatrix F (2*r))) (y : B × (K → SymMatrix F (2*r))) : ℝ :=
  activationMatrixKernel r (p x.1 y.1) x.2 y.2

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1336 : Prop where
  proof : (∀ {A B K F : Type} [inst : Fintype K] [inst : DecidableEq K] [inst : Field F] [inst : Fintype F] [inst : DecidableEq F],
      (∀ (r : ℕ) (p : A → B → FiniteLaw (Activation K))
        (x : A × (K → SymMatrix F (2*r))) (y : B × (K → SymMatrix F (2*r))),
    0≤typedMatrixKernel r p x y))

theorem typedMatrixKernel_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1336] : (∀ {A B K F : Type} [inst : Fintype K] [inst : DecidableEq K] [inst : Field F] [inst : Fintype F] [inst : DecidableEq F],
    (∀ (r : ℕ) (p : A → B → FiniteLaw (Activation K))
      (x : A × (K → SymMatrix F (2*r))) (y : B × (K → SymMatrix F (2*r))),
  0≤typedMatrixKernel r p x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_1336.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1337 : Prop where
  proof : (∀ {A B K F : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype K] [inst : DecidableEq K] [inst : Field F]
      [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (π : FiniteLaw A) (ν : FiniteLaw B)
        (p : A → B → FiniteLaw (Activation K)),
    bipartiteMoment (typedMatrixLaw (F := F) (K := K) r π) (typedMatrixLaw r ν) (typedMatrixKernel r p)=
          (typeMapLaw π ν).mean (fun ab => conditionalMatrixMoment (F := F) r (fun k => p (ab.1 (cornerPoint k)) (ab.2 k.1)))))

theorem typedMatrixKernel_moment [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1337] : (∀ {A B K F : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype K] [inst : DecidableEq K] [inst : Field F]
    [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (π : FiniteLaw A) (ν : FiniteLaw B)
      (p : A → B → FiniteLaw (Activation K)),
  bipartiteMoment (typedMatrixLaw (F := F) (K := K) r π) (typedMatrixLaw r ν) (typedMatrixKernel r p)=
        (typeMapLaw π ν).mean (fun ab => conditionalMatrixMoment (F := F) r (fun k => p (ab.1 (cornerPoint k)) (ab.2 k.1))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1337.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1338 : Prop where
  proof : (∀ {A B K F : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype K] [inst : DecidableEq K] [inst : Field F]
      [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
        (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K)),
    kernelMean (typedMatrixLaw (F := F) (K := K) r π) (typedMatrixLaw r ν) (typedMatrixKernel r p)=1))

theorem typedMatrixKernel_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1338] : (∀ {A B K F : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype K] [inst : DecidableEq K] [inst : Field F]
    [inst : Fintype F] [inst : DecidableEq F], (∀ (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
      (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K)),
  kernelMean (typedMatrixLaw (F := F) (K := K) r π) (typedMatrixLaw r ν) (typedMatrixKernel r p)=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1338.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1339 : Prop where
  proof : (∀ {A B K F : Type} [inst : Fintype K] [inst : DecidableEq K] [inst : Field F] [inst : Fintype F] [inst : DecidableEq F],
      (∀ (r : ℕ) (p : A → B → FiniteLaw (Activation K))
        (x : A × (K → SymMatrix F (2*(2*r)))) (y : B × (K → SymMatrix F (2*(2*r)))),
    typedMatrixKernel (2*r) p x y=typedMatrixKernel (2*r) (fun b a => p a b) y x))

theorem typedMatrixKernel_transpose [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1339] : (∀ {A B K F : Type} [inst : Fintype K] [inst : DecidableEq K] [inst : Field F] [inst : Fintype F] [inst : DecidableEq F],
    (∀ (r : ℕ) (p : A → B → FiniteLaw (Activation K))
      (x : A × (K → SymMatrix F (2*(2*r)))) (y : B × (K → SymMatrix F (2*(2*r)))),
  typedMatrixKernel (2*r) p x y=typedMatrixKernel (2*r) (fun b a => p a b) y x)) := @OAI.SidorenkoCounterexample.ProofCertificate_1339.proof certificateEvidence
end

end TypedMatrix
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1340 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ {A B K : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
        (r : ℕ) (hl : singularTailThreshold≤2*(2*r)) (π : FiniteLaw A) (ν : FiniteLaw B)
        (p : A → B → FiniteLaw (Activation K))
        (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0),
    Tendsto (fun q : OddPrime => bipartiteMoment
          (typedMatrixLaw (F := ZMod q.val) (K := K) (2*r) π) (typedMatrixLaw (2*r) ν) (typedMatrixKernel (2*r) p))
          primeInfinity (nhds (1+averagedCoefficient π ν p))))

theorem typedMatrixKernel_tendsto [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1340] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ {A B K : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
      (r : ℕ) (hl : singularTailThreshold≤2*(2*r)) (π : FiniteLaw A) (ν : FiniteLaw B)
      (p : A → B → FiniteLaw (Activation K))
      (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0),
  Tendsto (fun q : OddPrime => bipartiteMoment
        (typedMatrixLaw (F := ZMod q.val) (K := K) (2*r) π) (typedMatrixLaw (2*r) ν) (typedMatrixKernel (2*r) p))
        primeInfinity (nhds (1+averagedCoefficient π ν p)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1340.proof certificateEvidence
end

end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]
noncomputable def diluted (p : FiniteLaw A) (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) : FiniteLaw (Option A) where
  weight x := match x with | none => 1-ε | some a => ε*p.weight a
  nonneg x := by cases x with | none => exact sub_nonneg.mpr h1 | some a => exact mul_nonneg h0 (p.nonneg a)
  total := by rw [Fintype.sum_option,←Finset.mul_sum,p.total]; ring

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1341 : Prop where
  proof : (∀ {A I : Type}, (Function.Injective (fun a : I → A => fun i => some (a i))))

theorem someFunction_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1341] : (∀ {A I : Type}, (Function.Injective (fun a : I → A => fun i => some (a i)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1341.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1342 : Prop where
  proof : (∀ {A I : Type} [inst : Fintype I], (∀ (z : I → Option A) (hz : ∀ a : I → A,(fun i => some (a i))≠z),
    ∃ i,z i=none))

theorem exists_none_of_not_some [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1342] : (∀ {A I : Type} [inst : Fintype I], (∀ (z : I → Option A) (hz : ∀ a : I → A,(fun i => some (a i))≠z),
  ∃ i,z i=none)) := @OAI.SidorenkoCounterexample.ProofCertificate_1342.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1343 : Prop where
  proof : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I] [inst : DecidableEq I], (∀ (p : FiniteLaw A) (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1)
        (f : (I → Option A) → ℝ) (hf : ∀ z,(∃ i,z i=none) → f z=0),
    (independent (fun _ : I => p.diluted ε h0 h1)).mean f=
          ε^Fintype.card I*(independent (fun _ : I => p)).mean (fun a => f (fun i => some (a i)))))

theorem diluted_independent_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1343] : (∀ {A I : Type} [inst : Fintype A] [inst : Fintype I] [inst : DecidableEq I], (∀ (p : FiniteLaw A) (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1)
      (f : (I → Option A) → ℝ) (hf : ∀ z,(∃ i,z i=none) → f z=0),
  (independent (fun _ : I => p.diluted ε h0 h1)).mean f=
        ε^Fintype.card I*(independent (fun _ : I => p)).mean (fun a => f (fun i => some (a i))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1343.proof certificateEvidence
end

end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Dilution
variable {A B K : Type} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
noncomputable def dilutedPairLaw (p : A → B → FiniteLaw (Activation K)) : Option A → B → FiniteLaw (Activation K)
  | none,_ => inactiveLaw
  | some a,b => p a b

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1344 : Prop where
  proof : (∀ {A B K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : A → B → FiniteLaw (Activation K))
        (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0),
    ∀ a b α,α≠∅ → (dilutedPairLaw p a b).mean (activationPhi α)=0))

theorem dilutedPairLaw_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1344] : (∀ {A B K : Type} [inst : Fintype K] [inst : DecidableEq K], (∀ (p : A → B → FiniteLaw (Activation K))
      (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0),
  ∀ a b α,α≠∅ → (dilutedPairLaw p a b).mean (activationPhi α)=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1344.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1345 : Prop where
  proof : (∀ {A B K : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype K] [inst : DecidableEq K], (∀ (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
        (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1),
    averagedCoefficient (π.diluted ε h0 h1) ν (dilutedPairLaw p)=ε^13*averagedCoefficient π ν p))

theorem coefficient_dilution_left [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1345] : (∀ {A B K : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype K] [inst : DecidableEq K], (∀ (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
      (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1),
  averagedCoefficient (π.diluted ε h0 h1) ν (dilutedPairLaw p)=ε^13*averagedCoefficient π ν p)) := @OAI.SidorenkoCounterexample.ProofCertificate_1345.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1346 : Prop where
  proof : (∀ {A B K : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype K] [inst : DecidableEq K], (∀ (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
        (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1),
    averagedCoefficient ν (π.diluted ε h0 h1) (fun b a => dilutedPairLaw p a b)=
          ε^22*averagedCoefficient ν π (fun b a => p a b)))

theorem coefficient_dilution_right [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1346] : (∀ {A B K : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype K] [inst : DecidableEq K], (∀ (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
      (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1),
  averagedCoefficient ν (π.diluted ε h0 h1) (fun b a => dilutedPairLaw p a b)=
        ε^22*averagedCoefficient ν π (fun b a => p a b))) := @OAI.SidorenkoCounterexample.ProofCertificate_1346.proof certificateEvidence
end

end Dilution
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1347 : Prop where
  proof : ((∀ (t0 t1 : ℝ) (hneg : t0<0),
    ∃ ε : ℝ,0<ε ∧ ε<1 ∧ (1+ε^13*t0)*(1+ε^22*t1)<1))

theorem exists_dilution_gap [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1347] : ((∀ (t0 t1 : ℝ) (hneg : t0<0),
  ∃ ε : ℝ,0<ε ∧ ε<1 ∧ (1+ε^13*t0)*(1+ε^22*t1)<1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1347.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section PinningRound
variable {I J E C : Type} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
end PinningRound
end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Mix
variable {A : Type} [Fintype A]
end Mix
section Pin
variable {I J E C : Type} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
end Pin
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Weights
variable {A I : Type} [Fintype A] [Nonempty A] [Fintype I]
noncomputable def exponentialNormalizer (s : A → ℝ) (ρ : ℝ) : ℝ := ∑ a,Real.exp (ρ*s a)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1348 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A] [inst : Nonempty A], (∀ (s : A → ℝ) (ρ : ℝ),
    0<exponentialNormalizer s ρ))

theorem exponentialNormalizer_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1348] : (∀ {A : Type} [inst : Fintype A] [inst : Nonempty A], (∀ (s : A → ℝ) (ρ : ℝ),
  0<exponentialNormalizer s ρ)) := @OAI.SidorenkoCounterexample.ProofCertificate_1348.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1348]
noncomputable def exponentialPrior (s : A → ℝ) (ρ : ℝ) : FiniteLaw A where
  weight a := Real.exp (ρ*s a)/exponentialNormalizer s ρ
  nonneg _ := div_nonneg (Real.exp_pos _).le (exponentialNormalizer_pos s ρ).le
  total := by rw [←Finset.sum_div]; exact div_self (ne_of_gt (exponentialNormalizer_pos s ρ))
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1349 : Prop where
  proof : (∀ {I : Type} [inst : Fintype I], (∀ (ρ : ℝ) (s : I → ℝ),
    (∏ i,Real.exp (ρ*s i))=Real.exp (ρ*∑ i,s i)))

theorem prod_exp_weight [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1349] : (∀ {I : Type} [inst : Fintype I], (∀ (ρ : ℝ) (s : I → ℝ),
  (∏ i,Real.exp (ρ*s i))=Real.exp (ρ*∑ i,s i))) := @OAI.SidorenkoCounterexample.ProofCertificate_1349.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1350 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1348] {A I : Type} [inst : Fintype A] [inst : Nonempty A]
      [inst : Fintype I], (∀ (s : A → ℝ) (ρ : ℝ) (a : I → A),
    (∏ i,(exponentialPrior s ρ).weight (a i))=
          Real.exp (ρ*∑ i,s (a i))/(exponentialNormalizer s ρ)^Fintype.card I))

theorem exponentialPrior_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1350] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1348] {A I : Type} [inst : Fintype A] [inst : Nonempty A]
    [inst : Fintype I], (∀ (s : A → ℝ) (ρ : ℝ) (a : I → A),
  (∏ i,(exponentialPrior s ρ).weight (a i))=
        Real.exp (ρ*∑ i,s (a i))/(exponentialNormalizer s ρ)^Fintype.card I)) := @OAI.SidorenkoCounterexample.ProofCertificate_1350.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1351 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀),
    Tendsto (fun ρ : ℝ => ∑ a,c a*Real.exp (ρ*(s a-s a₀))) atTop (nhds (c a₀))))

theorem exponential_dominant_limit [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1351] : (∀ {A : Type} [inst : Fintype A], (∀ (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀),
  Tendsto (fun ρ : ℝ => ∑ a,c a*Real.exp (ρ*(s a-s a₀))) atTop (nhds (c a₀)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1351.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1352 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀)
        (hc : c a₀<0),
    ∃ ρ : ℝ,0<ρ ∧ (∑ a,c a*Real.exp (ρ*s a))<0))

theorem exponential_dominant_negative [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1352] : (∀ {A : Type} [inst : Fintype A], (∀ (s c : A → ℝ) (a₀ : A) (hs : ∀ a,a≠a₀ → s a<s a₀)
      (hc : c a₀<0),
  ∃ ρ : ℝ,0<ρ ∧ (∑ a,c a*Real.exp (ρ*s a))<0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1352.proof certificateEvidence
end

end Weights
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Gibbs
variable {I J E : Type} [Fintype I] [Fintype J] [Fintype E] [Nonempty I] [Nonempty J]
noncomputable def gibbsThinning (s : VertexPairScores I J) (ρ M : ℝ) (a : I) (b : J) : ℝ :=
  Real.exp (ρ*(s.pair a b-M))

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1353 : Prop where
  proof : (∀ {I J : Type}, (∀ (s : VertexPairScores I J) (ρ M : ℝ) (a : I) (b : J),
    0<gibbsThinning s ρ M a b))

theorem gibbsThinning_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1353] : (∀ {I J : Type}, (∀ (s : VertexPairScores I J) (ρ M : ℝ) (a : I) (b : J),
  0<gibbsThinning s ρ M a b)) := @OAI.SidorenkoCounterexample.ProofCertificate_1353.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1354 : Prop where
  proof : (∀ {I J : Type}, (∀ (s : VertexPairScores I J) (ρ M : ℝ) (hρ : 0≤ρ)
        (hM : ∀ a b,s.pair a b≤M) (a : I) (b : J),
    gibbsThinning s ρ M a b≤1))

theorem gibbsThinning_le_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1354] : (∀ {I J : Type}, (∀ (s : VertexPairScores I J) (ρ M : ℝ) (hρ : 0≤ρ)
      (hM : ∀ a b,s.pair a b≤M) (a : I) (b : J),
  gibbsThinning s ρ M a b≤1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1354.proof certificateEvidence
end

noncomputable def gibbsPrefactor (s : VertexPairScores I J) (ρ M : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-ρ*(n:ℝ)*M)/((exponentialNormalizer s.left ρ)^Fintype.card I*(exponentialNormalizer s.right ρ)^Fintype.card J)

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1355 : Prop where
  proof : (∀ {I J : Type} [inst : Fintype I] [inst : Fintype J] [inst : Nonempty I] [inst : Nonempty J], (∀ (s : VertexPairScores I J) (ρ M : ℝ) (n : ℕ),
    0<gibbsPrefactor s ρ M n))

theorem gibbsPrefactor_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1355] : (∀ {I J : Type} [inst : Fintype I] [inst : Fintype J] [inst : Nonempty I] [inst : Nonempty J], (∀ (s : VertexPairScores I J) (ρ M : ℝ) (n : ℕ),
  0<gibbsPrefactor s ρ M n)) := @OAI.SidorenkoCounterexample.ProofCertificate_1355.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1356 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1348] {I J E : Type} [inst : Fintype I] [inst : Fintype J]
      [inst : Fintype E] [inst : Nonempty I] [inst : Nonempty J], (∀ (s : VertexPairScores I J) (ρ M : ℝ) (t : E → I) (h : E → J)
        (a : I → I) (b : J → J),
    (∏ i,(exponentialPrior s.left ρ).weight (a i))*(∏ j,(exponentialPrior s.right ρ).weight (b j))*
            (∏ e,gibbsThinning s ρ M (a (t e)) (b (h e)))=
          gibbsPrefactor s ρ M (Fintype.card E)*Real.exp (ρ*s.score t h a b)))

theorem gibbs_weight_formula [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1356] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1348] {I J E : Type} [inst : Fintype I] [inst : Fintype J]
    [inst : Fintype E] [inst : Nonempty I] [inst : Nonempty J], (∀ (s : VertexPairScores I J) (ρ M : ℝ) (t : E → I) (h : E → J)
      (a : I → I) (b : J → J),
  (∏ i,(exponentialPrior s.left ρ).weight (a i))*(∏ j,(exponentialPrior s.right ρ).weight (b j))*
          (∏ e,gibbsThinning s ρ M (a (t e)) (b (h e)))=
        gibbsPrefactor s ρ M (Fintype.card E)*Real.exp (ρ*s.score t h a b))) := @OAI.SidorenkoCounterexample.ProofCertificate_1356.proof certificateEvidence
end

end Gibbs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1357 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1348] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_1022]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0657] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0659] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1025]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1144] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_1214],
      (∀ (s : VertexPairScores (Fin 13) (Fin 22)) (ρ M : ℝ)
        (h0 : ∀ a b,0≤gibbsThinning s ρ M a b) (h1 : ∀ a b,gibbsThinning s ρ M a b≤1),
    averagedCoefficient (exponentialPrior s.left ρ) (exponentialPrior s.right ρ)
          (fun a b => thinnedLaw (basePairLaw a b) (gibbsThinning s ρ M a b) (h0 a b) (h1 a b))=
          gibbsPrefactor s ρ M 66*(∑ m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22),
            typedCoefficient basePairLaw m.1 m.2*Real.exp (ρ*s.score cornerPoint (fun k : ActCorner => k.1) m.1 m.2))))

theorem averagedCoefficient_gibbs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1357] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_1348] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_1022]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0657] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0659] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_1025]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_1144] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_1214],
    (∀ (s : VertexPairScores (Fin 13) (Fin 22)) (ρ M : ℝ)
      (h0 : ∀ a b,0≤gibbsThinning s ρ M a b) (h1 : ∀ a b,gibbsThinning s ρ M a b≤1),
  averagedCoefficient (exponentialPrior s.left ρ) (exponentialPrior s.right ρ)
        (fun a b => thinnedLaw (basePairLaw a b) (gibbsThinning s ρ M a b) (h0 a b) (h1 a b))=
        gibbsPrefactor s ρ M 66*(∑ m : (Fin 13 → Fin 13) × (Fin 22 → Fin 22),
          typedCoefficient basePairLaw m.1 m.2*Real.exp (ρ*s.score cornerPoint (fun k : ActCorner => k.1) m.1 m.2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1357.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1358 : Prop where
  proof : ((∃ (π : FiniteLaw (Fin 13)) (ν : FiniteLaw (Fin 22))
        (p : Fin 13 → Fin 22 → FiniteLaw (Activation ActCorner)),
        (∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) ∧ averagedCoefficient π ν p<0))

theorem exists_negative_coefficient [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1358] : ((∃ (π : FiniteLaw (Fin 13)) (ν : FiniteLaw (Fin 22))
      (p : Fin 13 → Fin 22 → FiniteLaw (Activation ActCorner)),
      (∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) ∧ averagedCoefficient π ν p<0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1358.proof certificateEvidence
end

end SidorenkoCounterexample
end
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
structure OrientedKernel where
  X : Type
  Y : Type
  [finiteX : Fintype X]
  [finiteY : Fintype Y]
  [nonemptyX : Nonempty X]
  [nonemptyY : Nonempty Y]
  left : FiniteLaw X
  right : FiniteLaw Y
  value : X → Y → ℝ
  nonneg : ∀ x y,0≤value x y
  mean_one : kernelMean left right value=1
  gap : bipartiteMoment left right value*bipartiteMoment right left (fun y x => value x y)<1

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1359 : Prop where
  proof : ((Nonempty OrientedKernel))

theorem exists_oriented_kernel [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1359] : ((Nonempty OrientedKernel)) := @OAI.SidorenkoCounterexample.ProofCertificate_1359.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Cross
variable {A B C D X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X] [Fintype Y]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1360 : Prop where
  proof : (∀ {A B C D : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype C] [inst : Fintype D], (∀ (p : FiniteLaw A) (q : FiniteLaw B) (r : FiniteLaw C) (s : FiniteLaw D)
        (f : A → D → ℝ) (g : C → B → ℝ),
    p.mean (fun a => q.mean (fun b => r.mean (fun c => s.mean (fun d => f a d*g c b))))=
          p.mean (fun a => s.mean (f a))*r.mean (fun c => q.mean (g c))))

theorem four_means_factor [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1360] : (∀ {A B C D : Type} [inst : Fintype A] [inst : Fintype B] [inst : Fintype C] [inst : Fintype D], (∀ (p : FiniteLaw A) (q : FiniteLaw B) (r : FiniteLaw C) (s : FiniteLaw D)
      (f : A → D → ℝ) (g : C → B → ℝ),
  p.mean (fun a => q.mean (fun b => r.mean (fun c => s.mean (fun d => f a d*g c b))))=
        p.mean (fun a => s.mean (f a))*r.mean (fun c => q.mean (g c)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1360.proof certificateEvidence
end

noncomputable def crossedKernel (W : X → Y → ℝ) (x y : X × Y) : ℝ := W x.1 y.2*W y.1 x.2

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1361 : Prop where
  proof : (∀ {X Y : Type}, (∀ (W : X → Y → ℝ) (x y : X × Y),
    crossedKernel W x y=crossedKernel W y x))

theorem crossedKernel_symm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1361] : (∀ {X Y : Type}, (∀ (W : X → Y → ℝ) (x y : X × Y),
  crossedKernel W x y=crossedKernel W y x)) := @OAI.SidorenkoCounterexample.ProofCertificate_1361.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1362 : Prop where
  proof : (∀ {X Y : Type}, (∀ (W : X → Y → ℝ) (hW : ∀ x y,0≤W x y) (x y : X × Y),
    0≤crossedKernel W x y))

theorem crossedKernel_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1362] : (∀ {X Y : Type}, (∀ (W : X → Y → ℝ) (hW : ∀ x y,0≤W x y) (x y : X × Y),
  0≤crossedKernel W x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_1362.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1363 : Prop where
  proof : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ),
    kernelMean (π.prod ν) (π.prod ν) (crossedKernel W)=(kernelMean π ν W)^2))

theorem crossedKernel_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1363] : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ),
  kernelMean (π.prod ν) (π.prod ν) (crossedKernel W)=(kernelMean π ν W)^2)) := @OAI.SidorenkoCounterexample.ProofCertificate_1363.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1364 : Prop where
  proof : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ),
    bipartiteMoment (π.prod ν) (π.prod ν) (crossedKernel W)=
          bipartiteMoment π ν W*bipartiteMoment ν π (fun y x => W x y)))

theorem crossedKernel_moment [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1364] : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ),
  bipartiteMoment (π.prod ν) (π.prod ν) (crossedKernel W)=
        bipartiteMoment π ν W*bipartiteMoment ν π (fun y x => W x y))) := @OAI.SidorenkoCounterexample.ProofCertificate_1364.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1365 : Prop where
  proof : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) (c : ℝ),
    kernelMean π ν (fun x y => W x y/c)=kernelMean π ν W/c))

theorem kernelMean_div [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1365] : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) (c : ℝ),
  kernelMean π ν (fun x y => W x y/c)=kernelMean π ν W/c)) := @OAI.SidorenkoCounterexample.ProofCertificate_1365.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1366 : Prop where
  proof : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) (c : ℝ),
    bipartiteMoment π ν (fun x y => W x y/c)=bipartiteMoment π ν W/c^66))

theorem bipartiteMoment_div [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1366] : (∀ {X Y : Type} [inst : Fintype X] [inst : Fintype Y], (∀ (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) (c : ℝ),
  bipartiteMoment π ν (fun x y => W x y/c)=bipartiteMoment π ν W/c^66)) := @OAI.SidorenkoCounterexample.ProofCertificate_1366.proof certificateEvidence
end

end Cross
structure SymmetricCounterKernel where
  Ω : Type
  [finite : Fintype Ω]
  [nonempty : Nonempty Ω]
  law : FiniteLaw Ω
  value : Ω → Ω → ℝ
  nonneg : ∀ x y,0≤value x y
  le_one : ∀ x y,value x y≤1
  symm : ∀ x y,value x y=value y x
  mean_pos : 0<kernelMean law law value
  gap : bipartiteMoment law law value<(kernelMean law law value)^66

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1367 : Prop where
  proof : ((Nonempty SymmetricCounterKernel))

theorem exists_symmetric_kernel [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1367] : ((Nonempty SymmetricCounterKernel)) := @OAI.SidorenkoCounterexample.ProofCertificate_1367.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
section Marginal
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1368 : Prop where
  proof : (∀ {I J A : Type} [inst : Fintype I] [inst : Fintype J] [inst : Fintype A] [inst : DecidableEq I] [inst : DecidableEq J],
      (∀ (p : I ⊕ J → FiniteLaw A) (f : (I ⊕ J → A) → ℝ),
    (independent p).mean f=(independent (fun i => p (.inl i))).mean (fun x =>
          (independent (fun j => p (.inr j))).mean (fun y => f (Sum.elim x y)))))

theorem independent_mean_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1368] : (∀ {I J A : Type} [inst : Fintype I] [inst : Fintype J] [inst : Fintype A] [inst : DecidableEq I] [inst : DecidableEq J],
    (∀ (p : I ⊕ J → FiniteLaw A) (f : (I ⊕ J → A) → ℝ),
  (independent p).mean f=(independent (fun i => p (.inl i))).mean (fun x =>
        (independent (fun j => p (.inr j))).mean (fun y => f (Sum.elim x y))))) := @OAI.SidorenkoCounterexample.ProofCertificate_1368.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1369 : Prop where
  proof : (∀ {I J A : Type} [inst : Fintype I] [inst : Fintype J] [inst : Fintype A] [inst : DecidableEq I] [inst : DecidableEq J],
      (∀ (p : J → FiniteLaw A) (e : I → J) (he : Function.Injective e)
        (f : (I → A) → ℝ),
    (independent p).mean (fun x => f (fun i => x (e i)))=(independent (fun i => p (e i))).mean f))

theorem independent_mean_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1369] : (∀ {I J A : Type} [inst : Fintype I] [inst : Fintype J] [inst : Fintype A] [inst : DecidableEq I] [inst : DecidableEq J],
    (∀ (p : J → FiniteLaw A) (e : I → J) (he : Function.Injective e)
      (f : (I → A) → ℝ),
  (independent p).mean (fun x => f (fun i => x (e i)))=(independent (fun i => p (e i))).mean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1369.proof certificateEvidence
end

noncomputable def bind (p : FiniteLaw A) (q : A → FiniteLaw B) : FiniteLaw B where
  weight b := ∑ a,p.weight a*(q a).weight b
  nonneg b := Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) ((q a).nonneg b))
  total := by rw [Finset.sum_comm]; simp_rw [←Finset.mul_sum,(q _).total,mul_one]; exact p.total

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1370 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (q : A → FiniteLaw B) (f : B → ℝ),
    (p.bind q).mean f=p.mean (fun a => (q a).mean f)))

theorem mean_bind [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1370] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (p : FiniteLaw A) (q : A → FiniteLaw B) (f : B → ℝ),
  (p.bind q).mean f=p.mean (fun a => (q a).mean f))) := @OAI.SidorenkoCounterexample.ProofCertificate_1370.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1371 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f : A → ℝ) (hf : ∀ a,0≤f a) (n : ℕ),
    (p.mean f)^n≤p.mean (fun a => (f a)^n)))

theorem mean_pow_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1371] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) (f : A → ℝ) (hf : ∀ a,0≤f a) (n : ℕ),
  (p.mean f)^n≤p.mean (fun a => (f a)^n))) := @OAI.SidorenkoCounterexample.ProofCertificate_1371.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1372 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f g : A → ℝ} (h : p.mean f<p.mean g),
    ∃ a,f a<g a))

theorem exists_lt_of_mean_lt [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1372] : (∀ {A : Type} [inst : Fintype A], (∀ (p : FiniteLaw A) {f g : A → ℝ} (h : p.mean f<p.mean g),
  ∃ a,f a<g a)) := @OAI.SidorenkoCounterexample.ProofCertificate_1372.proof certificateEvidence
end

end Marginal
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
noncomputable def edgeIndicator {V : Type} (G : SimpleGraph V) (a b : V) : ℝ := if G.Adj a b then 1 else 0

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1373 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V) (a b : V),
    0≤edgeIndicator G a b))

theorem edgeIndicator_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1373] : ((∀ {V : Type} (G : SimpleGraph V) (a b : V),
  0≤edgeIndicator G a b)) := @OAI.SidorenkoCounterexample.ProofCertificate_1373.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1374 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V) (a b : V),
    edgeIndicator G a b≤1))

theorem edgeIndicator_le_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1374] : ((∀ {V : Type} (G : SimpleGraph V) (a b : V),
  edgeIndicator G a b≤1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1374.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1375 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V) (a b : V),
    edgeIndicator G a b=edgeIndicator G b a))

theorem edgeIndicator_symm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1375] : ((∀ {V : Type} (G : SimpleGraph V) (a b : V),
  edgeIndicator G a b=edgeIndicator G b a)) := @OAI.SidorenkoCounterexample.ProofCertificate_1375.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1376 : Prop where
  proof : ((∀ (j : Fin 22) (i : Fin 13),
    i∈faces j ↔ ∃ r,faceVertex j r=i))

theorem mem_faces_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1376] : ((∀ (j : Fin 22) (i : Fin 13),
  i∈faces j ↔ ∃ r,faceVertex j r=i)) := @OAI.SidorenkoCounterexample.ProofCertificate_1376.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1377 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V) (f : PatternVertex → V),
    (∀ u v,H.Adj u v → G.Adj (f u) (f v)) ↔
          ∀ k : ActCorner,G.Adj (f (.inl (cornerPoint k))) (f (.inr k.1))))

theorem hom_iff_corners [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1377] : ((∀ {V : Type} (G : SimpleGraph V) (f : PatternVertex → V),
  (∀ u v,H.Adj u v → G.Adj (f u) (f v)) ↔
        ∀ k : ActCorner,G.Adj (f (.inl (cornerPoint k))) (f (.inr k.1)))) := @OAI.SidorenkoCounterexample.ProofCertificate_1377.proof certificateEvidence
end

noncomputable def homIndicator {V : Type} (G : SimpleGraph V) (f : PatternVertex → V) : ℝ :=
  ∏ k : ActCorner,edgeIndicator G (f (.inl (cornerPoint k))) (f (.inr k.1))

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1378 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V) (f : PatternVertex → V),
    homIndicator G f=if ∀ u v,H.Adj u v → G.Adj (f u) (f v) then 1 else 0))

theorem homIndicator_eq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1378] : ((∀ {V : Type} (G : SimpleGraph V) (f : PatternVertex → V),
  homIndicator G f=if ∀ u v,H.Adj u v → G.Adj (f u) (f v) then 1 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1378.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1379 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V) (f : PatternVertex → V),
    0≤homIndicator G f))

theorem homIndicator_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1379] : ((∀ {V : Type} (G : SimpleGraph V) (f : PatternVertex → V),
  0≤homIndicator G f)) := @OAI.SidorenkoCounterexample.ProofCertificate_1379.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1380 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V) (f : PatternVertex → V),
    homIndicator G f≤1))

theorem homIndicator_le_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1380] : ((∀ {V : Type} (G : SimpleGraph V) (f : PatternVertex → V),
  homIndicator G f≤1)) := @OAI.SidorenkoCounterexample.ProofCertificate_1380.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1381 : Prop where
  proof : ((∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    homDensity H G=uniformMean (homIndicator G)))

theorem homDensity_eq_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1381] : ((∀ {V : Type} [Fintype V] (G : SimpleGraph V),
  homDensity H G=uniformMean (homIndicator G))) := @OAI.SidorenkoCounterexample.ProofCertificate_1381.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1382 : Prop where
  proof : ((∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    edgeDensity G=uniformMean (fun ab : V × V => edgeIndicator G ab.1 ab.2)))

theorem edgeDensity_eq_mean [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1382] : ((∀ {V : Type} [Fintype V] (G : SimpleGraph V),
  edgeDensity G=uniformMean (fun ab : V × V => edgeIndicator G ab.1 ab.2))) := @OAI.SidorenkoCounterexample.ProofCertificate_1382.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1383 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V),
    0≤homDensity H G))

theorem homDensity_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1383] : ((∀ {V : Type} (G : SimpleGraph V),
  0≤homDensity H G)) := @OAI.SidorenkoCounterexample.ProofCertificate_1383.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1384 : Prop where
  proof : ((∀ {V : Type} (G : SimpleGraph V),
    0≤edgeDensity G))

theorem edgeDensity_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1384] : ((∀ {V : Type} (G : SimpleGraph V),
  0≤edgeDensity G)) := @OAI.SidorenkoCounterexample.ProofCertificate_1384.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1385 : Prop where
  proof : ((∀ {V : Type} [Fintype V] (G : SimpleGraph V)
        (h : ∀ a b,¬G.Adj a b),
    edgeDensity G=0))

theorem edgeDensity_eq_zero_of_edgeless [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1385] : ((∀ {V : Type} [Fintype V] (G : SimpleGraph V)
      (h : ∀ a b,¬G.Adj a b),
  edgeDensity G=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_1385.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class _root_.OAI.SidorenkoCounterexample.ProofCertificate_1386 : Prop where
  proof : ((∀ {A : Type} [Fintype A] (π : FiniteLaw A) (U : A → A → ℝ),
    (FiniteLaw.independent (fun _ : PatternVertex => π)).mean (fun z =>
          ∏ k : ActCorner,U (z (.inl (cornerPoint k))) (z (.inr k.1)))=bipartiteMoment π π U))

theorem sourceMoment_eq_bipartite [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_1386] : ((∀ {A : Type} [Fintype A] (π : FiniteLaw A) (U : A → A → ℝ),
  (FiniteLaw.independent (fun _ : PatternVertex => π)).mean (fun z =>
        ∏ k : ActCorner,U (z (.inl (cornerPoint k))) (z (.inr k.1)))=bipartiteMoment π π U)) := @OAI.SidorenkoCounterexample.ProofCertificate_1386.proof certificateEvidence
end

end SidorenkoCounterexample
end
end OAI


