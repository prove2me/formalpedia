-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
-- name    : QEC_Coding_QuantumTanner_SpectralFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:53:37.40307+00:00
-- url     : https://prove2.me/theorems/bf916fcb-3628-4494-bae1-80bc51b2e197
-- title:
--   Spectral Family
-- statement:
--   Definitions and structural lemmas for Spectral Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SpectralFamily.lean

import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe u v
namespace Family
end Family
def HasGoodSampleFamily
    {Index : Type u} {G : Index → Type v} {A B : Type v}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [Fintype A] [Fintype B]
    (L : ∀ i, A → G i) (R : ∀ i, B → G i)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : ∀ i, Function.Injective (L i)) (hR : ∀ i, Function.Injective (R i))
    (hLA : ∀ i a, L i (invA a) = (L i a)⁻¹)
    (hRB : ∀ i b, R i (invB b) = (R i b)⁻¹)
    (hTNC : ∀ i g a b, L i a * g ≠ g * R i b)
    (delta eta rho : ℝ) (Delta : ℕ)
    (sample : RandomLocalCodeSample (randomRowCount rho Delta) A B) : Prop :=
  let family := fun i => canonicalDataOfLocalCodeSample (L i) (R i) invA invB
    (hL i) (hR i) (hLA i) (hRB i) (hTNC i) sample
  ∃ hCofinal : ∀ N : ℕ, ∃ i, N ≤ (family i).blockLength,
    QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily (Family.ofData family hCofinal) ∧
    QEC.QLDPC.HasEventualRateAtLeast (Family.ofData family hCofinal)
      ((1 - 2 * rho) ^ 2) ∧
    QEC.QLDPC.HasEventualRelativeDistanceAtLeast (Family.ofData family hCofinal)
      (delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + eta))) ∧
    ∀ i,
      (1 - 2 * rho) ^ 2 * (family i).blockLength ≤ ((family i).encodedDimension : ℝ) ∧
      delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + eta)) *
          ((Family.ofData family hCofinal).blockLength i : ℝ) ≤
        ((Family.ofData family hCofinal).distance i : ℝ) ∧
      QEC.Coding.BoundedLocality ((Family.ofData family hCofinal).localityProfile i)
        (Delta * Delta)
end QEC.Coding.QuantumTanner


