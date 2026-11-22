-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
-- name    : Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:56.982811+00:00
-- url     : https://prove2.me/theorems/974631b3-a5af-46e8-bf59-4a1546f6563b
-- title:
--   Stabiliser Complement Decomposition
-- statement:
--   Definitions and structural lemmas for Stabiliser Complement Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/StabiliserComplementDecomposition.lean

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.ExpansionTerms
section PartA2
open Finset Real MeasureTheory NumberField
def BlockMinorSumAbsoluteBound : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (r : ℕ)
    (S : Finset (Σ c : Composition (r + 1), (Fin c.length → E))), (∀ γ ∈ S, BlockEndMinorsIntegral γ) →
      ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ ≤ C ^ (Fintype.card (InfinitePlace E) * (r + 1))
def BlockMinorAbsoluteFromExplicit : Prop := BlockMinorSumPowSixtyFour → BlockMinorSumAbsoluteBound
def MomentConstantBound : Prop :=
  ∀ C0 CA C1 : ℝ, 0 ≤ C0 → 0 ≤ CA → 0 ≤ C1 → ∃ C : ℝ,
    ∀ (r n : ℕ) (b bv ka T j q : ℝ), 2 ≤ b → 0 < ka → ka ≤ b ^ C0 → ka⁻¹ ≤ b ^ C0 → 1 ≤ T →
      T ≤ b ^ (C0 * (2 * (r : ℝ) + 2)) → 1 ≤ n → (n : ℝ) ≤ bv → bv ≤ b → 0 ≤ j → 0 ≤ q → j + q ≤ b →
      ((n : ℝ) * √(T * max ka ka⁻¹ ^ (2 * r) * b ^ CA) * (6 * bv) ^ (2 * r + 2)) *
          max 1 (C1 * (n : ℝ) ^ 2 * (b + j + q) / ka) ^ r ≤
        b ^ (C * (2 * (r : ℝ) + 2)) * (1 + 1 / ka) ^ (2 * r + 2)
end PartA2
section PartB2
open Finset Matrix Polynomial
open scoped ComplexConjugate TensorProduct
def AntidiagonalSignChoose : Prop := ∀ s : ℕ, ParitySign s = (-1) ^ (s.choose 2)
def BlockMinorEqLeadingMinor : Prop :=
  ∀ (F : Type) [Field F] (d : ℕ) (c : Composition d) (t : Fin c.length → F) (a : Fin c.length),
    IndexedMinorEntry c.blocksFun t a = leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo ((a : ℕ) + 1))
def LeadingMinorCodingsAgree : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (Z : Matrix (Fin d) (Fin d) R) (l : ℕ) (h : l ≤ d),
    leadingPrincipalMinor Z l = LeadingPrincipalMinor Z l h
def DminBridge : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (l : Fin (r + 2)), Formalism.QuantumDeterminants.Dmin k r z z' g l = leadingPrincipalMinor (Formalism.QuantumDeterminants.Zhat k r z z' g) (l : ℕ)
def GfBridge : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    Formalism.QuantumDeterminants.Gf k r z z' g =
      gramDiscriminant r (Formalism.QuantumDeterminants.Zhat k r z z' g) (Formalism.QuantumDeterminants.Tz k r z) (Formalism.QuantumDeterminants.Tz k r z')
def GfLeD : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    0 ≤ Formalism.QuantumDeterminants.Tz k r z → 0 ≤ Formalism.QuantumDeterminants.Tz k r z' →
      Formalism.QuantumDeterminants.Gf k r z z' g ≤ ‖Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))‖ ^ 2
def InOrthComplementSpan (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (x : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x (Formalism.QuantumDeterminants.gramVec k r z z' g i) = 0
def StabiliserComplementDecomposition : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), 0 < Formalism.QuantumDeterminants.Gf k r z z' g →
      (∀ x : Fin (2 * r + k + 1) → ℂ, ∃ (co : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (u : Fin (2 * r + k + 1) → ℂ),
        InOrthComplementSpan k r z z' g u ∧ x = (∑ i, co i • Formalism.QuantumDeterminants.gramVec k r z z' g i) + u) ∧
      1 ≤ k ∧
      ∃ bu : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, LinearIndependent ℂ bu ∧ (∀ i, InOrthComplementSpan k r z z' g (bu i)) ∧
        ∀ x, InOrthComplementSpan k r z z' g x → x ∈ Submodule.span ℂ (Set.range bu)
def StabiliserPairExists : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), 0 < Formalism.QuantumDeterminants.Gf k r z z' g →
    ∀ (a a' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      IsUpperUnitriangular a → IsUpperUnitriangular a' → aᴴ * Formalism.QuantumDeterminants.Zhat k r z z' g * a' = Formalism.QuantumDeterminants.Zhat k r z z' g →
      (∀ x, InOrthComplementSpan k r z z' g x → InOrthComplementSpan k r z z' g (q *ᵥ x)) →
      (∀ x y, InOrthComplementSpan k r z z' g x → InOrthComplementSpan k r z z' g y →
        Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (q *ᵥ x) (q *ᵥ y) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y) →
      ∃! p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
        (p ∈ Formalism.QuantumDeterminants.Sset k r z ∧ g⁻¹ * p * g ∈ Formalism.QuantumDeterminants.Sset k r z') ∧
        (∀ b, p *ᵥ Formalism.QuantumDeterminants.fvec k r z b = ∑ e, a e b • Formalism.QuantumDeterminants.fvec k r z e) ∧
        (∀ b, p *ᵥ (g *ᵥ Formalism.QuantumDeterminants.fvec k r z' b) = ∑ e, a' e b • (g *ᵥ Formalism.QuantumDeterminants.fvec k r z' e)) ∧
        ∀ x, InOrthComplementSpan k r z z' g x → p *ᵥ x = q *ᵥ x
def StabiliserProductConverse : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), 0 < Formalism.QuantumDeterminants.Gf k r z z' g →
    ∀ (c : Composition (r + 1)) (t : Fin c.length → ℂ), Formalism.QuantumDeterminants.Zhat k r z z' g = blockAntidiagonalMatrix c t →
    ∀ (a' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      IsUpperUnitriangular a' → (∀ i j, c.index i ≠ c.index j → a' i j = 0) →
      (∀ x, InOrthComplementSpan k r z z' g x → InOrthComplementSpan k r z z' g (q *ᵥ x)) →
      (∀ x y, InOrthComplementSpan k r z z' g x → InOrthComplementSpan k r z z' g y →
        Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (q *ᵥ x) (q *ᵥ y) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y) →
      ∃! p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
        (p ∈ Formalism.QuantumDeterminants.Sset k r z ∧ g⁻¹ * p * g ∈ Formalism.QuantumDeterminants.Sset k r z') ∧
        (∀ b, p *ᵥ (g *ᵥ Formalism.QuantumDeterminants.fvec k r z' b) = ∑ e, a' e b • (g *ᵥ Formalism.QuantumDeterminants.fvec k r z' e)) ∧
        ∀ x, InOrthComplementSpan k r z z' g x → p *ᵥ x = q *ᵥ x
def StabiliserPreservesComplement : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    ∀ p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      p ∈ Formalism.QuantumDeterminants.Sset k r z → g⁻¹ * p * g ∈ Formalism.QuantumDeterminants.Sset k r z' →
      (∀ x, InOrthComplementSpan k r z z' g x → InOrthComplementSpan k r z z' g (p *ᵥ x)) ∧
      ∀ x y, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (p *ᵥ x) (p *ᵥ y) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y
noncomputable def formalDeterminantVector {V : Type*} [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {r : ℕ}
    (y f' : Fin (r + 1) → V) : V :=
  ∑ a, (Matrix.of fun a b => h (y a) (f' b)).adjugate (Fin.last r) a • y a
def DualVectorOrthogonal : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (r : ℕ) (y f' : Fin (r + 1) → V)
    (b : Fin (r + 1)),
    h (formalDeterminantVector h y f') (f' b) = if b = Fin.last r then (Matrix.of fun a b => h (y a) (f' b)).det else 0
noncomputable def formalDeterminantVectorOnGroup (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, (Matrix.of fun a b => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a)
    (Formalism.QuantumDeterminants.fvec k r z' b)).adjugate (Fin.last r) a • (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a)
noncomputable def N3om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if r ≤ i.val ∧ i.val ≤ r + k then
    formalDeterminantVectorOnGroup k r z z' g i +
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (formalDeterminantVectorOnGroup k r z z' g) z' / (Formalism.QuantumDeterminants.Tz k r z' : ℂ) * z' i
  else 0
def OrthogonalComplementDecomposition : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    Formalism.QuantumDeterminants.Tz k r z' ≠ 0 → ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Formalism.QuantumDeterminants.inWb k r (N3om k r z z' g) ∧
      (∀ b, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (Formalism.QuantumDeterminants.fvec k r z' b) = 0) ∧
      ∃ co : Fin (r + 1) → ℂ, formalDeterminantVectorOnGroup k r z z' g = (∑ b, co b • Formalism.QuantumDeterminants.fvec k r z' b) + N3om k r z z' g
def DualVectorUnipotentInvariant : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      N3om k r z z' (n * g * n') = N3om k r z z' g
def DualVectorEquivariant : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      N3om k r z z' (h * g * h') = h'⁻¹ *ᵥ N3om k r z z' g
def DualVectorNormOnGroup : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z' → ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (N3om k r z z' g) =
        ((Formalism.QuantumDeterminants.Gf k r z z' g / Formalism.QuantumDeterminants.Tz k r z' : ℝ) : ℂ) ∧
      (0 ≤ Formalism.QuantumDeterminants.Tz k r z →
        (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (N3om k r z z' g)).re ≤
          ‖Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))‖ ^ 2 / Formalism.QuantumDeterminants.Tz k r z')
noncomputable def rankTwoSkewOperator {V : Type*} [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (e v x : V) : V :=
  h x v • e - h x e • v
def RankTwoSkewInNilradical : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ x y, h y x = conj (h x y)) →
    ∀ (r : ℕ) (f : Fin (r + 1) → V) (T : ℝ),
      (∀ a b, h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(T : ℂ) else 0) →
      ∀ (a : Fin r) (e v : V), e - f a.castSucc ∈ Submodule.span ℂ (f '' {b | b < a.castSucc}) →
        (∀ b, b ≤ a.castSucc → h (f b) v = 0) →
        e ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) ∧
        (∀ x, (∀ b : Fin r, h x (f b.castSucc) = 0) → rankTwoSkewOperator h e v x = h x v • e) ∧
        (∀ b, rankTwoSkewOperator h e v (f b) = h (f b) v • e) ∧
        (∀ b, b ≤ a.castSucc → rankTwoSkewOperator h e v (f b) = 0) ∧
        rankTwoSkewOperator h e v (f a.succ) - h (f a.succ) v • f a.castSucc ∈ Submodule.span ℂ (f '' {b | b < a.castSucc}) ∧
        rankTwoSkewOperator h e v e = 0 ∧ rankTwoSkewOperator h e v v = h v v • e
noncomputable def rankTwoSkewMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (e v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    Formalism.QuantumDeterminants.herm H (Pi.single j 1) v * e i - Formalism.QuantumDeterminants.herm H (Pi.single j 1) e * v i
def RankTwoSkewMatrixApply : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (e v x : Fin n → ℂ),
    rankTwoSkewMatrix H e v *ᵥ x = Formalism.QuantumDeterminants.herm H x v • e - Formalism.QuantumDeterminants.herm H x e • v
def RankTwoSkewConjugation : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), IsUnit H.det → ∀ g ∈ Formalism.QuantumDeterminants.UH H, ∀ e v : Fin n → ℂ,
    g⁻¹ * rankTwoSkewMatrix H e v * g = rankTwoSkewMatrix H (g⁻¹ *ᵥ e) (g⁻¹ *ᵥ v)
noncomputable def nilpotentExpSquare {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (e v : ι → ℂ) (t : ℝ) :
    Matrix ι ι ℂ :=
  1 + (t : ℂ) • rankTwoSkewMatrix H e v + ((t : ℂ) ^ 2 / 2) • (rankTwoSkewMatrix H e v * rankTwoSkewMatrix H e v)
def RankTwoNilpotentGroup : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ (a : Fin r) (e v : Fin (2 * r + k + 1) → ℂ),
      e - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
        Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) →
      (∀ b, b ≤ a.castSucc → Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) v = 0) →
      rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v * rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v * rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v = 0 ∧
      (∀ s t : ℝ, nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v (s + t) =
        nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v s * nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) ∧
      ∀ t : ℝ, nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t ∈ Formalism.QuantumDeterminants.Nset k r ∧
        Formalism.QuantumDeterminants.ell k r z (nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) =
          (t : ℂ) * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) v
def CharacterDerivativeNorm : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ (a : Fin r) (e v : Fin (2 * r + k + 1) → ℂ) (ka l : ℝ),
      e - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
        Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) →
      (∀ b, b ≤ a.castSucc → Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) v = 0) →
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) v = -Complex.I * (l : ℂ) →
      ∀ t : ℝ, Formalism.QuantumDeterminants.psi k r z ((ka : ℂ) * Formalism.QuantumDeterminants.cStd) (nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) =
        Complex.exp (-(2 * (ka : ℂ) * (l : ℂ) * (t : ℂ)) * Complex.I)
def MajorantOrthogonalComponent : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (y : Fin n → V) (a : Fin n),
    ∃ u : V, u - y a ∈ Submodule.span ℂ (y '' {b | b < a}) ∧ (∀ b, b < a → inner ℂ u (y b) = 0) ∧
      ‖u‖ = majorantDistance y a ∧ inner ℂ u (y a) = ((‖u‖ ^ 2 : ℝ) : ℂ)
def SkewVectorChoice : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ (r : ℕ) (y : Fin (r + 1) → V) (a : Fin r), majorantDistance y a.succ ≠ 0 →
      ∃ e' v' : V, e' - y a.castSucc ∈ Submodule.span ℂ (y '' {b | b < a.castSucc}) ∧
        ‖e'‖ = majorantDistance y a.castSucc ∧ ‖v'‖ = 1 ∧ (∀ b, b ≤ a.castSucc → majorantHermitianForm θ (y b) v' = 0) ∧
        majorantHermitianForm θ (y a.succ) v' = -Complex.I * (majorantDistance y a.succ : ℂ)
def MomentPointwiseBound : Prop :=
  ∀ (V ι : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ) (x : ι → V) (P : V) (d : ℂ)
    (ka la la1 : ℝ), 0 < la → ‖d‖ = 2 * ka * la1 → d • P = ∑ i, c i • x i → ∑ i, ‖c i‖ ^ 2 ≤ 4 * la ^ 2 →
      (ka * la1 / la) ^ 2 * ‖P‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2
def TensorFormExists : Prop :=
  ∀ (W V : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (ip : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ) (_xi : Module.Basis (Fin n) ℂ V),
    ∃ B : (W ⊗[ℂ] V) →ₗ[ℂ] (W ⊗[ℂ] V) →ₗ⋆[ℂ] ℂ,
      ∀ (w w' : W) (ξ ξ' : V), B (w ⊗ₜ[ℂ] ξ) (w' ⊗ₜ[ℂ] ξ') = ip w w' * h ξ ξ'
def TensorFormNondegenerate : Prop :=
  ∀ (W V : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (ip : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ) (xi : Module.Basis (Fin n) ℂ V) (ep : Fin n → ℝ)
    (B : (W ⊗[ℂ] V) →ₗ[ℂ] (W ⊗[ℂ] V) →ₗ⋆[ℂ] ℂ), (∀ c, ep c = 1 ∨ ep c = -1) →
    (∀ c c', h (xi c) (xi c') = if c = c' then (ep c : ℂ) else 0) →
    (∀ (w w' : W) (ξ ξ' : V), B (w ⊗ₜ[ℂ] ξ) (w' ⊗ₜ[ℂ] ξ') = ip w w' * h ξ ξ') →
    (∀ w, (∀ w', ip w w' = 0) → w = 0) → ∀ x, (∀ y, B x y = 0) → x = 0
def TensorEndomorphismComponents : Prop :=
  ∀ (W V : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (xi : Module.Basis (Fin n) ℂ V) (A : Module.End ℂ (W ⊗[ℂ] V)),
    ∃! Ac : Matrix (Fin n) (Fin n) (Module.End ℂ W),
      ∀ (w : W) (c : Fin n), A (w ⊗ₜ[ℂ] xi c) = ∑ c', Ac c' c w ⊗ₜ[ℂ] xi c'
def PartialTraceIdentity : Prop :=
  ∀ (W V : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (ip : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ) (xi : Module.Basis (Fin n) ℂ V) (ep : Fin n → ℝ)
    (B : (W ⊗[ℂ] V) →ₗ[ℂ] (W ⊗[ℂ] V) →ₗ⋆[ℂ] ℂ), (∀ c, ep c = 1 ∨ ep c = -1) →
    (∀ c c', h (xi c) (xi c') = if c = c' then (ep c : ℂ) else 0) →
    (∀ (w w' : W) (ξ ξ' : V), B (w ⊗ₜ[ℂ] ξ) (w' ⊗ₜ[ℂ] ξ') = ip w w' * h ξ ξ') →
    ∀ (A : Module.End ℂ (W ⊗[ℂ] V)) (Ac : Matrix (Fin n) (Fin n) (Module.End ℂ W)),
      (∀ (w : W) (c : Fin n), A (w ⊗ₜ[ℂ] xi c) = ∑ c', Ac c' c w ⊗ₜ[ℂ] xi c') →
      ∀ w w' : W, ∑ c, (ep c : ℂ) * B (A (w ⊗ₜ[ℂ] xi c)) (w' ⊗ₜ[ℂ] xi c) = ip (Ac.trace w) w'
def SchurOrthogonalityRelations₂ : Prop :=
  ∀ (n : ℕ) (hxi N1 N2 d Bxx : ℂ) (ds rho : Fin n → ℝ) (eps : Fin n → ℝ) (X Y Bs : Fin n → ℂ),
    (∀ s, eps s = 1 ∨ eps s = -1) → N2 ≠ 0 → Bxx = N1 * hxi →
    (∀ s, X s = (eps s : ℂ) * Bs s) → (∀ s, Y s = (eps s : ℂ) * (rho s : ℂ) * N2) →
    hxi * N1 * N2 / d = ∑ s, X s / (ds s : ℂ) * Y s →
    Bxx / d = ∑ s, ((rho s / ds s : ℝ) : ℂ) * Bs s
def ClusterHypotheses {H ι κ : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι] [Fintype κ]
    (bs : OrthonormalBasis ι ℂ H) (D O : H →ₗ[ℂ] H) (δ : ι → ℝ) (VV : Submodule ℂ H) (b dl : ℝ)
    (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (In : Finset κ) : Prop :=
  0 < b ∧ dl ≤ b / 32 ∧
  (∀ i, D (bs i) = (δ i : ℂ) • bs i) ∧
  (∀ i, (-b / 8 - dl ≤ δ i ∧ δ i ≤ dl) ∨ (b - dl ≤ δ i ∧ δ i ≤ 2 * b + dl)) ∧
  (∀ x ∈ VV, ‖O x‖ ≤ b / 16 * ‖x‖) ∧ (∀ x ∈ VV, (D + O) x ∈ VV) ∧
  (∀ x ∈ VV, ∑ i, p i x = x) ∧ (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ (D + O) (p i x) = lam i • p i x) ∧
  (∀ i ∈ In, ‖lam i + ((b / 16 : ℝ) : ℂ)‖ < 9 * b / 16) ∧ (∀ i, i ∉ In → 9 * b / 16 < ‖lam i + ((b / 16 : ℝ) : ℂ)‖)
def NodesProjectorNormBound : Prop :=
  ∀ (H ι κ : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (bs : OrthonormalBasis ι ℂ H) (D O : H →ₗ[ℂ] H) (δ : ι → ℝ) (VV : Submodule ℂ H) (b dl : ℝ)
    (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (In : Finset κ), ClusterHypotheses bs D O δ VV b dl p lam In →
      ∀ x ∈ VV, ‖∑ i ∈ Inᶜ, p i x‖ ≤ 31 / 13 * ‖x‖
def NodesFromClusterNorm : Prop := ClusterProjectorNormBound → NodesProjectorNormBound
def OperatorNormOnSubspace : Prop :=
  ∀ (H ι κ : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι] [Fintype κ]
    (bs : OrthonormalBasis ι ℂ H) (D O : H →ₗ[ℂ] H) (δ : ι → ℝ) (VV : Submodule ℂ H) (b dl : ℝ)
    (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (In : Finset κ), ClusterHypotheses bs D O δ VV b dl p lam In →
      ∀ x ∈ VV, ‖(D + O) x‖ ≤ (2 * b + dl + b / 16) * ‖x‖ ∧ ‖(D + O) x‖ ≤ 3 * b * ‖x‖
def NodeProjectorNormExplicit : Prop :=
  ∀ (H ι κ : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (bs : OrthonormalBasis ι ℂ H) (D O : H →ₗ[ℂ] H) (δ : ι → ℝ) (VV : Submodule ℂ H) (b dl : ℝ)
    (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (In : Finset κ) (s : κ), ClusterHypotheses bs D O δ VV b dl p lam In → s ∉ In →
    (∀ i, i ∉ In → ‖lam i‖ ≤ 3 * b) → (∀ i, i ∉ In → i ≠ s → 1 ≤ ‖lam s - lam i‖) →
      ∀ x ∈ VV, ‖p s x‖ ≤ 3 * (6 * b) ^ (Inᶜ.erase s).card * ‖x‖
def QuadraticProjectorSum : Prop :=
  ∀ (H κ : Type) [SeminormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ]
    (hh : H →ₗ[ℂ] H →ₗ⋆[ℂ] ℂ) (VV : Submodule ℂ H) (p : κ → H →ₗ[ℂ] H) (In : Finset κ) (Cc Cs : ℝ),
    (∀ x y, hh y x = conj (hh x y)) → (∀ x, ‖hh x x‖ ≤ ‖x‖ ^ 2) →
    (∀ s t, s ≠ t → ∀ x ∈ VV, hh (p s x) (p t x) = 0) → (∀ s ∈ In, ∀ x ∈ VV, 0 ≤ (hh (p s x) (p s x)).re) →
    (∀ x ∈ VV, ‖∑ s ∈ In, p s x‖ ≤ Cc * ‖x‖) → (∀ s, s ∉ In → ∀ x ∈ VV, ‖p s x‖ ≤ Cs * ‖x‖) →
      ∀ x ∈ VV, ∑ s, ‖hh (p s x) (p s x)‖ ≤ (Cc ^ 2 + (Inᶜ.card : ℝ) * Cs ^ 2) * ‖x‖ ^ 2
def NodeProjectorSizes : Prop :=
  ∀ (M n : ℕ) (b : ℝ), M + 1 ≤ n → (n : ℝ) ≤ b →
    3 * (6 * b) ^ M ≤ (6 * (n : ℝ) * b) ^ (M + 1) ∧
    (18 / 13 : ℝ) ^ 2 + ((M : ℝ) + 1) * (3 * (6 * b) ^ M) ^ 2 ≤ (6 * b) ^ (2 * (M + 1)) ∧
    (6 * b) ^ (2 * (M + 1)) ≤ (6 * (n : ℝ) * b) ^ (2 * (M + 1) + 1)
end PartB2
section PartC2
open Finset
noncomputable def casimirGeneral (n : ℕ) (mu : Fin n → ℝ) : ℝ := (∑ a, mu a ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a ^ 2
noncomputable def compactCasimirValue {n : ℕ} (ε : Fin n → Bool) (nu : Fin n → ℝ) : ℝ :=
  (∑ a, (nu a + Formalism.REAL.rhoC ε a) ^ 2) - ∑ a, Formalism.REAL.rhoC ε a ^ 2
def HalfSumRootsBounds : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : Fin n),
    Formalism.REAL.rhoC ε a + Formalism.REAL.rhoN ε a = Formalism.QuantumDeterminants.rhoStd n a ∧
    |Formalism.REAL.rhoC ε a| ≤ ((n : ℝ) - 1) / 2 ∧ |Formalism.REAL.rhoN ε a| ≤ ((n : ℝ) - 1) / 2 ∧
    |Formalism.REAL.rhoN ε a - Formalism.REAL.rhoC ε a| ≤ ((n : ℝ) - 1) / 2
def CasimirWeightBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (mu nu om : Fin n → ℝ) (j bs : ℝ), 0 ≤ j → (n : ℝ) ≤ bs →
    (∀ a, |mu a| + (n : ℝ) ≤ bs) → ∑ a, |nu a - Formalism.QuantumDeterminants.lowK ε mu a| ≤ j →
    ∑ a, |om a - Formalism.QuantumDeterminants.lowK ε mu a| ≤ j →
    compactCasimirValue ε nu - ∑ a, om a ^ 2 ≤ 4 * (bs + j) * ((n : ℝ) ^ 2 + j) ∧
    compactCasimirValue ε nu - casimirGeneral n mu ≤ 4 * (bs + j) * ((n : ℝ) ^ 2 + j) ∧
    (compactCasimirValue ε nu - ∑ a, om a ^ 2) + (compactCasimirValue ε nu - casimirGeneral n mu) ≤ 8 * (bs + j) * ((n : ℝ) ^ 2 + j)
def CasimirDifferenceBound : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (ε : Fin n → Bool) (mu nu om : Fin n → ℝ) (j bv : ℝ), 1 ≤ n → 0 ≤ j → j ≤ bv →
    (∀ a, |mu a| + (n : ℝ) ≤ 2.02 * bv) → ∑ a, |nu a - Formalism.QuantumDeterminants.lowK ε mu a| ≤ j + 2 →
    ∑ a, |om a - Formalism.QuantumDeterminants.lowK ε mu a| ≤ j + 2 →
    compactCasimirValue ε nu - ∑ a, om a ^ 2 ≤ C * bv * (j + (n : ℝ) ^ 2) ∧
    compactCasimirValue ε nu - casimirGeneral n mu ≤ C * bv * (j + (n : ℝ) ^ 2)
def CasimirStandardRepresentation : Prop :=
  ∀ n : ℕ, casimirGeneral (n + 1) (Formalism.QuantumDeterminants.rhoStd (n + 1) + Pi.single 0 1) = (n : ℝ) + 1 ∧
    casimirGeneral (n + 1) (Formalism.QuantumDeterminants.rhoStd (n + 1) - Pi.single (Fin.last n) 1) = (n : ℝ) + 1
def CasimirShiftEigenvalue : Prop :=
  ∀ (n : ℕ) (mu : Fin n → ℝ) (s s' : Fin n),
    (casimirGeneral n (mu - Pi.single s 1) - casimirGeneral n mu - (n : ℝ)) / 2 = -mu s + (1 - (n : ℝ)) / 2 ∧
    (casimirGeneral n (mu + Pi.single s 1) - casimirGeneral n mu - (n : ℝ)) / 2 = mu s + (1 - (n : ℝ)) / 2 ∧
    (casimirGeneral n (mu + Pi.single s 1) - casimirGeneral n mu - (n : ℝ)) / 2 -
      (casimirGeneral n (mu + Pi.single s' 1) - casimirGeneral n mu - (n : ℝ)) / 2 = mu s - mu s'
def DiagonalEntryNearEigenvalue : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (mu om : Fin n → ℝ) (j : ℝ) (c : Fin n),
    ∑ a, |om a - Formalism.QuantumDeterminants.lowK ε mu a| ≤ j + 2 →
    |-om c - (-mu c + (1 - (n : ℝ)) / 2)| ≤ j + (n : ℝ) + 1
def SpectralPositionBounds : Prop :=
  ∀ (n : ℕ) (b q0 j mc d : ℝ), 1 ≤ n → 0 ≤ q0 → 0 ≤ j → q0 ≤ b / 100 → j + 2 ≤ b / (8704 * (n : ℝ)) →
    8704 * (n : ℝ) ^ 3 ≤ b → |d - (-mc + (1 - (n : ℝ)) / 2)| ≤ j + (n : ℝ) + 1 →
    q0 + ((n : ℝ) - 1) / 2 + j + (n : ℝ) + 1 ≤ b / 32 ∧
    (-q0 ≤ mc → mc ≤ b / 8 + q0 →
      |(-mc + (1 - (n : ℝ)) / 2) + b / 16| < 9 * b / 16 ∧
      -b / 8 - (q0 + ((n : ℝ) - 1) / 2 + j + (n : ℝ) + 1) ≤ d ∧ d ≤ q0 + ((n : ℝ) - 1) / 2 + j + (n : ℝ) + 1) ∧
    (-2 * b - q0 ≤ mc → mc ≤ -b + q0 →
      9 * b / 16 < |(-mc + (1 - (n : ℝ)) / 2) + b / 16| ∧ |-mc + (1 - (n : ℝ)) / 2| ≤ 3 * b ∧
      b - (q0 + ((n : ℝ) - 1) / 2 + j + (n : ℝ) + 1) ≤ d ∧ d ≤ 2 * b + (q0 + ((n : ℝ) - 1) / 2 + j + (n : ℝ) + 1))
def WignerProductLeOne : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin K) (n0 : ℕ), WInterl u rho →
    (0 ≤ WProdPlus u rho l n0 ∧ WProdPlus u rho l n0 ≤ 1) ∧
    (0 ≤ WProdMinus u rho l n0 ∧ WProdMinus u rho l n0 ≤ 1)
def WignerProductVanishing : Prop :=
  ∀ (K : ℕ) (u : Fin (K + 1) → ℝ) (rho : Fin K → ℝ) (l : Fin K) (n0 : ℕ), WInterl u rho →
    (WProdPlus u rho l n0 ≠ 0 ↔ WIL (u + Pi.single l.succ (n0 : ℝ)) rho) ∧
    (WProdMinus u rho l n0 ≠ 0 ↔ WIL (u - Pi.single l.castSucc (n0 : ℝ)) rho)
end PartC2
section PartD2
open Finset
def CutLengthEqualTypes : Prop :=
  ∀ (k : ℕ) (u u'' : ℕ → ℝ) (j l n0 : ℕ), l + 1 < k →
    ((j = l + 1 ∧ ∀ i, i < k → u'' i = u i + if i = l + 1 then (n0 : ℝ) else 0) ∨
     (j = l ∧ ∀ i, i < k → u'' i = u i - if i = l then (n0 : ℝ) else 0)) →
    ∃ α β : ℝ, β - α = (n0 : ℝ) - 4 ∧ (∀ Y, LiesOnCut k u u'' j Y ↔ α ≤ Y ∧ Y ≤ β) ∧
      ∀ r : ℕ, 30 * (r + 1) ^ 2 + 6 ≤ n0 → 30 * ((r : ℝ) + 1) ^ 2 + 2 ≤ β - α
def BpGLe : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (T T' : ℝ), 0 ≤ T → 0 ≤ T' →
    gramDiscriminant r Z T T' ≤ ‖LeadingPrincipalMinor Z (r + 1) le_rfl‖ ^ 2
def BpJBound : Prop :=
  ∀ (G Dm T' om jn JF : ℝ) (p n0 : ℕ), 0 ≤ G → 0 ≤ Dm → G ≤ Dm ^ 2 → 0 < T' → 0 ≤ om → om ^ 2 = G / T' → 0 ≤ jn →
    0 ≤ JF → JF ≤ G ^ p * om ^ n0 * jn →
    JF ≤ Dm ^ (2 * p + n0) * (Real.sqrt T' ^ n0)⁻¹ * jn ∧
    JF ^ 2 ≤ Dm ^ (2 * (2 * p + n0)) * (T' ^ n0)⁻¹ * jn ^ 2
end PartD2
end Formalism.HermitianLatticeCounting.ExpansionTerms


