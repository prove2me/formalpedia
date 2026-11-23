-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
-- name    : Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:13.470152+00:00
-- url     : https://prove2.me/theorems/f895cc2e-4d9e-488f-8b26-78709d3b0e03
-- title:
--   Last Graded Of Graded Alone
-- statement:
--   Definitions and structural lemmas for Last Graded Of Graded Alone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/LastGradedOfGradedAlone.lean

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
def dualWt {r : ℕ} (M : ℕ) (κ : Fin r → ℕ) : Fin r → ℕ := fun a => M - κ (Fin.rev a)
def DualWtSpec : Prop :=
  ∀ (r M : ℕ) (κ : Fin r → ℕ), ((∀ a, κ a ≤ M) → dualWt M (dualWt M κ) = κ) ∧ (∀ a, dualWt M κ a ≤ M) ∧
    (Antitone κ → Antitone (dualWt M κ))
def BlockDual : Prop :=
  ∀ (p q w M : ℕ) (κ : Fin q → ℕ),
    (fun a : Fin (p + q) => dualWt M (blockWtLast p q w κ) (Fin.cast (Nat.add_comm p q) a)) =
      blockWt p q (M - w) (dualWt M κ)
def DepthDual : Prop :=
  ∀ (p q w M i : ℕ) (μ : Fin (q + p) → ℕ), w ≤ M → (∀ a, μ a ≤ M) →
    (IsDepthLast p q w μ i ↔
      IsDepth p q (M - w) (fun a : Fin (p + q) => M - μ (Fin.rev (Fin.cast (Nat.add_comm p q) a))) i)
def WtBound : Prop :=
  ∀ (r M : ℕ) (ν μ : Fin r → ℕ), Antitone ν → (∀ a, ν a ≤ M) → nablaWt r ν μ ≠ ⊥ → ∀ a, μ a ≤ M
def ExpTwist : Prop :=
  ∀ (l r c : ℕ) (ν μ : Fin r → ℕ) (e : ℕ), Antitone ν →
    (ExpLe l r (fun a => ν a + c) (fun a => μ a + c) e ↔ ExpLe l r ν μ e)
def ExpDual : Prop :=
  ∀ (l r M : ℕ) (ν μ : Fin r → ℕ) (e : ℕ), l.Prime → Antitone ν → (∀ a, ν a ≤ M) → (∀ a, μ a ≤ M) →
    (ExpLe l r ν μ e ↔ ExpLe l r (fun a => M - ν (Fin.rev a)) (fun a => M - μ (Fin.rev a)) e)
def LastGradedOfGraded : Prop := ExpDual → LemmaDGraded → LemmaDLastGraded
noncomputable def genDet (r : ℕ) : MvPolynomial (Fin r × Fin r) ℤ :=
  (Matrix.of fun a s : Fin r => (X (a, s) : MvPolynomial (Fin r × Fin r) ℤ)).det
noncomputable def cofMap (r : ℕ) :
    MvPolynomial (Fin r × Fin r) ℤ →ₐ[ℤ] MvPolynomial (Fin r × Fin r) ℤ :=
  aeval fun v : Fin r × Fin r =>
    (Matrix.of fun a s : Fin r => (X (a, s) : MvPolynomial (Fin r × Fin r) ℤ)).adjugate (Fin.rev v.2) (Fin.rev v.1)
def NablaDual : Prop :=
  ∀ (r M : ℕ) (ν : Fin r → ℕ), Antitone ν → (∀ a, ν a ≤ M) → ∀ x ∈ dualWeyl ℤ r r ν,
    ∃ g ∈ dualWeyl ℤ r r (dualWt M ν), genDet r ^ (∑ a, ν a) * g = genDet r ^ M * cofMap r x
def WeylDual : Prop :=
  ∀ (r M : ℕ) (ν : Fin r → ℕ), Antitone ν → (∀ a, ν a ≤ M) → ∀ x ∈ weyl ℤ r r le_rfl ν,
    ∃ g ∈ weyl ℤ r r le_rfl (dualWt M ν), genDet r ^ (∑ a, ν a) * g = genDet r ^ M * cofMap r x
def DualWeight : Prop :=
  ∀ (r M : ℕ) (μ : Fin r → ℕ) (x g : MvPolynomial (Fin r × Fin r) ℤ), (∀ a, μ a ≤ M) →
    IsWeightedHomogeneous (rowW r r) x μ → genDet r ^ (∑ a, μ a) * g = genDet r ^ M * cofMap r x →
      IsWeightedHomogeneous (rowW r r) g (dualWt M μ)
def CofCof : Prop :=
  ∀ r : ℕ, cofMap r (genDet r) = genDet r ^ (r - 1) ∧
    ∀ (N : ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ), x.IsHomogeneous N →
      genDet r ^ N * cofMap r (cofMap r x) = genDet r ^ ((r - 1) * N) * x
def ExpDualOfLattices : Prop := NablaDual → WeylDual → DualWeight → CofCof → ExpDual
def LastGradedOfGradedAlone : Prop := LemmaDGraded → LemmaDLastGraded
end Formalism.CohomologicalDescent.LD


