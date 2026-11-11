-- Prove2me | Definitions.Def_JainCRERepetition_Cubic_copied
-- name    : JainCRERepetition_Cubic_copied
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:25.893781+00:00
-- url     : https://prove2.me/theorems/93636e53-ba77-4ff6-97a4-30294197bf83
-- title:
--   Definitions 2.5–2.9 — coherent families, charges and pure descriptions
-- statement:
--   Let $\mu$ be a prior and $q$ a posterior supported on $\mu$. A copied-input family consists of normalized bipartite vectors $\psi_{xy}$, with Alice holding her question and workspace and Bob holding his own. Its coherent vector is
--
--   $$|\psi\rangle=\sum_{x,y}\sqrt{q(x,y)}|xx\rangle|yy\rangle|\psi_{xy}\rangle.$$
--
--   The two protected question copies are traced only when the indicated marginal requires it. The Alice comparison, its purification form, the actual coherent Alice target, the symmetric Bob target, and the charges $b_A,b_B$ are computed explicitly. In particular, $b_A$ is the loss of relative entropy on discarding the reference; it is not replaced by conditional mutual information.
--
--   Pure descriptions retain both inequalities of Eq. (38), with common finite pure padding, an Alice isometry depending only on $x$, and a Bob unitary depending only on $y$. The sampler predicate states both the optimized and parameterized designated-output guarantees of Fact 2.23, including finite-resource witnesses for every positive slack and equality of local maps for identical local descriptions.
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), pp. 11–14, Definitions 2.5–2.9; p. 18, Fact 2.23; p. 27, Eq. (38); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_quantum

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic

section Copied
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

structure CopiedFamily (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  prior : Law (X × Y)
  posterior : Law (X × Y)
  supported : ∀ z, prior.p z = 0 → posterior.p z = 0
  vector : X → Y → A × B → ℂ
  unit : ∀ x y, IsUnit (vector x y)

abbrev AliceIndex (X Y A : Type) := (X × Y) × (X × A)

def seedMatching (τ : Op (X × (X × A))) : Prop :=
  ∀ a b, (a.1 ≠ a.2.1 ∨ b.1 ≠ b.2.1) → τ a b = 0

def comparison (μ : Law (X × Y)) (τ : Op (X × (X × A))) : Op (AliceIndex X Y A) :=
  fun a b => if a.1.2 = b.1.2 then
    (Real.sqrt (kernel μ.p a.2.1 a.1.2) : ℂ) *
    (Real.sqrt (kernel μ.p b.2.1 b.1.2) : ℂ) *
    τ (a.1.1,a.2) (b.1.1,b.2) else 0

def IsComparison (μ : Law (X × Y)) (ν : Op (AliceIndex X Y A)) : Prop :=
  ∃ τ : Op (X × (X × A)), IsState τ ∧ seedMatching τ ∧
    (∀ x, marginalX μ.p x = 0 → ∀ a, τ (x,(x,a)) (x,(x,a)) = 0) ∧
    ν = comparison μ τ

def aliceTarget (F : CopiedFamily X Y A B) : Op (AliceIndex X Y A) :=
  fun a b => if a.1.2 = b.1.2 ∧ a.1.1 = a.2.1 ∧ b.1.1 = b.2.1 then
    (Real.sqrt (F.posterior.p (a.2.1,a.1.2)) : ℂ) *
    (Real.sqrt (F.posterior.p (b.2.1,b.1.2)) : ℂ) *
    ∑ k, F.vector a.2.1 a.1.2 (a.2.2,k) * star (F.vector b.2.1 b.1.2 (b.2.2,k)) else 0

def CopiedFamily.flip (F : CopiedFamily X Y A B) : CopiedFamily Y X B A where
  prior := swapLaw F.prior
  posterior := swapLaw F.posterior
  supported z := F.supported (z.2,z.1)
  vector y x z := F.vector x y (z.2,z.1)
  unit y x := by
    unfold IsUnit sqnorm
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa only [IsUnit, sqnorm, Fintype.sum_prod_type] using F.unit x y

def bAlice (F : CopiedFamily X Y A B) (ν : Op (AliceIndex X Y A)) : ℝ :=
  charge (aliceTarget F) ν

def bBob (F : CopiedFamily X Y A B) (ν : Op (AliceIndex Y X B)) : ℝ :=
  charge (aliceTarget F.flip) ν

/-- The purified representation in (5), with the traced Y and purifying F already eliminated. -/
def purifiedComparison {E : Type} [Fintype E] (μ : Law (X × Y)) (r : Law X)
    (ξ : X → A × E → ℂ) : Op (AliceIndex X Y A) :=
  fun a b => if a.1.2 = b.1.2 ∧ a.1.1 = a.2.1 ∧ b.1.1 = b.2.1 then
    (Real.sqrt (r.p a.2.1 * kernel μ.p a.2.1 a.1.2) : ℂ) *
    (Real.sqrt (r.p b.2.1 * kernel μ.p b.2.1 b.1.2) : ℂ) *
    ∑ f, ξ a.2.1 (a.2.2,f) * star (ξ b.2.1 (b.2.2,f)) else 0

/-- Pure padding of the entire designated original workspace. -/
def paddedVector (u : A × B → ℂ) (pa pb : ℕ) :
    (A × Fin (pa+1)) × (B × Fin (pb+1)) → ℂ :=
  fun z => if z.1.2 = 0 ∧ z.2.2 = 0 then u (z.1.1,z.2.1) else 0

def PureDescriptions (F : CopiedFamily X Y A B)
    (νA : Op (AliceIndex X Y A)) (νB : Op (AliceIndex Y X B)) : Prop :=
  ∃ (pa pb k : ℕ)
    (u : X → Fin k × (B × Fin (pb+1)) → ℂ)
    (v : Y → Fin k × (B × Fin (pb+1)) → ℂ)
    (J : X → Matrix (A × Fin (pa+1)) (Fin k) ℂ)
    (W : Y → Op (B × Fin (pb+1))),
    (∀ x, IsUnit (u x) ∧ (J x)ᴴ * J x = 1) ∧
    (∀ y, IsUnit (v y) ∧ (W y)ᴴ * W y = 1 ∧ W y * (W y)ᴴ = 1) ∧
    (∑ x, ∑ y, F.posterior.p (x,y) * sqnorm (u x - v y)) ≤
      4 * Real.log 2 * (bAlice F νA + bBob F νB) ∧
    (∑ x, ∑ y, F.posterior.p (x,y) *
      infidelity (ket (((J x) ⊗ₖ (W y)ᴴ) *ᵥ u x))
        (ket (paddedVector (F.vector x y) pa pb))) ≤ Real.log 2 * bAlice F νA

end Copied

/-- The entire original A/B workspaces are the designated output of the sampler. -/
def SamplingConstant (C : ℝ) : Prop :=
  ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (u : X → A × B → ℂ) (v : Y → A × B → ℂ),
    (∀ x, IsUnit (u x)) → (∀ y, IsUnit (v y)) →
    ∀ (p : Law (X × Y)) (ζ : ℝ), 0 < ζ →
      let Δ := ∑ x, ∑ y, p.p (x,y) * sqnorm (u x - v y)
      (∃ P : Preparation (X := X) (Y := Y) (A := A) (B := B),
        (∀ x x', u x = u x' → P.alice x = P.alice x') ∧
        (∀ y y', v y = v y' → P.bob y = P.bob y') ∧
        preparationError p.p (fun x _ => u x) P ≤ min 1 (4*C*Real.sqrt Δ) + ζ) ∧
      (∀ h : ℝ, 0 < h → h < 1/2 →
        ∃ P : Preparation (X := X) (Y := Y) (A := A) (B := B),
          (∀ x x', u x = u x' → P.alice x = P.alice x') ∧
          (∀ y y', v y = v y' → P.bob y = P.bob y') ∧
          preparationError p.p (fun x _ => u x) P ≤ C*(h^2+Δ/h^2+Δ)+ζ)

end JainCRERepetition.Cubic


