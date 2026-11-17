-- Prove2me | Definitions.Def_GroupCohomology_FiniteFlatCocycle
-- name    : GroupCohomology_FiniteFlatCocycle
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:26.933185+00:00
-- url     : https://prove2.me/theorems/ad2bfa66-e585-4ac5-86f4-61c28885b02c
-- title:
--   Finite-flat local representations and cocycle classes
-- statement:
--   The file defines a local action to be finite flat when it is represented by a finite flat cocommutative Hopf algebra over $ℤ_p$, whose geometric points under convolution are equivariantly identified with the given additive group. A cocycle is finite flat when its action on $W×𝔽_p$ has such a model, and the file defines the subspace of $H^1$ spanned by classes admitting these models. This is the local finite-flat condition used in the Kummer and Selmer arguments.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
set_option autoImplicit false

namespace groupCohomology

/-- A finite-flat Hopf model of the given local action on an additive group.
The equivalence identifies convolution with addition and intertwines local automorphisms. -/
def IsFiniteFlatRepresentation (p : ℕ) [Fact p.Prime]
    {W : Type} [AddCommGroup W]
    (act : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W → W) : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
    Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
    ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ W,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = σ (f h)) → e g = act σ (e f)

/-- Finite flatness of the extension attached to a local additive cocycle.
For cocycles the displayed formula is the usual action on `W × ZMod p`.
Continuity and the cocycle identity are retained by the caller's cohomology carrier. -/
def IsFiniteFlatCocycle (p : ℕ) [Fact p.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (c : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W) : Prop :=
  IsFiniteFlatRepresentation p (fun σ (x : W × ZMod p) =>
    (ρ σ x.1 + x.2 • c σ, x.2))

/-- The local finite-flat class space is the span of classes admitting a finite-flat
cocycle-extension model. With a coefficient model, taking the span adds no classes. -/
noncomputable def finiteFlatClasses (p : ℕ) [Fact p.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W) :
    Submodule (ZMod p) (H1 (Rep.of ρ)) :=
  Submodule.span (ZMod p)
    {y | ∃ c : cocycles₁ (Rep.of ρ), IsFiniteFlatCocycle p ρ c ∧ y = H1π (Rep.of ρ) c}

end groupCohomology


