-- Prove2me | Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
-- name    : Formalism_AlgebraicWeights_IsAlgWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:13.154293+00:00
-- url     : https://prove2.me/theorems/d1066cc0-e8b9-430d-8a33-021e219bf6f7
-- title:
--   Is Alg Weight
-- statement:
--   Definitions and structural lemmas for Is Alg Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AlgebraicWeights/IsAlgWeight.lean

import Mathlib
import Definitions.Def_Formalism_ConjugateSelfDual_Imports
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
namespace Formalism.AUTREP
section Eig
variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
def eig (T : Subalgebra k (Module.End k M)) (x : T →ₐ[k] k) : Submodule k M :=
  ⨅ t : T, LinearMap.ker ((t : Module.End k M) - algebraMap k (Module.End k M) (x t))
def mult (T : Subalgebra k (Module.End k M)) (x : T →ₐ[k] k) : ℕ := Module.finrank k (eig T x)
def xval (T : Subalgebra k (Module.End k M)) (x : T →ₐ[k] k) (t : Module.End k M) : k :=
  open Classical in if h : t ∈ T then x ⟨t, h⟩ else 0
end Eig
section Unitary
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
open ReciprocityTheory.Aut
abbrev GAf : Type := ↥(GA L n)
def princAt (v : HeightOneSpectrum (𝓞 L⁺)) (c : ℕ) : Subgroup (GL (Fin n) (v.adicCompletion L⁺)) :=
  Formalism.UG.princ (v.adicCompletionIntegers L⁺).subtype (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L⁺) ^ c)
structure LevelDatum where
  ι : Type
  fin : Finite ι
  s : ι → SplitPlace L
  H : ∀ a, Subgroup (GL (Fin n) ((s a).v.adicCompletion L⁺))
  c : ι → ℕ
  open_ : ∀ a, princAt L n (s a).v (c a) ≤ H a
variable {L n}
def LevelDatum.U (D : LevelDatum L n) : Subgroup (GAf L n) := Level D.s D.H
def LevelDatum.B (D : LevelDatum L n) : Set (HeightOneSpectrum (𝓞 L⁺)) := Set.range fun a => (D.s a).v
variable (L n)
def IsAlgWeight {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) : Prop :=
  FiniteDimensional ℂ W ∧
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      LinearMap.toMatrix b b (ρ γ) = fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (P i j)
abbrev Forms {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W)
    (U : Subgroup (GAf L n)) : Submodule ℂ (GAf L n → W) :=
  Formalism.UG.AMF ℂ (GQ L n) U ρ
def tSet (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (j : ℕ) : Set (GAf L n) :=
  {x | TrivOutside {s.v} x ∧ ∃ a ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring,
    ∃ b ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring,
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) _) =
        (a : Matrix (Fin n) (Fin n) _) * Formalism.UG.diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _)}
open Classical in

def heckeFun {W : Type} [AddCommGroup W] [Module ℂ W] (U : Subgroup (GAf L n)) (D : Set (GAf L n))
    (f : GAf L n → W) : GAf L n → W :=
  fun g => ∑ᶠ c : GAf L n ⧸ U, if (∃ x ∈ D, (x : GAf L n ⧸ U) = c) then f (g * c.out) else 0
open Classical in

def heckeEnd {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W)
    (U : Subgroup (GAf L n)) (D : Set (GAf L n)) : Module.End ℂ (Forms L n ρ U) :=
  if h : ∃ φ : Module.End ℂ (Forms L n ρ U), ∀ f g, (φ f : GAf L n → W) g = heckeFun L n U D f g
  then h.choose else 0
def tOp {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W)
    (U : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (j : ℕ) :
    Module.End ℂ (Forms L n ρ U) :=
  heckeEnd L n ρ U (tSet L n s ϖ j)
def IsUnif (v : HeightOneSpectrum (𝓞 L⁺)) (ϖ : v.adicCompletion L⁺) : Prop :=
  Valued.v ϖ = WithZero.exp (-1 : ℤ)
def heckeAlg {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W)
    (U : Subgroup (GAf L n)) (B : Set (HeightOneSpectrum (𝓞 L⁺))) :
    Subalgebra ℂ (Module.End ℂ (Forms L n ρ U)) :=
  Algebra.adjoin ℂ {t | ∃ (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (j : ℕ),
    s.v ∉ B ∧ IsUnif L s.v ϖ ∧ 1 ≤ j ∧ j ≤ n ∧ t = tOp L n ρ U s ϖ j}
def satPoly {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W}
    {U : Subgroup (GAf L n)} {B : Set (HeightOneSpectrum (𝓞 L⁺))} (x : heckeAlg L n ρ U B →ₐ[ℂ] ℂ)
    (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) : ℂ[X] :=
  X ^ n + ∑ j ∈ Finset.Icc 1 n,
    C ((-1 : ℂ) ^ j * (s.q : ℂ) ^ (j * (j - 1) / 2) * xval (heckeAlg L n ρ U B) x (tOp L n ρ U s ϖ j)) *
      X ^ (n - j)
end Unitary
section GeneralLinearIntegers
variable {L : Type} [Field L] [NumberField L]
abbrev qw (w : HeightOneSpectrum (𝓞 L)) : ℕ := Formalism.ConjugateSelfDual.normV w
def dualPoly (P : ℂ[X]) (c : ℂ) : ℂ[X] :=
  C (P.coeff 0)⁻¹ * ∑ i ∈ Finset.range (P.natDegree + 1), C (P.coeff i * c ^ i) * X ^ (P.natDegree - i)
def PolHecke [IsCMField L] {a : ℕ} (S : Formalism.ConjugateSelfDual.CuspSpectrum L a) (π : S.Rep) (m : ℤ) : Prop :=
  ∀ᶠ w in cofinite, ∀ w' : HeightOneSpectrum (𝓞 L),
    w'.asIdeal = w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj L : 𝓞 L →+* 𝓞 L) →
    S.hecke π w' = dualPoly (S.hecke π w) ((qw w : ℂ) ^ m)
def chiVal (S : Formalism.ConjugateSelfDual.CuspSpectrum L 1) (ν : S.Rep) (w : HeightOneSpectrum (𝓞 L)) : ℂ :=
  -(S.hecke ν w).coeff 0
structure Part (S : Formalism.ConjugateSelfDual.SpectrumFamily) (L : Type) [Field L] [NumberField L] where
  a : ℕ
  π : (S L a).Rep
  d : ℕ
  t : ℤ
  ν : (S L 1).Rep
def partHecke {S : Formalism.ConjugateSelfDual.SpectrumFamily} (p : Part S L) (w : HeightOneSpectrum (𝓞 L)) : ℂ[X] :=
  ∏ k ∈ Finset.range p.d, ((S L p.a).hecke p.π w).scaleRoots
    (chiVal (S L 1) p.ν w * ((Real.sqrt (qw w : ℝ) : ℝ) : ℂ) ^ (p.t + p.d - 1 - 2 * (k : ℤ)))
def isoHecke {S : Formalism.ConjugateSelfDual.SpectrumFamily} (P : List (Part S L)) (w : HeightOneSpectrum (𝓞 L)) : ℂ[X] :=
  (P.map fun p => partHecke p w).prod
end GeneralLinearIntegers
open ReciprocityTheory.Aut in

def GoodCM (L : Type) [Field L] [NumberField L] [IsCMField L] : Prop :=
  (∀ w : HeightOneSpectrum (𝓞 L),
    w.asIdeal.ramificationIdx (𝓞 (NumberField.maximalRealSubfield L)) = 1) ∧
  ∀ v : HeightOneSpectrum (𝓞 (NumberField.maximalRealSubfield L)),
    (¬ ∃ s : SplitPlace L, s.v = v) → ((2 : ℕ) : 𝓞 (NumberField.maximalRealSubfield L)) ∉ v.asIdeal
end Formalism.AUTREP


