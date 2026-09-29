-- Prove2me | Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
-- name    : AutomorphicForm_TwistedGeometricRemainder
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/b98b2f97-9550-53be-8c33-45b0985dfda8
-- title:
--   Twisted geometric remainder of the trace formula
-- statement:
--   The module defines, for a finite Galois extension $L/K$ of number fields with a distinguished automorphism $\sigma$ generating the Galois group (the hypothesis `hgen` asserts that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$), a complex number [`AutomorphicForm.twistedGeometricRemainder`](../def/AutomorphicForm_TwistedGeometricRemainder.html#L26) attached to the following data: an idèle-Galois descent datum $D$ for $L/K$, two subsets $\Phi_L, \Phi_0$ of $\mathrm{GL}_2$ of the adèles of $L$, a measure $\nu_{Z_L}$ and a subset $\Omega_L$ of the idèles of $L$, a character $\xi_L$ of the full subgroup of the idèle group with values in $\mathbb{C}^\times$, and a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$. Its value is the [`HalfLine.intercept`](../def/Analysis_HalfLineIntercept.html#L12) of the function of a real parameter $R$ given by the difference of two terms. The first is the integral over $x \in \Phi_0$, against the adelic Haar measure on $\mathrm{GL}_2$, of the integral over $z \in \Omega_L$ against $\nu_{Z_L}$ of $\xi_L(z)$ times the truncation operator [`AutomorphicForm.lambdaT`](../def/AutomorphicForm_TruncationOperator.html#L48), formed from the cusp-pin data `productionPinsOf` for $\Phi_L$ at principal level intersected with the finite adelic subgroup and with Hecke generators and adelic box, applied with the unipotent family, the adelic height of $L$, cut-off $e^R$, to the $\sigma$-twisted adelic kernel of $\varphi$ in the variable $x$, evaluated at the central translate $z \cdot x$. The second is the same double integral over $x \in \Phi_L$ and $z \in \Omega_L$ of $\xi_L(z)$ times the finite sum over those $\delta \in \mathrm{GL}_2(L)$ whose twisted norm class (under `normClassMap` applied to the $\sigma$-conjugacy class of $\delta$) is the conjugacy class of some $\gamma \in \mathrm{GL}_2(K)$ lying in the elliptic cell (no eigenvalue in $K$) or the central cell (a scalar matrix), of $\varphi$ at $x^{-1}\,\delta\,\sigma(z x)$, where $\sigma$ acts through `sigmaAdelicAct` built from $D$.
--
--   The accompanying theorem `twistedGeometricRemainder_eq_of_forall_le_setIntegral_eq` states that this intercept is identified with a prescribed constant term. Under a long list of hypotheses — a finite set $T$ of finite places of $K$ disjoint from $S$ with $|T| \ge 2$, all places of $L$ above $T$ outside $S_L$, chosen extensions $w_v$ with $\sigma$-translated partners $w'$, uniformisers $\varpi_v$ with nonzero image, Hecke coset systems $r_{T,v}$ for the integral subgroup and the matrix $\mathrm{diag}(\varpi_v,1)$, central elements $z_v$ scalar of scalar $\varpi_v$, and the assumption that for every pair of exponent vectors $k, j$ and every $\varphi$ admitting the indicated semi-local factorisation with the Hecke-word components at places in $T$ the difference of the two integrals above equals $R \cdot \nu(k,j) + \mu(k,j)$ for all sufficiently large $R$ — the remainder equals $\mu(k,j)$ for any such $k, j, \varphi$. An `example` at the end exhibits the remainder in its intended geometric setting, where $\Phi_L$ and $\Phi_0$ are fundamental domains for $\mathrm{GL}_2(L)$ on the slab of idèle-norm of the determinant in $[\alpha,\beta]$, $\Phi_0$ is moreover covered by finitely many translates of a centre-cut Siegel set, $\Omega_L$ is a fundamental domain for $L^\times$ in the idèles, and $\xi_L$ is continuous and trivial on principal idèles.
--
--   **Relation to Mathlib.** Mathlib has no twisted (base-change) trace formula; the truncation operator, twisted adelic kernel, twisted norm classes and conjugacy cells used here are all project notions, built over Mathlib's adèle rings, Haar measures and `GL (Fin 2)`.
--
--   **Where it is used.** The twisted trace formula for a cyclic extension is the analytic engine behind cyclic base change for $\mathrm{GL}_2$, which in turn supports the Langlands–Tunnell theorem supplying the modularity of the residual representation at $3$ in the Frey–Serre–Ribet–Wiles argument. The remainder defined here isolates the $R$-independent part of the geometric side after truncation, along the elliptic and central conjugacy cells.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_TwistedGeometricRemainder.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_Analysis_HalfLineIntercept

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

def AutomorphicForm.twistedGeometricRemainder
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ΦL Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) : ℂ :=
  HalfLine.intercept (fun R : ℝ =>
    (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
    (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L)))

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.twistedGeometricRemainder_eq_of_forall_le_setIntegral_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (μ ν : (HeightOneSpectrum (𝓞 K) → ℕ) → (HeightOneSpectrum (𝓞 K) → ℕ) → ℂ) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      (∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → (
  ∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (@AutomorphicForm.lambdaT _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
        (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
  (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) +
      ((R : ℂ) * ν ks js + μ ks js)) →
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      AutomorphicForm.twistedGeometricRemainder K L D σ hgen ΦL Φ₀ νZL ΩL ξL φ = μ ks js := by
  intro T _ _ _ ws w' _ ϖs _ hϖs0 ns rTs _ zs _ hspan ks js φ φf hfac
  obtain ⟨R₀, hR⟩ := hspan ks js φ φf hfac
  unfold AutomorphicForm.twistedGeometricRemainder
  exact HalfLine.intercept_eq_of_forall_le_eq_add_mul ⟨R₀, fun R hle => sub_eq_iff_eq_add'.mpr (hR R hle)⟩

open AutomorphicForm in
open scoped TensorProduct.RightActions in

example
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (_hα : 0 < α)  (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (_hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (_hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (_SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (_hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (_hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (_S : Finset (HeightOneSpectrum (𝓞 K)))
    (_φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (_φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (_hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (_hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (_hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (_hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (_hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) : ℂ :=
  AutomorphicForm.twistedGeometricRemainder K L D σ hgen ΦL Φ₀ νZL ΩL ξL φ

end


