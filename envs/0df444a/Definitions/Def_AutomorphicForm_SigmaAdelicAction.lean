-- Prove2me | Definitions.Def_AutomorphicForm_SigmaAdelicAction
-- name    : AutomorphicForm_SigmaAdelicAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/92caf3ee-7584-5fc5-a4d7-ada199814b45
-- title:
--   Galois twisting of adelic GL2​ functions
-- statement:
--   The standing context is a field $F$, a number field $E$ with an $F$-algebra structure, and a datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E`](../def/M4aHerbrand_IdeleClassVocab.html#L28): a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $E \simeq_{\mathrm{alg}[F]} E$ to the ring automorphisms of the adele ring $\mathbb{A}_E =$ `AdeleRing (𝓞 E) E`, each continuous, and compatible with the principal embedding in the sense that $D.\mathrm{act}\,\sigma$ applied to the image of $x \in E$ is the image of $\sigma x$. Three definitions are made. First, `sigmaAdelicAct F E D σ` is the monoid endomorphism of $\mathrm{GL}_2(\mathbb{A}_E)$ obtained by applying the ring homomorphism underlying $D.\mathrm{act}\,\sigma$ to matrix entries. Second, for a complex-valued function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_E)$, the twist `sigmaSectionActOn F E D σ φ` is the precomposition $\varphi \circ \mathrm{sigmaAdelicAct}\,\sigma$. Third, given any measurable-space structure on $\mathrm{GL}_2(\mathbb{A}_E)$ and any measure $\nu_K$ on it, `sigmaPairingOn F E D νK σ φ` is the Bochner integral $\int \varphi(k)\,\overline{\varphi^{\sigma}(k)}\,d\nu_K$, with $\varphi^{\sigma}$ the above twist and the bar complex conjugation; no Haar or compactness condition is imposed on $\nu_K$, which is a parameter to be supplied by the user.
--
--   The accompanying lemmas record that the family $\sigma \mapsto \mathrm{sigmaAdelicAct}\,\sigma$ sends $1$ to the identity and $\sigma\tau$ to the composite of the endomorphisms attached to $\sigma$ and $\tau$ (stated as separate lemmas rather than bundled into an action), that each $\mathrm{sigmaAdelicAct}\,\sigma$ is continuous, and that on the image of $\mathrm{GL}_2(E)$ it agrees with entrywise application of $\sigma$. On the analytic side, the twist by $1$ is the identity on functions, the pairing at $\sigma = 1$ is $\int \varphi\,\overline{\varphi}\,d\nu_K$, and the pairing of the zero function vanishes. A degenerate instance with $E = F = \mathbb{Q}$ and the trivial descent is also recorded.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, `Matrix.GeneralLinearGroup.map` and the Bochner integral used here; the Galois action on the adeles packaged as [`M4aHerbrand.IdeleGaloisDescent`](../def/M4aHerbrand_IdeleClassVocab.html#L28), and the resulting twisting operations on complex-valued functions on $\mathrm{GL}_2$ of the adeles, are the project's own notions.
--
--   **Where it is used.** This module fixes the vocabulary for Galois conjugation of adelic objects in two variables: the entrywise action of $\mathrm{Gal}$-type automorphisms on $\mathrm{GL}_2(\mathbb{A}_E)$, the induced twist $\varphi \mapsto \varphi^{\sigma}$ of complex-valued functions, and an integral pairing of a function against its twist, together with the compatibility of the action with the global points $\mathrm{GL}_2(E)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SigmaAdelicAction.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

variable (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)

def sigmaAdelicAct (σ : E ≃ₐ[F] E) :
    Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) →*
      Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) :=
  Matrix.GeneralLinearGroup.map (D.act σ : RingAut (AdeleRing (𝓞 E) E)).toRingHom

def sigmaSectionActOn (σ : E ≃ₐ[F] E)
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ) :
    Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ :=
  φ ∘ (sigmaAdelicAct F E D σ)

def sigmaPairingOn
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E))]
    (νK : MeasureTheory.Measure (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E)))
    (σ : E ≃ₐ[F] E)
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ) : ℂ :=
  ∫ k, φ k * starRingEnd ℂ (sigmaSectionActOn F E D σ φ k) ∂νK

theorem sigmaAdelicAct_one : sigmaAdelicAct F E D 1 = MonoidHom.id _ := by
  ext g i j
  show ((D.act 1 : RingAut _).toRingHom : AdeleRing (𝓞 E) E → _) (g.val i j) = g.val i j
  rw [D.act.map_one]
  rfl

theorem sigmaAdelicAct_mul (σ τ : E ≃ₐ[F] E) :
    sigmaAdelicAct F E D (σ * τ) = (sigmaAdelicAct F E D σ).comp (sigmaAdelicAct F E D τ) := by
  ext g i j
  show ((D.act (σ * τ) : RingAut _).toRingHom : AdeleRing (𝓞 E) E → _) (g.val i j) =
    ((D.act σ : RingAut _).toRingHom : _ → _)
      (((D.act τ : RingAut _).toRingHom : _ → _) (g.val i j))
  rw [D.act.map_mul]
  rfl

theorem continuous_sigmaAdelicAct (σ : E ≃ₐ[F] E) :
    Continuous (sigmaAdelicAct F E D σ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Continuous.matrix_map (Units.continuous_val) (D.continuous_act σ)
  · exact Continuous.matrix_map (Units.continuous_coe_inv) (D.continuous_act σ)

theorem sigmaAdelicAct_globalPoints (σ : E ≃ₐ[F] E)
    (g : Matrix.GeneralLinearGroup (Fin 2) E) :
    sigmaAdelicAct F E D σ
        (Matrix.GeneralLinearGroup.map (algebraMap E (AdeleRing (𝓞 E) E)) g) =
      Matrix.GeneralLinearGroup.map (algebraMap E (AdeleRing (𝓞 E) E))
        (Matrix.GeneralLinearGroup.map (σ : E →+* E) g) := by
  ext i j
  exact D.compat σ (g.val i j)

theorem sigmaSectionActOn_one
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ) :
    sigmaSectionActOn F E D 1 φ = φ := by
  ext g
  show φ (sigmaAdelicAct F E D 1 g) = φ g
  rw [sigmaAdelicAct_one]
  rfl

theorem sigmaPairingOn_one
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E))]
    (νK : MeasureTheory.Measure (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E)))
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ) :
    sigmaPairingOn F E D νK 1 φ = ∫ k, φ k * starRingEnd ℂ (φ k) ∂νK := by
  unfold sigmaPairingOn
  rw [sigmaSectionActOn_one]

theorem sigmaPairingOn_zero
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E))]
    (νK : MeasureTheory.Measure (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E)))
    (σ : E ≃ₐ[F] E) :
    sigmaPairingOn F E D νK σ 0 = 0 := by
  unfold sigmaPairingOn
  simp only [Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]

section Inhabitant

example :
    haveI : Subsingleton (ℚ ≃ₐ[ℚ] ℚ) :=
      ⟨fun a b => AlgEquiv.ext fun x => (a.commutes x).trans (b.commutes x).symm⟩
    sigmaAdelicAct ℚ ℚ (M4aHerbrand.identityDescent (𝓞 ℚ) ℚ ℚ) 1 = MonoidHom.id _ :=
  sigmaAdelicAct_one ℚ ℚ _

end Inhabitant

end AutomorphicForm


