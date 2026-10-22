-- Prove2me | Definitions.Def_LieSuperCStar_Correspondence_Setting
-- name    : LieSuperCStar_Correspondence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:15.771598+00:00
-- url     : https://prove2.me/theorems/3ad9cac8-9963-4b8f-b642-dd30be5c8ed5
-- title:
--   Definitions 2.1 and 2.3, §§3–6 — Lie supergroup representations and their non-unital C*-algebra
-- statement:
--   Let $(G,\mathfrak g)$ be a finite-dimensional real Lie supergroup, where $\mathfrak g=\mathfrak g_{\bar0}\oplus\mathfrak g_{\bar1}$ and $\mathfrak g_{\bar0}=\operatorname{Lie}(G)$. The shared setting defines a graded unitary representation $(\pi,\rho^\pi,\mathcal H)$, the smooth orbit space $\mathcal H^\infty$, test functions on $G_\varepsilon$, the represented algebraic crossed product, its $C^*$-completion $\mathcal A(G,\mathfrak g)$, nondegenerate *-representations, and even bounded intertwiners.
--
--   The generator represented by a word $D=x_1\cdots x_k$ and test function $f$ acts as
--
--   $$
--   \widehat\pi(D\otimes f)v=\rho^\pi(x_1)\cdots\rho^\pi(x_k)\pi(f)v.
--   $$
--
--   These definitions give every milestone and the category-equivalence goal one common interpretation. In particular, the odd action is defined on $\mathcal H^\infty$ itself, while $\mathcal A$ is generated from the Lie supergroup data independently of any chosen representation.
--
--   **Formalization Note** Smoothness means $C^\infty$, not real analyticity. The test space is a pair of smooth compactly supported functions on $G$; $U(\mathfrak g_{\mathbb C})$ is represented by words. The universal product ranges over Hilbert spaces in `Type`, rather than a set of cyclic equivalence classes. Its star subalgebra is non-unital. Integrated actions are vector integrals, and a distinguished zero branch in `genOp` is used only when an input is not smooth; Gårding smoothing is needed to show this branch is absent for test functions.
-- source:
--   Neeb–Salmasian, C*-algebras and direct integral decomposition for Lie supergroups, arXiv:1506.01558v1, pp. 3–9, 11–13, Definitions 2.1, 2.3, equations (3)–(6), (12), (13), (18)–(21)

import Mathlib
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P09

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace LieSuperCStar.Correspondence

variable {E G F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

abbrev EvenLie (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : Type) [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(ℝ, E) ∞ G] := GroupLieAlgebra 𝓘(ℝ, E) G

abbrev SuperLie (E G F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(ℝ, E) ∞ G] := EvenLie E G × F

/-- The even adjoint action is the derivative of conjugation. -/
def Ad0 (g : G) : EvenLie E G →L[ℝ] EvenLie E G :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => g * h * g⁻¹) 1

/-- Definition 2.1, expressed as a finite-dimensional Harish-Chandra pair. -/
structure HCPair (E G F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
    [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] where
  act : EvenLie E G →ₗ[ℝ] F →ₗ[ℝ] F
  obr : F →ₗ[ℝ] F →ₗ[ℝ] EvenLie E G
  Ad1 : G →* (F ≃L[ℝ] F)
  obr_symm : ∀ y z, obr y z = obr z y
  act_bracket : ∀ x x' y, act ⁅x, x'⁆ y = act x (act x' y) - act x' (act x y)
  obr_equivariant : ∀ x y z, ⁅x, obr y z⁆ = obr (act x y) z + obr y (act x z)
  odd_jacobi : ∀ y, act (obr y y) y = 0
  Ad1_smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] F) ∞
    (fun g : G => (Ad1 g : F →L[ℝ] F))
  Ad1_act : ∀ g x y, Ad1 g (act x y) = act (Ad0 g x) (Ad1 g y)
  Ad0_obr : ∀ g y z, Ad0 g (obr y z) = obr (Ad1 g y) (Ad1 g z)
  dAd1 : ∀ x y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun g : G => Ad1 g y) 1 x = act x y

/-- The smooth orbit vectors, as a complex submodule of the Hilbert space. -/
def smoothVectors {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ H where
  carrier := {v | QAlgorithms.Papers.Independent.Renew46.P09.HasSmoothOrbit
    (E := E) (fun g : G => π g) v}
  zero_mem' := by
    simpa only [Set.mem_setOf_eq, QAlgorithms.Papers.Independent.Renew46.P09.HasSmoothOrbit,
      map_zero] using
      (contMDiff_const : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (fun _ : G => (0 : H)))
  add_mem' := by
    intro v w hv hw
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (fun g : G => π g v) at hv
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (fun g : G => π g w) at hw
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (fun g : G => π g (v + w))
    convert hv.add hw using 1
    funext g
    simpa only [Pi.add_apply] using (map_add (π g) v w)
  smul_mem' := by
    intro c v hv
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (fun g : G => π g v) at hv
    let T : H →L[ℝ] H := (c • ContinuousLinearMap.id ℂ H).restrictScalars ℝ
    have hT := T.contMDiff.comp hv
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (fun g : G => π g (c • v))
    convert hT using 1
    funext g
    simp [T]

/-- Definition 2.3. The odd operators act on smooth vectors themselves. -/
structure UnitaryRep (hc : HCPair E G F) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  π : G →* (H ≃ₗᵢ[ℂ] H)
  P : H →L[ℂ] H
  ρ : SuperLie E G F →ₗ[ℝ] Module.End ℂ (smoothVectors (E := E) π)
  cont : ∀ v : H, Continuous (fun g : G => π g v)
  dense : Dense (smoothVectors (E := E) π : Set H)
  P_sq : P * P = 1
  P_sa : IsSelfAdjoint P
  P_comm : ∀ g v, P (π g v) = π g (P v)
  P_smooth : ∀ v : smoothVectors (E := E) π, P (v : H) ∈ smoothVectors (E := E) π
  even_parity : ∀ x (v : smoothVectors (E := E) π),
    P ((ρ (x, 0) v : smoothVectors (E := E) π) : H) =
      ((ρ (x, 0) ⟨P v, P_smooth v⟩ : smoothVectors (E := E) π) : H)
  odd_parity : ∀ y (v : smoothVectors (E := E) π),
    P ((ρ (0, y) v : smoothVectors (E := E) π) : H) =
      -((ρ (0, y) ⟨P v, P_smooth v⟩ : smoothVectors (E := E) π) : H)
  even_bracket : ∀ x x' (v : smoothVectors (E := E) π),
    ρ (⁅x, x'⁆, 0) v = ρ (x, 0) (ρ (x', 0) v) - ρ (x', 0) (ρ (x, 0) v)
  mixed_bracket : ∀ x y (v : smoothVectors (E := E) π),
    ρ (0, hc.act x y) v = ρ (x, 0) (ρ (0, y) v) - ρ (0, y) (ρ (x, 0) v)
  odd_bracket : ∀ y z (v : smoothVectors (E := E) π),
    ρ (hc.obr y z, 0) v = ρ (0, y) (ρ (0, z) v) + ρ (0, z) (ρ (0, y) v)
  deriv : ∀ x (v : smoothVectors (E := E) π),
    ((ρ (x, 0) v : smoothVectors (E := E) π) : H) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (fun g : G => π g (v : H)) 1 x
  symm : ∀ y (v w : smoothVectors (E := E) π),
    inner ℂ (((ρ (0, y) v : smoothVectors (E := E) π) : H)) (w : H) =
      inner ℂ (v : H) ((-Complex.I) • (((ρ (0, y) w : smoothVectors (E := E) π) : H)))
  covar : ∀ g y (v w : smoothVectors (E := E) π), (w : H) = π g (v : H) →
    π g (((ρ (0, y) v : smoothVectors (E := E) π) : H)) =
      (((ρ (0, hc.Ad1 g y) w : smoothVectors (E := E) π) : H))

/-- One component of a compactly supported smooth function on G × {1, ε}. -/
def IsTestFn (f : G → ℂ) : Prop :=
  ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f

abbrev TestPair (G : Type) := (G → ℂ) × (G → ℂ)

/-- The integrated action of the two components of a test function on G × {1, ε}. -/
def piInt {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (μ : Measure G) {hc : HCPair E G F} (π : UnitaryRep hc H)
    (f : TestPair G) (v : H) : H :=
  QAlgorithms.Papers.Independent.Renew46.P09.integratedVector μ (fun g => π.π g) f.1 v +
    QAlgorithms.Papers.Independent.Renew46.P09.integratedVector μ
      (fun g => π.π g) f.2 (π.P v)

/-- An enveloping-algebra word acts on smooth vectors. -/
def wordAct {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {hc : HCPair E G F} (π : UnitaryRep hc H) :
    List (SuperLie E G F) → Module.End ℂ (smoothVectors (E := E) π.π)
  | [] => 1
  | x :: xs => π.ρ x * wordAct π xs

/-- The operator represented by a word and a test pair. Gårding's theorem makes the
    smooth-vector branch hold for test functions. -/
def genOp {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (μ : Measure G) {hc : HCPair E G F} (π : UnitaryRep hc H)
    (xs : List (SuperLie E G F)) (f : TestPair G) (v : H) : H := by
  classical
  exact
  if h : piInt μ π f v ∈ smoothVectors (E := E) π.π then
    ((wordAct π xs ⟨piInt μ π f v, h⟩ : smoothVectors (E := E) π.π) : H)
  else 0

/-- All Type-small Hilbert representations of this Harish-Chandra pair. -/
structure RepIdx (hc : HCPair E G F) : Type 1 where
  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  rep : UnitaryRep hc H

attribute [instance] RepIdx.nacg RepIdx.ips RepIdx.cs

abbrev Big (hc : HCPair E G F) :=
  lp (fun r : RepIdx hc => r.H →L[ℂ] r.H) ∞

/-- A uniformly bounded family representing a generator of the crossed product. -/
def IsGen (hc : HCPair E G F) (μ : Measure G) (a : Big hc)
    (xs : List (SuperLie E G F)) (f : TestPair G) : Prop :=
  IsTestFn (E := E) f.1 ∧ IsTestFn (E := E) f.2 ∧
    ∀ (r : RepIdx hc) (v : r.H), a r v = genOp μ r.rep xs f v

def gens (hc : HCPair E G F) (μ : Measure G) : Set (Big hc) :=
  {a | ∃ xs f, IsGen hc μ a xs f}

/-- The image of the algebraic crossed product in the universal representation family. -/
def A0 (hc : HCPair E G F) (μ : Measure G) : Submodule ℂ (Big hc) :=
  Submodule.span ℂ (gens hc μ)

/-- The completion of the represented crossed product as a non-unital C*-algebra. -/
def CStarAlg (hc : HCPair E G F) (μ : Measure G) :
    NonUnitalStarSubalgebra ℂ (Big hc) :=
  (NonUnitalStarAlgebra.adjoin ℂ (gens hc μ)).topologicalClosure

/-- A canonical generator when it exists; otherwise the zero family. -/
def genElt (hc : HCPair E G F) (μ : Measure G)
    (xs : List (SuperLie E G F)) (f : TestPair G) : Big hc := by
  classical
  exact
  if h : ∃ a : Big hc, IsGen hc μ a xs f then Classical.choose h else 0

/-- The universal family of group operators. -/
def uG (hc : HCPair E G F) (g : G) : Big hc :=
  ⟨(fun r : RepIdx hc =>
      letI : NormedAddCommGroup r.H := r.nacg
      letI : InnerProductSpace ℂ r.H := r.ips
      letI : CompleteSpace r.H := r.cs
      (r.rep.π g).toLinearIsometry.toContinuousLinearMap), by
    apply memℓp_infty
    refine ⟨1, ?_⟩
    rintro _ ⟨r, rfl⟩
    letI : NormedAddCommGroup r.H := r.nacg
    letI : InnerProductSpace ℂ r.H := r.ips
    letI : CompleteSpace r.H := r.cs
    exact (r.rep.π g).toLinearIsometry.norm_toContinuousLinearMap_le⟩

/-- The universal parity family. -/
def uEps (hc : HCPair E G F) : Big hc :=
  ⟨(fun r : RepIdx hc => r.rep.P), by
    apply memℓp_infty
    refine ⟨1, ?_⟩
    rintro _ ⟨r, rfl⟩
    have hsq : ‖r.rep.P‖ * ‖r.rep.P‖ = ‖(1 : r.H →L[ℂ] r.H)‖ := by
      rw [← CStarRing.norm_star_mul_self, r.rep.P_sa, r.rep.P_sq]
    have hone : ‖(1 : r.H →L[ℂ] r.H)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    nlinarith [norm_nonneg r.rep.P]⟩

/-- Nondegeneracy means that the represented algebra generates a dense subspace. -/
def IsNondegenerate {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {hc : HCPair E G F} {μ : Measure G}
    (Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  Dense (Submodule.span ℂ (⋃ a : CStarAlg hc μ, Set.range (Ψ a)) : Set H)

/-- Equation (12), shared by the two directions of the correspondence. -/
def Corresponds {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {hc : HCPair E G F} {μ : Measure G}
    (π : UnitaryRep hc H) (Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ xs f (a : CStarAlg hc μ), IsGen hc μ (a : Big hc) xs f →
    ∀ v : H, Ψ a v = genOp μ π xs f v

/-- Even bounded operators intertwining both the group and the derived superalgebra actions. -/
def IsIntertwiner {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {hc : HCPair E G F}
    (π : UnitaryRep hc H) (σ : UnitaryRep hc K) (T : H →L[ℂ] K) : Prop :=
  (∀ g v, T (π.π g v) = σ.π g (T v)) ∧
  (∀ v, T (π.P v) = σ.P (T v)) ∧
  ∀ u (v : smoothVectors (E := E) π.π) (w : smoothVectors (E := E) σ.π),
    (w : K) = T (v : H) →
      T (((π.ρ u v : smoothVectors (E := E) π.π) : H)) =
        (((σ.ρ u w : smoothVectors (E := E) σ.π) : K))

/-- The algebraic subspace Ψ(A°)H of Section 6. -/
def CoreVectors {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {hc : HCPair E G F} {μ : Measure G}
    (Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ (a : CStarAlg hc μ) (w : H),
    (a : Big hc) ∈ A0 hc μ ∧ v = Ψ a w}

/-- The multiplier equation (18) for the G-component of (19). -/
def IsMultExt {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {hc : HCPair E G F} {μ : Measure G}
    (Ψ : CStarAlg hc μ →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (U : G →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∀ (g : G) (a : CStarAlg hc μ), ∃ b : CStarAlg hc μ,
    (b : Big hc) = uG hc g * (a : Big hc) ∧
      ∀ v : H, U g (Ψ a v) = Ψ b v

end LieSuperCStar.Correspondence


