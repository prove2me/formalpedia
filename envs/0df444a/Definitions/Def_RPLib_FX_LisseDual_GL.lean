-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_GL
-- name    : RPLib_FX_LisseDual_GL
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T04:29:23.989704+00:00
-- url     : https://prove2.me/theorems/a226dfac-b897-586d-9da4-6096ff1557b3
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, glue lemmas
-- statement:
--   Glue lemmas of the lisse duality library for affine curves over a finite field: translations of the pure-Mathlib unramifiedness, prime-under and translated-ideal conditions into the library's (copied from the published `RPLib_F2_031`), and the cochain forms of the duality map `alphaM` (a pairing `lpair` on relative cocycles with its primitive, trace-formula, injectivity and surjectivity clauses).
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_FX_LisseDual_03

/-!
# Lisse Poincaré duality on an affine curve over a finite field: glue lemmas

Glue lemmas for the lisse duality theorem of the library series `RPLib_FX_LisseDual_*`: the helpers `unram_iff`,
`under_iff` and `mem_smul_iff` (copied from the published `RPLib_F2_031`), which translate the pure-Mathlib
unramifiedness, prime-under and translated-ideal conditions into the library's, and the cochain forms of the
duality map `alphaM`: `SW38B.lpair` with its primitive, trace-formula, injectivity and surjectivity clauses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace SW38B

open scoped Pointwise

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

theorem under_iff {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K]
    [IsFractionRing A K] {M L : IntermediateField K (AlgebraicClosure K)} (h : M ≤ L)
    [IsDedekindDomain (integralClosure A M)] [IsDedekindDomain (integralClosure A L)]
    (w : IsDedekindDomain.HeightOneSpectrum (integralClosure A L)) (x : integralClosure A M) :
    x ∈ (CdOne.underI A h w).asIdeal ↔
      ∃ y ∈ w.asIdeal, ((y : L) : AlgebraicClosure K) = ((x : M) : AlgebraicClosure K) := by
  show x ∈ w.asIdeal.comap (incl A K h) ↔ _
  rw [Ideal.mem_comap]
  constructor
  · intro hx
    exact ⟨_, hx, incl_val A K h x⟩
  · rintro ⟨y, hy, he⟩
    have : y = incl A K h x := Subtype.ext (Subtype.ext (he.trans (incl_val A K h x).symm))
    rwa [← this]

theorem mem_smul_iff {A K : Type} [CommRing A] [Field K] [Algebra A K] (R0 : Type) [CommRing R0]
    [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
    (g : Pi1 A K) (Q : Ideal (CurveCoh.proChart A K R0)) (b : CurveCoh.proChart A K R0) :
    b ∈ g • Q ↔ ∃ c ∈ Q, (b : maxUnram A K) = g (c : maxUnram A K) := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hb
    refine ⟨_, hb, ?_⟩
    show (b : maxUnram A K) = g (g⁻¹ • (b : maxUnram A K))
    rw [← AlgEquiv.smul_def, smul_inv_smul]
  · rintro ⟨c, hc, he⟩
    have : g⁻¹ • b = c := Subtype.ext (by
      show g⁻¹ • (b : maxUnram A K) = c
      rw [he, ← AlgEquiv.smul_def, inv_smul_smul])
    rwa [this]


section Clauses

open CurveCoh CupDuality PerfectCx

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation Λ G Λ} {Γ : Subgroup G} {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {M : Type} [AddCommGroup M] [Module Λ M] {ρ : Representation Λ G M}

open Classical in
/-- The duality pairing on cochains: `alphaM` of the classes when both are cocycles, `0` otherwise. -/
noncomputable def lpair (hv : H2Van σ Γ ⊤) (DD : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G))
    (hρ : IsOpen (ρ.ker : Set G)) : (Γ → M) × (S → M) → (Γ → (M →ₗ[Λ] Λ)) → Λ := fun x d =>
  if h : x ∈ Z1c ρ Γ I ∧ d ∈ Z1 (ρ.linHom σ) Γ then
    alphaM hv (h2kEquiv DD hσ).toLinearMap ρ hρ (H1c.mk ρ Γ I ⟨x, h.1⟩) (H1.mk (ρ.linHom σ) Γ ⟨d, h.2⟩)
  else 0

theorem lpair_prim (hv : H2Van σ Γ ⊤) (hσ : IsOpen (σ.ker : Set G)) (hρ : IsOpen (ρ.ker : Set G))
    (c : Γ → M) (d : Γ → (M →ₗ[Λ] Λ)) (hc : c ∈ Z1 ρ Γ) (hd : d ∈ Z1 (ρ.linHom σ) Γ) :
    ∃ u : Γ → Λ, IsLocallyConstant u ∧
      ∀ g h : Γ, (ρ.linHom σ) g (d h) (c g) = σ g (u h) - u (g * h) + u g :=
  exists_prim (dualHyp hρ hσ hv) hc hd

theorem lpair_formula (hv : H2Van σ Γ ⊤) (DD : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G))
    (hρ : IsOpen (ρ.ker : Set G)) (x : (Γ → M) × (S → M)) (d : Γ → (M →ₗ[Λ] Λ)) (u : Γ → Λ)
    (hx : x ∈ Z1c ρ Γ I) (hd : d ∈ Z1 (ρ.linHom σ) Γ)
    (hu : IsLocallyConstant u ∧ ∀ g h : Γ, (ρ.linHom σ) g (d h) (x.1 g) = σ g (u h) - u (g * h) + u g) :
    lpair hv DD hσ hρ x d = ∑ s, (d (tG t s) (x.2 s) - u (tG t s)) := by
  rw [lpair, dif_pos ⟨hx, hd⟩, alphaM_apply, cupPair_mk,
    cupH_eq (dualHyp hρ hσ hv) ⟨x, hx⟩ ⟨d, hd⟩ u hu]
  rfl

theorem lpair_inj (hv : H2Van σ Γ ⊤) (DD : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G))
    (hρ : IsOpen (ρ.ker : Set G)) (hbij : Function.Bijective (alphaM hv (h2kEquiv DD hσ).toLinearMap ρ hρ))
    (x : (Γ → M) × (S → M)) (hx : x ∈ Z1c ρ Γ I)
    (h0 : ∀ d : Γ → (M →ₗ[Λ] Λ), d ∈ Z1 (ρ.linHom σ) Γ → lpair hv DD hσ hρ x d = 0) :
    ∃ m : M, (∀ g : Γ, x.1 g = ρ g m - m) ∧ ∀ s, x.2 s = m := by
  have hz : alphaM hv (h2kEquiv DD hσ).toLinearMap ρ hρ (H1c.mk ρ Γ I ⟨x, hx⟩) = 0 := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
    have h1 := h0 d.1 d.2
    rw [lpair, dif_pos ⟨hx, d.2⟩] at h1
    exact h1
  have h1 : H1c.mk ρ Γ I ⟨x, hx⟩ = 0 := hbij.1 (hz.trans (map_zero _).symm)
  have h2 := (Submodule.Quotient.mk_eq_zero _).1 h1
  exact ((mem_B1c ρ Γ I x).1 h2).2

theorem lpair_surj (hv : H2Van σ Γ ⊤) (DD : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G))
    (hρ : IsOpen (ρ.ker : Set G)) (hbij : Function.Bijective (alphaM hv (h2kEquiv DD hσ).toLinearMap ρ hρ))
    (f : (Γ → (M →ₗ[Λ] Λ)) → Λ)
    (hadd : ∀ d d' : Γ → (M →ₗ[Λ] Λ), d ∈ Z1 (ρ.linHom σ) Γ → d' ∈ Z1 (ρ.linHom σ) Γ →
      f (d + d') = f d + f d')
    (hsmul : ∀ (a : Λ) (d : Γ → (M →ₗ[Λ] Λ)), d ∈ Z1 (ρ.linHom σ) Γ → f (a • d) = a * f d)
    (hcob : ∀ φ : M →ₗ[Λ] Λ, f (fun g => (ρ.linHom σ) g φ - φ) = 0) :
    ∃ x : (Γ → M) × (S → M), x ∈ Z1c ρ Γ I ∧
      ∀ d : Γ → (M →ₗ[Λ] Λ), d ∈ Z1 (ρ.linHom σ) Γ → lpair hv DD hσ hρ x d = f d := by
  let f0 : Z1 (ρ.linHom σ) Γ →ₗ[Λ] Λ :=
    { toFun := fun d => f d
      map_add' := fun d d' => hadd d d' d.2 d'.2
      map_smul' := fun a d => hsmul a d d.2 }
  let φ : Module.Dual Λ (H1 (ρ.linHom σ) Γ) := Submodule.liftQ _ f0 (by
    intro d hd
    obtain ⟨-, m, hm⟩ := (mem_B1 _ Γ _).1 hd
    have he : (d : Γ → (M →ₗ[Λ] Λ)) = fun g : Γ => (ρ.linHom σ) g m - m := funext hm
    show f d = 0
    rw [he]
    exact hcob m)
  obtain ⟨X, hX⟩ := hbij.2 φ
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ X
  refine ⟨x, hx, fun d hd => ?_⟩
  rw [lpair, dif_pos ⟨hx, hd⟩]
  exact LinearMap.congr_fun hX (H1.mk (ρ.linHom σ) Γ ⟨d, hd⟩)

end Clauses

end SW38B
end RamanujanPetersson


