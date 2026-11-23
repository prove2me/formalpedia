-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsSmoothTwAct
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsSmoothTwAct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:14.568385+00:00
-- url     : https://prove2.me/theorems/cbaac2fe-28fc-4df5-9894-f0d0fcaa1d2f
-- title:
--   Is Smooth Tw Act
-- statement:
--   Definitions and structural lemmas for Is Smooth Tw Act, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsSmoothTwAct.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Gwa2.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}
noncomputable def UpperTheory.Reformulated.B.Gwa2.twKer :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      Submodule.span k
        {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[k] V) (↑n : G) : V → V) v - (↑((ψ : ↥N → kˣ) n) : k) • v}
@[reducible] noncomputable def UpperTheory.Reformulated.B.Gwa2.TwJacquet :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Type :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      V ⧸ UpperTheory.Reformulated.B.Gwa2.twKer ρ N ψ
theorem UpperTheory.Reformulated.B.Gwa2.aux4 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (m : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m)) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs m
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  obtain ⟨h, hθ⟩ := hs m n
  refine Submodule.subset_span ⟨⟨_, h⟩, ρ (s m) v, ?_⟩
  have key : ρ (s m * (n : G) * (s m)⁻¹) (ρ (s m) v) = ρ (s m) (ρ (n : G) v) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]
  rw [hθ, map_sub, map_smul, ← key]
theorem UpperTheory.Reformulated.B.Gwa2.aux5 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        Submodule.span ℂ
            {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
          Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M))) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  exact UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs 1
theorem UpperTheory.Reformulated.B.Gwa2.aux6 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M)))
          (UpperTheory.Reformulated.B.Gwa2.aux5 ρ N θ s hs) =
        (1 : UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s 1) v) = Submodule.Quotient.mk v
  rw [map_one, map_one, Module.End.one_apply]
theorem UpperTheory.Reformulated.B.Gwa2.aux7 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (a b : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b))) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  exact UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs (a * b)
theorem UpperTheory.Reformulated.B.Gwa2.aux8 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n)
      (a b : M),
      (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b)))
          (UpperTheory.Reformulated.B.Gwa2.aux7 ρ N θ s hs a b) =
        (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) a))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs a) *
          (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) b))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs b) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s (a * b)) v) = Submodule.Quotient.mk (ρ (s a) (ρ (s b) v))
  rw [map_mul, map_mul, Module.End.mul_apply]
noncomputable def UpperTheory.Reformulated.B.Gwa2.twAct :
    {G V : Type} →
      [inst : Group G] →
        [inst_1 : AddCommGroup V] →
          [inst_2 : _root_.Module ℂ V] →
            (ρ : Representation ℂ G V) →
              (N : Subgroup G) →
                (θ : ↥N →* ℂˣ) →
                  {M : Type} →
                    [inst_3 : Group M] →
                      (s : M →* G) →
                        (∀ (m : M) (n : ↥N),
                            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
                              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
                          Representation ℂ M (UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ) :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (N : Subgroup G)
        (θ : ↥N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
        (hs :
          ∀ (m : M) (n : ↥N),
            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) ↦
      {
        toFun := fun (m : M) ↦
          (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs m),
        map_one' := UpperTheory.Reformulated.B.Gwa2.aux6 ρ N θ s hs, map_mul' := UpperTheory.Reformulated.B.Gwa2.aux8 ρ N θ s hs :
        M →* UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ }


