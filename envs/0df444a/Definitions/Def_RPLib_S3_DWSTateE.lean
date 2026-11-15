-- Prove2me | Definitions.Def_RPLib_S3_DWSTateE
-- name    : RPLib_S3_DWSTateE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:26:06.463508+00:00
-- url     : https://prove2.me/theorems/14ee6259-5904-4f56-9cd7-b23c733de719
-- title:
--   Weight-two Ramanujan-Petersson library: quotients with duals, ideal kernels `E[I]`, the action `ι_I : O → End_{F_q}(E/E[I])` (b2)
-- statement:
--   Quotients with duals, ideal kernels `E[I]`, the action `ι_I : O → End_{F_q}(E/E[I])` (b2).
--
--   * `IsQuot G φ ψ n` : `φ : E → E'` is a surjective `F_q`-isogeny with kernel `G` and dual `ψ` (`ψ φ = [n]`,
--     `φ ψ = [n]`, `p ∤ n`); `exists_isQuot` (Vélu), `IsQuot.ext`, `IsQuot.factor` (universal property).
--   * `OAct R W L` : an `R`-structure on `E` (a ring isomorphism `ι` of `R` onto `End_{F_q}(E)`);
--     `OrdData.toOAct d` (the structure `θ d`, `R = Ord d`). Working with any `OAct` lets quotients be iterated.
--   * `kerI s I = E[I]`, `mem_kerI`, `ι_apply_mem_kerI`, `exists_quotI` (the quotient `E → E/E[I]` exists when `I`
--     contains an integer prime to `p`).
--   * `ιq hq : R →+* End(E')` with `ιq_spec : ιq α (φ P) = φ (ι α P)`, `ιq_mem` (lands in `End_{F_q}(E')`),
--     `ιq_injective`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateD

/-!
# S3-DWS-Tate, part E: quotients with duals, ideal kernels `E[I]`, the action `ι_I : O → End_{F_q}(E/E[I])` (b2)

* `IsQuot G φ ψ n` : `φ : E → E'` is a surjective `F_q`-isogeny with kernel `G` and dual `ψ` (`ψ φ = [n]`,
  `φ ψ = [n]`, `p ∤ n`); `exists_isQuot` (Vélu), `IsQuot.ext`, `IsQuot.factor` (universal property).
* `OAct R W L` : an `R`-structure on `E` (a ring isomorphism `ι` of `R` onto `End_{F_q}(E)`);
  `OrdData.toOAct d` (the structure `θ d`, `R = Ord d`). Working with any `OAct` lets quotients be iterated.
* `kerI s I = E[I]`, `mem_kerI`, `ι_apply_mem_kerI`, `exists_quotI` (the quotient `E → E/E[I]` exists when `I`
  contains an integer prime to `p`).
* `ιq hq : R →+* End(E')` with `ιq_spec : ιq α (φ P) = φ (ι α P)`, `ιq_mem` (lands in `End_{F_q}(E')`),
  `ιq_injective`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Quot

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W' : WeierstrassCurve F} [W'.IsElliptic]

/-- `φ : E → E'` is a separable `F_q`-quotient by `G` with dual `ψ` (`ψ ∘ φ = [n]`, `φ ∘ ψ = [n]`, `p ∤ n`). -/
structure IsQuot (G : AddSubgroup (Pt W L)) (φ : Pt W L →+ Pt W' L) (ψ : Pt W' L →+ Pt W L) (n : ℕ) :
    Prop where
  hn : (n : F) ≠ 0
  isog : IsIsog φ
  isogψ : IsIsog ψ
  ker : ∀ S, φ S = 0 ↔ S ∈ G
  surj : Function.Surjective φ
  dual1 : ∀ P, ψ (φ P) = n • P
  dual2 : ∀ Q, φ (ψ Q) = n • Q
  frob : ∀ P, φ (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (φ P)
  frobψ : ∀ Q, ψ (RPLib.EllFq.frob W' L Q) = RPLib.EllFq.frob W L (ψ Q)

omit [W'.IsElliptic] in
/-- **Vélu quotients with duals exist** for finite Frobenius-stable `G` with `p ∤ #G`. -/
theorem exists_isQuot (G : AddSubgroup (Pt W L)) [Finite G] (hG : (Nat.card G : L) ≠ 0)
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    ∃ W' : WeierstrassCurve F, ∃ _ : W'.IsElliptic, ∃ φ : Pt W L →+ Pt W' L, ∃ ψ : Pt W' L →+ Pt W L,
      IsQuot G φ ψ (Nat.card G) := by
  letI := Fintype.ofFinite G
  have hG' : (Fintype.card G : L) ≠ 0 := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨W', hE, φ, ψ, hφ, hψ, hker, hs, h1, h2, hf, hfψ, -⟩ := exists_quot_isog_dual G hG' hFr
  refine ⟨W', hE, φ, ψ, ⟨fun h => hG ?_, hφ, hψ, hker, hs, fun P => ?_, fun Q => ?_, hf, hfψ⟩⟩
  · rw [← map_natCast (algebraMap F L), h, map_zero]
  · rw [Nat.card_eq_fintype_card]; exact h1 P
  · rw [Nat.card_eq_fintype_card]; exact h2 Q

variable {G : AddSubgroup (Pt W L)} {φ : Pt W L →+ Pt W' L} {ψ : Pt W' L →+ Pt W L} {n : ℕ}

lemma IsQuot.ext (hq : IsQuot G φ ψ n) {W₁ : WeierstrassCurve F} {β₁ β₂ : Pt W' L →+ Pt W₁ L}
    (h : ∀ P, β₁ (φ P) = β₂ (φ P)) : β₁ = β₂ :=
  AddMonoidHom.ext fun Q => by obtain ⟨P, rfl⟩ := hq.surj Q; exact h P

lemma IsQuot.ext_end (hq : IsQuot G φ ψ n) {γ₁ γ₂ : AddMonoid.End (Pt W' L)}
    (h : ∀ P, γ₁ (φ P) = γ₂ (φ P)) : γ₁ = γ₂ :=
  AddMonoidHom.ext fun Q => by obtain ⟨P, rfl⟩ := hq.surj Q; exact h P

/-- **Universal property** of a quotient with dual: an isogeny killing `G` factors through `φ`. -/
theorem IsQuot.factor (hq : IsQuot G φ ψ n) {W₁ : WeierstrassCurve F} [W₁.IsElliptic]
    {α : Pt W L →+ Pt W₁ L} (hα : IsIsog α) (hker : ∀ T ∈ G, α T = 0) :
    ∃ β : Pt W' L →+ Pt W₁ L, IsIsog β ∧ (∀ P, β (φ P) = α P) ∧
      ((∀ P, α (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W₁ L (α P)) →
        ∀ Q, β (RPLib.EllFq.frob W' L Q) = RPLib.EllFq.frob W₁ L (β Q)) := by
  obtain ⟨B, hB⟩ := hα.comp hq.isogψ
  have hker' : ∀ Q : Pt W' L, n • Q = 0 → (α.comp ψ) Q = 0 := fun Q hQ =>
    hker _ ((hq.ker _).mp (by rw [hq.dual2, hQ]))
  obtain ⟨β, hβ, hβn, hβf⟩ := exists_factorN hq.hn hB hker'
  have hnL : (n : L) ≠ 0 := fun h => hq.hn (by
    apply (algebraMap F L).injective; rw [map_natCast, h, map_zero])
  have hφβ : ∀ P, β (φ P) = α P := fun P => by
    obtain ⟨R, rfl⟩ := nsmul_surjective (W := W) hnL P
    show β (φ (n • R)) = α (n • R)
    rw [map_nsmul, hβn, AddMonoidHom.comp_apply, hq.dual1]
  refine ⟨β, hβ, hφβ, fun hfr Q => hβf (fun Q => ?_) Q⟩
  simp only [AddMonoidHom.comp_apply]
  rw [hq.frobψ, hfr]

end Quot

section OActDef

variable {F : Type*} [Field F] [Fintype F]

attribute [local instance] finite_coordinateRing decEqFF

/-- An `R`-structure on `E`: a ring isomorphism `ι` of `R` onto `End_{F_q}(E)`. -/
structure OAct (R : Type*) [CommRing R] (W : WeierstrassCurve F) [W.IsElliptic] (L : Type*) [Field L]
    [Algebra F L] [IsAlgClosed L] [DecidableEq L] where
  ι : R →+* AddMonoid.End (Pt W L)
  inj : Function.Injective ι
  mem : ∀ a, ι a ∈ endFq W L
  surj : ∀ γ ∈ endFq W L, ∃ a, ι a = γ

end OActDef

section IdealKer

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W : WeierstrassCurve F} [W.IsElliptic]

/-- The `Ord d`-structure `θ d` on `E`. -/
noncomputable def OrdData.toOAct (d : OrdData W L) : OAct (Ord d) W L :=
  ⟨(θ d).toRingHom, θ_injective d, θ_mem d, fun _ h => exists_θ_eq d h⟩

lemma OrdData.toOAct_ι (d : OrdData W L) (a : Ord d) : d.toOAct.ι a = θ d a := rfl

lemma natCast_end_ne_zero {N : ℕ} (hNF : (N : F) ≠ 0) : (N : AddMonoid.End (Pt W L)) ≠ 0 := fun h =>
  hNF (by
    have h1 := intCast_eq_zero (W := W) (L := L) (r := (N : ℤ)) (by rw [Int.cast_natCast]; exact h)
    rw [Int.natCast_eq_zero.mp h1, Nat.cast_zero])

variable {R : Type*} [CommRing R]

lemma OAct.natCast_ne_zero (s : OAct R W L) {N : ℕ} (hNF : (N : F) ≠ 0) : (N : R) ≠ 0 := fun h =>
  natCast_end_ne_zero (W := W) (L := L) hNF (by rw [← map_natCast s.ι, h, map_zero])

lemma OAct.frob_comm (s : OAct R W L) (α : R) (P : Pt W L) :
    s.ι α (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W L (s.ι α P) :=
  (DFunLike.congr_fun (mem_endFq.mp (s.mem α)).2 P).symm

lemma OAct.ι_comm (s : OAct R W L) (α β : R) (P : Pt W L) : s.ι α (s.ι β P) = s.ι β (s.ι α P) := by
  show (s.ι α * s.ι β) P = (s.ι β * s.ι α) P
  rw [← map_mul, ← map_mul, mul_comm]

lemma OAct.natCast_apply (s : OAct R W L) (N : ℕ) (P : Pt W L) : s.ι (N : R) P = N • P := by
  rw [map_natCast]; rfl

variable (s : OAct R W L)

/-- The kernel `E[I] = ⋂_{α ∈ I} ker ι(α)` of an ideal `I` of `R`. -/
abbrev kerI (I : Ideal R) : AddSubgroup (Pt W L) := kerSet (s.ι '' (I : Set R))

variable {s}

lemma mem_kerI {I : Ideal R} {P : Pt W L} : P ∈ kerI s I ↔ ∀ α ∈ I, s.ι α P = 0 := by
  rw [mem_kerSet]
  constructor
  · intro h α hα; exact h _ ⟨α, hα, rfl⟩
  · rintro h _ ⟨α, hα, rfl⟩; exact h α hα

lemma natCast_mem_ι {I : Ideal R} {N : ℕ} (hN : (N : R) ∈ I) :
    (N : AddMonoid.End (Pt W L)) ∈ s.ι '' (I : Set R) := ⟨N, hN, map_natCast _ _⟩

lemma ι_apply_mem_kerI {I : Ideal R} {P : Pt W L} (hP : P ∈ kerI s I) (α : R) :
    s.ι α P ∈ kerI s I := mem_kerI.mpr fun β hβ => by
  have h := mem_kerI.mp hP (β * α) (I.mul_mem_right α hβ)
  rwa [map_mul] at h

lemma frob_mem_kerI {I : Ideal R} {P : Pt W L} (hP : P ∈ kerI s I) :
    RPLib.EllFq.frob W L P ∈ kerI s I :=
  frob_mem_kerSet_of_le (by rintro _ ⟨α, -, rfl⟩; exact s.mem α) hP

/-- **The quotient `E → E/E[I]` exists** when `I` contains an integer `N` prime to `p`. -/
theorem exists_quotI {I : Ideal R} {N : ℕ} (hN : (N : R) ∈ I) (hNF : (N : F) ≠ 0) :
    ∃ W' : WeierstrassCurve F, ∃ _ : W'.IsElliptic, ∃ φ : Pt W L →+ Pt W' L, ∃ ψ : Pt W' L →+ Pt W L,
      IsQuot (kerI s I) φ ψ (Nat.card (kerI s I)) := by
  haveI := finite_kerSet (natCast_mem_ι (s := s) hN) hNF
  exact exists_isQuot _ (card_kerSet_ne_zero (natCast_mem_ι (s := s) hN) hNF) fun T hT => frob_mem_kerI hT

variable {W' : WeierstrassCurve F} [W'.IsElliptic] {I : Ideal R}
  {φ : Pt W L →+ Pt W' L} {ψ : Pt W' L →+ Pt W L} {n : ℕ}

lemma exists_ι (hq : IsQuot (kerI s I) φ ψ n) (α : R) :
    ∃ γ : AddMonoid.End (Pt W' L), γ ∈ endFq W' L ∧ ∀ P, γ (φ P) = φ (s.ι α P) := by
  obtain ⟨Φ, hΦ⟩ := (mem_endRing).mp (mem_endFq.mp (s.mem α)).1
  obtain ⟨A, hA⟩ := hq.isog
  obtain ⟨γ, hγ, hγφ, hγf⟩ := hq.factor (HasGenI.comp_endo hA hΦ) (fun T hT => by
    show φ (s.ι α T) = 0
    rw [hq.ker]; exact ι_apply_mem_kerI hT α)
  have hf := hγf (fun P => by
    show φ (s.ι α (RPLib.EllFq.frob W L P)) = RPLib.EllFq.frob W' L (φ (s.ι α P))
    rw [s.frob_comm, hq.frob])
  obtain ⟨B, hB⟩ := hγ
  exact ⟨γ, mem_endFq.mpr ⟨(mem_endRing).mpr ⟨B, fun S => hB S⟩,
    AddMonoidHom.ext fun Q => (hf Q).symm⟩, hγφ⟩

/-- The endomorphism of `E/E[I]` induced by `α ∈ R`. -/
noncomputable def ιf (hq : IsQuot (kerI s I) φ ψ n) (α : R) : AddMonoid.End (Pt W' L) :=
  Classical.choose (exists_ι hq α)

lemma ιf_spec (hq : IsQuot (kerI s I) φ ψ n) (α : R) (P : Pt W L) :
    ιf hq α (φ P) = φ (s.ι α P) := (Classical.choose_spec (exists_ι hq α)).2 P

/-- **(b2) The ring homomorphism `ι_I : R → End(E/E[I])`**, `ι_I(α) ∘ φ = φ ∘ ι(α)`. -/
noncomputable def ιq (hq : IsQuot (kerI s I) φ ψ n) : R →+* AddMonoid.End (Pt W' L) where
  toFun := ιf hq
  map_one' := hq.ext_end fun P => by rw [ιf_spec, map_one]; rfl
  map_mul' α β := hq.ext_end fun P => by
    show ιf hq (α * β) (φ P) = ιf hq α (ιf hq β (φ P))
    rw [ιf_spec, ιf_spec, ιf_spec, map_mul]; rfl
  map_zero' := hq.ext_end fun P => by
    show ιf hq 0 (φ P) = 0
    rw [ιf_spec, map_zero]; exact map_zero φ
  map_add' α β := hq.ext_end fun P => by
    show ιf hq (α + β) (φ P) = ιf hq α (φ P) + ιf hq β (φ P)
    rw [ιf_spec, ιf_spec, ιf_spec, map_add]; exact map_add φ _ _

lemma ιq_spec (hq : IsQuot (kerI s I) φ ψ n) (α : R) (P : Pt W L) :
    ιq hq α (φ P) = φ (s.ι α P) := ιf_spec hq α P

lemma ιq_mem (hq : IsQuot (kerI s I) φ ψ n) (α : R) : ιq hq α ∈ endFq W' L :=
  (Classical.choose_spec (exists_ι hq α)).1

/-- `ι_I` is injective. -/
theorem ιq_injective [IsDomain R] (hq : IsQuot (kerI s I) φ ψ n) {N : ℕ} (hN : (N : R) ∈ I)
    (hNF : (N : F) ≠ 0) : Function.Injective (ιq hq) := by
  rw [injective_iff_map_eq_zero]
  intro α hα
  have h1 : ∀ P, s.ι ((N : R) * α) P = 0 := fun P => by
    have h2 : φ (s.ι α P) = 0 := by rw [← ιq_spec hq, hα]; rfl
    have h3 := mem_kerI.mp ((hq.ker _).mp h2) _ hN
    rwa [map_mul]
  have h4 : (N : R) * α = 0 := s.inj (by rw [map_zero]; exact AddMonoidHom.ext h1)
  exact (mul_eq_zero.mp h4).resolve_left (s.natCast_ne_zero hNF)

end IdealKer

end RPLib.DWS


