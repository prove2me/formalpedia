-- Prove2me | Definitions.Def_RPLib_F2_031
-- name    : RPLib_F2_031
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T12:40:37.008188+00:00
-- url     : https://prove2.me/theorems/b9f61940-e48c-46b8-a5ef-3b8951bcbf96
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 031 of 70 (hypothesis bridge for curve duality)
-- statement:
--   File 031 of 70 of the flat curve library: hypothesis bridge for curve duality. It restates the solution of the corresponding problem with the library's main theorem as an explicit hypothesis `MAIN`, together with the elementary translation lemmas it needs.
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_027

/-!
# Curve-duality library (flat edition, hypothesis bridge): the duality theorem on cochains

Companion of the curve-duality library (parts 1-71), whose main result is
`RamanujanPetersson.CupDuality.constDuality_S3_perfect`; it only needs the cohomological core (parts 2, 3 and 5 and
the public files `Def_RPLib_S4_GalCover`, `Def_RPLib_S4_CurveCohCurve`, `Def_RPLib_S4_CurveCohPair`). For a topological group `G`, a subgroup `Γ`, subgroups
`I s` (`s ∈ S`, `S` finite) and constant-coefficient data `DD` for a character `σ : G → Aut_Λ(Λ)` trivial on `Γ`,
this file defines the cup pairing on cochains `cpair` (the pairing of the cohomology classes of a compactly
supported 1-cocycle and a 1-cocycle, `0` off cocycles) and proves, in elementary cochain terms, the explicit formula
for it, its left and right nondegeneracy, that it identifies each side with the dual of the other, and its
compatibility with Frobenius twists. The helpers `unram_iff`, `under_iff` and `mem_smul_iff` restate the library's
predicates (unramified subextension, restriction of a place, Galois action on ideals) explicitly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CDBridge

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

section Coh

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

theorem memZ1_triv (c : Γ → Λ) : c ∈ CurveCoh.Z1 (Representation.trivial Λ G Λ) Γ ↔
    IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + c h := by
  rw [CurveCoh.mem_Z1]
  simp only [Representation.trivial_apply]

theorem memZ1_sigma (σ : Representation Λ G Λ) (htr : ∀ (g : Γ) (x : Λ), σ g x = x) (d : Γ → Λ) :
    d ∈ CurveCoh.Z1 σ Γ ↔ IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h := by
  rw [CurveCoh.mem_Z1]
  simp only [htr]

theorem memZ1c_triv (x : (Γ → Λ) × (S → Λ)) : x ∈ CurveCoh.Z1c (Representation.trivial Λ G Λ) Γ I ↔
    (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
      ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) := by
  rw [CurveCoh.mem_Z1c, memZ1_triv]
  simp only [Representation.trivial_apply, sub_self, and_assoc]

theorem isPrim_iff (σ : Representation Λ G Λ) (htr : ∀ (g : Γ) (x : Λ), σ g x = x) (c d u : Γ → Λ) :
    CupDuality.IsPrim σ σ (LinearMap.mul Λ Λ) Γ c d u ↔
      IsLocallyConstant u ∧ ∀ g h, c g * d h = u h - u (g * h) + u g := by
  simp only [CupDuality.IsPrim, CupDuality.cupCochain, LinearMap.mul_apply', htr]

theorem eq_of_memB1c (x : (Γ → Λ) × (S → Λ))
    (hx : x ∈ CurveCoh.B1c (Representation.trivial Λ G Λ) Γ I) : ∃ m : Λ, x = (0, fun _ => m) := by
  obtain ⟨-, m, hm1, hm2⟩ := hx
  refine ⟨m, Prod.ext (funext fun g => ?_) (funext hm2)⟩
  rw [hm1 g]
  simp

end Coh

section Clauses

open CurveCoh CupDuality

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation Λ G Λ} {Γ : Subgroup G} {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)}

open Classical in
/-- The cup pairing on cochains: the pairing of the classes of `x` and `d` when both are cocycles, `0` otherwise. -/
noncomputable def cpair (H : CupHyp (Representation.trivial Λ G Λ) σ σ (LinearMap.mul Λ Λ) Γ)
    (DD : ConstData σ Γ I t) : (Γ → Λ) × (S → Λ) → (Γ → Λ) → Λ := fun x d =>
  if hx : x ∈ Z1c (Representation.trivial Λ G Λ) Γ I ∧ d ∈ Z1 σ Γ then
    constPair H DD (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx.1⟩) (H1.mk σ Γ ⟨d, hx.2⟩)
  else 0

theorem cpair_mk (H : CupHyp (Representation.trivial Λ G Λ) σ σ (LinearMap.mul Λ Λ) Γ)
    (DD : ConstData σ Γ I t) {x : (Γ → Λ) × (S → Λ)} {d : Γ → Λ}
    (hx : x ∈ Z1c (Representation.trivial Λ G Λ) Γ I) (hd : d ∈ Z1 σ Γ) :
    cpair H DD x d =
      constPair H DD (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx⟩) (H1.mk σ Γ ⟨d, hd⟩) := by
  rw [cpair, dif_pos ⟨hx, hd⟩]

variable (H : CupHyp (Representation.trivial Λ G Λ) σ σ (LinearMap.mul Λ Λ) Γ)
  (DD : ConstData σ Γ I t) (htr : ∀ (g : Γ) (x : Λ), σ g x = x)

include H htr in
theorem clause_cup : ∀ c d : Γ → Λ, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + c h) →
    (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
    ∃ u : Γ → Λ, IsLocallyConstant u ∧ ∀ g h, c g * d h = u h - u (g * h) + u g := by
  intro c d hc hd
  obtain ⟨u, hu⟩ := exists_prim H ((memZ1_triv Γ c).2 hc) ((memZ1_sigma Γ σ htr d).2 hd)
  exact ⟨u, (isPrim_iff Γ σ htr c d u).1 hu⟩

include htr in
theorem clause_formula : ∀ (x : (Γ → Λ) × (S → Λ)) (d u : Γ → Λ),
    (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
      ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) →
    (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
    (IsLocallyConstant u ∧ ∀ g h, x.1 g * d h = u h - u (g * h) + u g) →
    cpair H DD x d = ∑ s, (x.2 s * d (tG t s) - u (tG t s)) := by
  intro x d u hx hd hu
  have hx' := (memZ1c_triv Γ I x).2 hx
  have hd' := (memZ1_sigma Γ σ htr d).2 hd
  rw [cpair_mk H DD hx' hd']
  exact constPair_mk H DD ⟨x, hx'⟩ ⟨d, hd'⟩ u ((isPrim_iff Γ σ htr x.1 d u).2 hu)

include htr in
theorem clause_left (hperf : (constPair H DD).IsPerfPair) : ∀ x : (Γ → Λ) × (S → Λ),
    (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
      ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) →
    (∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → cpair H DD x d = 0) →
    x.1 = 0 ∧ ∃ a : Λ, ∀ s, x.2 s = a := by
  intro x hx h0
  have hbl := LinearMap.IsPerfPair.bijective_left (constPair H DD)
  have hx' := (memZ1c_triv Γ I x).2 hx
  have hB : constPair H DD (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩) = 0 := by
    refine LinearMap.ext fun Y => ?_
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ Y
    have h1 := h0 d.1 ((memZ1_sigma Γ σ htr d.1).1 d.2)
    rw [cpair_mk H DD hx' d.2] at h1
    exact h1
  have hX : H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩ = 0 :=
    hbl.1 (hB.trans (map_zero _).symm)
  have hmem := (Submodule.Quotient.mk_eq_zero _).1 hX
  obtain ⟨m, hm⟩ := eq_of_memB1c Γ I x hmem
  subst hm
  exact ⟨rfl, m, fun _ => rfl⟩

include htr in
theorem clause_right (hperf : (constPair H DD).IsPerfPair) : ∀ d : Γ → Λ,
    (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
    (∀ x : (Γ → Λ) × (S → Λ),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) → cpair H DD x d = 0) →
    d = 0 := by
  intro d hd h0
  have hbr := LinearMap.IsPerfPair.bijective_right (constPair H DD)
  have hd' := (memZ1_sigma Γ σ htr d).2 hd
  have hB : (constPair H DD).flip (H1.mk σ Γ ⟨d, hd'⟩) = 0 := by
    refine LinearMap.ext fun X => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ X
    have h1 := h0 x.1 ((memZ1c_triv Γ I x.1).1 x.2)
    rw [cpair_mk H DD x.2 hd'] at h1
    exact h1
  have hY : H1.mk σ Γ ⟨d, hd'⟩ = 0 := hbr.1 (hB.trans (map_zero _).symm)
  obtain ⟨-, m, hm⟩ := (Submodule.Quotient.mk_eq_zero _).1 hY
  funext g
  have h1 : d g = σ g m - m := hm g
  rw [h1, htr g m, sub_self]
  rfl

include htr in
theorem clause_surjL (hperf : (constPair H DD).IsPerfPair) : ∀ f : (Γ → Λ) → Λ,
    (∀ d d' : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
      (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) → f (d + d') = f d + f d') →
    (∀ (a : Λ) (d : Γ → Λ), (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
      f (a • d) = a * f d) →
    ∃ x : (Γ → Λ) × (S → Λ),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) ∧
      ∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → cpair H DD x d = f d := by
  intro f hadd hsmul
  have hbl := LinearMap.IsPerfPair.bijective_left (constPair H DD)
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0 ⟨IsLocallyConstant.zero, fun _ _ => by simp⟩
      ⟨IsLocallyConstant.zero, fun _ _ => by simp⟩
    rw [add_zero] at h
    exact (add_eq_left.1 h.symm)
  let f0 : Z1 σ Γ →ₗ[Λ] Λ :=
    { toFun := fun d => f d.1
      map_add' := fun d d' => hadd d.1 d'.1 ((memZ1_sigma Γ σ htr _).1 d.2)
        ((memZ1_sigma Γ σ htr _).1 d'.2)
      map_smul' := fun a d => hsmul a d.1 ((memZ1_sigma Γ σ htr _).1 d.2) }
  let f00 := ((B1 σ Γ).comap (Z1 σ Γ).subtype).liftQ f0 (by
    intro d hd
    obtain ⟨-, m, hm⟩ := hd
    have : d.1 = 0 := funext fun g => by
      have h1 : d.1 g = σ g m - m := hm g
      rw [h1, htr g m, sub_self]
      rfl
    show f d.1 = 0
    rw [this, hf0])
  obtain ⟨X, hX⟩ := hbl.2 f00
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ X
  refine ⟨x.1, (memZ1c_triv Γ I x.1).1 x.2, fun d hd => ?_⟩
  have hd' := (memZ1_sigma Γ σ htr d).2 hd
  rw [cpair_mk H DD x.2 hd']
  exact LinearMap.congr_fun hX (H1.mk σ Γ ⟨d, hd'⟩)

include htr in
theorem clause_surjR (hperf : (constPair H DD).IsPerfPair) : ∀ f : (Γ → Λ) × (S → Λ) → Λ,
    (∀ x y : (Γ → Λ) × (S → Λ),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) →
      (IsLocallyConstant y.1 ∧ (∀ g h, y.1 (g * h) = y.1 g + y.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → y.1 g = 0) → f (x + y) = f x + f y) →
    (∀ (a : Λ) (x : (Γ → Λ) × (S → Λ)),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) → f (a • x) = a * f x) →
    (∀ a : Λ, f (0, fun _ => a) = 0) →
    ∃ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) ∧
      ∀ x : (Γ → Λ) × (S → Λ),
        (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
          ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) → cpair H DD x d = f x := by
  intro f hadd hsmul h0
  have hbr := LinearMap.IsPerfPair.bijective_right (constPair H DD)
  let f0 : Z1c (Representation.trivial Λ G Λ) Γ I →ₗ[Λ] Λ :=
    { toFun := fun x => f x.1
      map_add' := fun x y => hadd x.1 y.1 ((memZ1c_triv Γ I _).1 x.2) ((memZ1c_triv Γ I _).1 y.2)
      map_smul' := fun a x => hsmul a x.1 ((memZ1c_triv Γ I _).1 x.2) }
  let f00 := ((B1c (Representation.trivial Λ G Λ) Γ I).comap
    (Z1c (Representation.trivial Λ G Λ) Γ I).subtype).liftQ f0 (by
    intro x hx
    obtain ⟨m, hm⟩ := eq_of_memB1c Γ I x.1 hx
    show f x.1 = 0
    rw [hm]
    exact h0 m)
  obtain ⟨Y, hY⟩ := hbr.2 f00
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ Y
  refine ⟨d.1, (memZ1_sigma Γ σ htr d.1).1 d.2, fun x hx => ?_⟩
  have hx' := (memZ1c_triv Γ I x).2 hx
  rw [cpair_mk H DD hx' d.2]
  exact LinearMap.congr_fun hY (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩)

include htr in
theorem clause_frob [Γ.Normal] (φ : G) (τ : S → S) (η : S → Γ) (hI : BdryCompat Γ I φ⁻¹ τ η) (c0 : Λ)
    (key : ∀ x y, constPair H DD (frobH1c (Representation.trivial Λ G Λ) Γ I φ⁻¹ τ η hI x)
      (frobH1 σ Γ φ⁻¹ y) = c0 * constPair H DD x y) :
    ∀ (x : (Γ → Λ) × (S → Λ)) (d c' d' : Γ → Λ),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) →
      (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
      (∀ g g' : Γ, (g' : G) = φ * g * φ⁻¹ → c' g = x.1 g' ∧ d' g = σ φ⁻¹ (d g')) →
      (IsLocallyConstant c' ∧ (∀ g h, c' (g * h) = c' g + c' h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → c' g = 0) ∧
      (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) ∧
      cpair H DD (c', fun s => x.2 (τ s) - x.1 (η s)) d' = c0 * cpair H DD x d := by
  intro x d c' d' hx hd hrel
  have hx' := (memZ1c_triv Γ I x).2 hx
  have hd' := (memZ1_sigma Γ σ htr d).2 hd
  have hconj : ∀ g, ((conjΓ Γ φ⁻¹ g : Γ) : G) = φ * g * φ⁻¹ := fun g => by
    rw [conjΓ_val, inv_inv]
  have hc' : c' = twist (Representation.trivial Λ G Λ) Γ φ⁻¹ x.1 := funext fun g => by
    rw [twist_apply, Representation.trivial_apply]
    exact (hrel g _ (hconj g)).1
  have hdd : d' = twist σ Γ φ⁻¹ d := funext fun g => by
    rw [twist_apply]
    exact (hrel g _ (hconj g)).2
  subst hc' hdd
  have hpair : ((twist (Representation.trivial Λ G Λ) Γ φ⁻¹ x.1, fun s => x.2 (τ s) - x.1 (η s)) :
      (Γ → Λ) × (S → Λ)) = twistc (Representation.trivial Λ G Λ) Γ φ⁻¹ τ η x := by
    refine Prod.ext rfl (funext fun s => ?_)
    rw [twistc_snd]
    simp only [Representation.trivial_apply]
  have hZc := twistc_mem_Z1c (Representation.trivial Λ G Λ) Γ I φ⁻¹ τ η hI hx'
  have hZ1 := twist_mem_Z1 σ Γ φ⁻¹ hd'
  rw [← hpair] at hZc
  refine ⟨(memZ1c_triv Γ I _).1 hZc, (memZ1_sigma Γ σ htr _).1 hZ1, ?_⟩
  rw [cpair_mk H DD hZc hZ1, cpair_mk H DD hx' hd']
  have e := key (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩) (H1.mk σ Γ ⟨d, hd'⟩)
  have hX : H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨_, hZc⟩ =
      frobH1c (Representation.trivial Λ G Λ) Γ I φ⁻¹ τ η hI
        (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩) := by
    simp only [frobH1c, H1c.mk, Submodule.mkQ_apply]
    exact congrArg _ (Subtype.ext hpair)
  have hY : H1.mk σ Γ ⟨_, hZ1⟩ = frobH1 σ Γ φ⁻¹ (H1.mk σ Γ ⟨d, hd'⟩) := by
    simp only [frobH1, H1.mk, Submodule.mkQ_apply]
    rfl
  exact (congrArg₂ (fun a b => constPair H DD a b) hX hY).trans e

end Clauses

end CDBridge
end RamanujanPetersson

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh Kummer CP4a Residue PerfectCx
open scoped Pointwise Polynomial

set_option synthInstance.maxHeartbeats 400000 in
/-- The statement of `RamanujanPetersson.CupDuality.constDuality_S3_perfect` (copied verbatim), so that `CDSol.bridge` can take it as a hypothesis. -/
def CDSolMainStmt : Prop :=
  ∀ {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F] [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F] {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (hk : Places.constField Fq F = ⊥) {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (σ : Representation Λ (Pi1 (Places.Rfin Fq F) F) Λ) (hσ : IsOpen (σ.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    (htriv : ∀ (g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) (x : Λ), σ g x = x),
    ∃ (t : (s : S) → ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s))
          (DD : ConstData σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia t)
          (H : CupHyp (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ) σ σ (LinearMap.mul Λ Λ)
            (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))),
          ParabolicPerfect H DD ∧ (constPair H DD).IsPerfPair ∧
          ∀ φ : Pi1 (Places.Rfin Fq F) F, IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ →
            ∀ (x : H1c (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
                (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia)
              (y : H1 σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))),
            constPair H DD (frobH1c (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
                (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹)
                (trueCompat D φ⁻¹) x) (frobH1 σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) φ⁻¹ y) =
              ((Fintype.card Fq : Λ) * σ φ⁻¹ 1) * constPair H DD x y

end CupDuality
end RamanujanPetersson

open RamanujanPetersson in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem CDSol.bridge (MAIN : RamanujanPetersson.CupDuality.CDSolMainStmt)
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p e : ℕ) [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (hk : algebraicClosure Fq F = ⊥)
    (l : ℕ) [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (CL : ℕ → IntermediateField F (AlgebraicClosure F))
    (hCL : ∀ m, CL m = IntermediateField.adjoin F
      (((Polynomial.X : Polynomial F) ^ (p ^ m) - Polynomial.X).rootSet (AlgebraicClosure F)))
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1)
    (hPicU : ∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
      ∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) M)]
        [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) M) M]
        (D : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) M) → ℤ),
        (Function.support D).Finite →
        ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ CL m), a ≠ 0 ∧
          ∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))]
            [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))
              ↥(M ⊔ CL m)]
            (w : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F)
              ↥(M ⊔ CL m)))
            (v : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) M)),
            (∀ x : integralClosure (FunctionField.ringOfIntegers Fq F) M, x ∈ v.asIdeal ↔
              ∃ y ∈ w.asIdeal, ((y : ↥(M ⊔ CL m)) :
                  AlgebraicClosure F) = ((x : M) : AlgebraicClosure F)) →
            (l : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a))
    (hPic : ∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
      ∀ [IsDedekindDomain (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M)]
        [IsFractionRing (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M) M]
        (r : ℕ),
        (∀ w : IsDedekindDomain.HeightOneSpectrum
            (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M),
          Nat.card (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M ⧸
            w.asIdeal) = r) →
        ∀ D : IsDedekindDomain.HeightOneSpectrum
            (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M) → ℤ,
          (Function.support D).Finite → ∑ᶠ w, D w = 0 →
          ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ CL m), a ≠ 0 ∧
            (∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F)
                ↥(M ⊔ CL m))]
              [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))
                ↥(M ⊔ CL m)]
              (y : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F)
                ↥(M ⊔ CL m))),
              ((l ^ n : ℕ) : ℤ) ∣ WithZero.log (y.valuation ↥(M ⊔ CL m) a)) ∧
            ∀ [IsDedekindDomain (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m))]
              [IsFractionRing (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m))
                ↥(M ⊔ CL m)]
              (w : IsDedekindDomain.HeightOneSpectrum
                (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m)))
              (v : IsDedekindDomain.HeightOneSpectrum
                (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M)),
              (∀ x : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M,
                x ∈ v.asIdeal ↔ ∃ y ∈ w.asIdeal, ((y : ↥(M ⊔ CL m)) :
                    AlgebraicClosure F) = ((x : M) : AlgebraicClosure F)) →
              ((l ^ n : ℕ) : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a))
    (Γ : Subgroup (KU ≃ₐ[F] KU))
    (hΓ : ∀ g : KU ≃ₐ[F] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (P : S → Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU))
    (hP : ∀ s, (P s).IsPrime ∧ P s ≠ ⊥)
    (hcover : ∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
      Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
        ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU))
    (hdisj : ∀ s s', ∀ g ∈ Γ,
      (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s')
    (I : S → Subgroup (KU ≃ₐ[F] KU))
    (hI : ∀ s (g : KU ≃ₐ[F] KU), g ∈ I s ↔
      ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, ∃ c ∈ P s, (c : KU) = g (b : KU) - b)
    (Λ : Type) [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (σ : Representation Λ (KU ≃ₐ[F] KU) Λ) (hσ : IsOpen (σ.ker : Set (KU ≃ₐ[F] KU)))
    (htriv : ∀ g ∈ Γ, ∀ x : Λ, σ g x = x) :
    ∃ t : S → Γ, (∀ s, (t s : KU ≃ₐ[F] KU) ∈ I s) ∧
      (∀ c d : Γ → Λ, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + c h) →
        (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
        ∃ u : Γ → Λ, IsLocallyConstant u ∧ ∀ g h, c g * d h = u h - u (g * h) + u g) ∧
      ∃ pair : (Γ → Λ) × (S → Λ) → (Γ → Λ) → Λ,
        (∀ (x : (Γ → Λ) × (S → Λ)) (d u : Γ → Λ),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
          (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
          (IsLocallyConstant u ∧ ∀ g h, x.1 g * d h = u h - u (g * h) + u g) →
          pair x d = ∑ s, (x.2 s * d (t s) - u (t s))) ∧
        (∀ x : (Γ → Λ) × (S → Λ),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
          (∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → pair x d = 0) →
          x.1 = 0 ∧ ∃ a : Λ, ∀ s, x.2 s = a) ∧
        (∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
          (∀ x : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → pair x d = 0) →
          d = 0) ∧
        (∀ f : (Γ → Λ) → Λ,
          (∀ d d' : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
            (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) → f (d + d') = f d + f d') →
          (∀ (a : Λ) (d : Γ → Λ), (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
            f (a • d) = a * f d) →
          ∃ x : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) ∧
            ∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → pair x d = f d) ∧
        (∀ f : (Γ → Λ) × (S → Λ) → Λ,
          (∀ x y : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
            (IsLocallyConstant y.1 ∧ (∀ g h, y.1 (g * h) = y.1 g + y.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → y.1 g = 0) → f (x + y) = f x + f y) →
          (∀ (a : Λ) (x : (Γ → Λ) × (S → Λ)),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → f (a • x) = a * f x) →
          (∀ a : Λ, f (0, fun _ => a) = 0) →
          ∃ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) ∧
            ∀ x : (Γ → Λ) × (S → Λ),
              (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → pair x d = f x) ∧
        ∀ φ : KU ≃ₐ[F] KU, (∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) →
            φ x = x ^ Fintype.card Fq) →
          ∃ τ : S → S, ∃ η : S → Γ,
            (∀ s (b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU), (∃ c ∈ P s, (b : KU) = φ (c : KU)) ↔
              ∃ c ∈ P (τ s), (b : KU) = (η s : KU ≃ₐ[F] KU) (c : KU)) ∧
            ∀ (x : (Γ → Λ) × (S → Λ)) (d c' d' : Γ → Λ),
              (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
              (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
              (∀ g g' : Γ, (g' : KU ≃ₐ[F] KU) = φ * g * φ⁻¹ → c' g = x.1 g' ∧ d' g = σ φ⁻¹ (d g')) →
              (IsLocallyConstant c' ∧ (∀ g h, c' (g * h) = c' g + c' h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → c' g = 0) ∧
              (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) ∧
              pair (c', fun s => x.2 (τ s) - x.1 (η s)) d' =
                ((Fintype.card Fq : Λ) * σ φ⁻¹ 1) * pair x d := by
  classical
  -- `K_U = maxUnram`
  have hset : unramSet (FunctionField.ringOfIntegers Fq F) F =
      {L : IntermediateField F (AlgebraicClosure F) | FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (CDBridge.unram_iff _ F L))
  have hKU' : KU = maxUnram (FunctionField.ringOfIntegers Fq F) F := by
    rw [hKU, maxUnram, hset]
    rfl
  subst hKU'
  have hCL' : CL = Kummer.constLevel F p := funext hCL
  subst hCL'
  have hΓ' : Γ = CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq) := by
    ext g
    rw [hΓ, CurveCoh.mem_pi1geo]
    rfl
  subst hΓ'
  -- the divisibility hypotheses in library form
  have hPicU' : CdOne.PicDivU (Places.Rfin Fq F) F p l := by
    intro M hM hMU i1 i2 D hD
    obtain ⟨m, hm, a, ha, H⟩ := @hPicU M hM hMU i1 i2 D hD
    refine ⟨m, hm, a, ha, ?_⟩
    intro i3 i4 w
    exact @H i3 i4 w _ (@CDBridge.under_iff _ _ _ _ _ _ _ _ _ le_sup_left i1 i3 w)
  have hPic' : Residue.PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n) := by
    intro M hM hMU i1 i2 r hr D hD hsum
    obtain ⟨m, hm, a, ha, H1, H2⟩ := @hPic M hM hMU i1 i2 r hr D hD hsum
    refine ⟨m, hm, a, ha, by intro i5 i6 y; exact @H1 i5 i6 y, ?_⟩
    intro i3 i4 w
    exact @H2 i3 i4 w _ (@CDBridge.under_iff _ _ _ _ _ _ _ _ _ le_sup_left i1 i3 w)
  -- boundary data
  let D : CurveCoh.BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S :=
    { B := CurveCoh.IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F)
      B_smul := fun g Q hQ => CurveCoh.isBdryPrime_smul _ _ _ g hQ
      P := P
      mem := hP
      cover := fun Q hQ => by
        obtain ⟨s, g, hg, hb⟩ := hcover Q hQ.1 hQ.2
        exact ⟨s, g, hg, Ideal.ext fun b => (hb b).trans (CDBridge.mem_smul_iff _ g (P s) b).symm⟩
      disj := fun s s' g hg he => hdisj s s' g hg fun b => by
        rw [he]
        exact CDBridge.mem_smul_iff _ g (P s) b }
  have hI' : I = D.inertia := by
    funext s
    ext g
    rw [hI]
    show _ ↔ g ∈ CurveCoh.BdryData.inertia D s
    rw [CurveCoh.BdryData.inertia, AddSubgroup.mem_inertia]
    refine forall_congr' fun b => ⟨fun ⟨c, hc, he⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
    have : c = g • b - b := Subtype.ext he
    rwa [← this]
  subst hI'
  have htr : ∀ (g : CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq)) (x : Λ),
      σ g x = x := fun g x => htriv g g.2 x
  obtain ⟨t, DD, H, -, hperf, hfrob⟩ :=
    MAIN hq he hk hl n hPicU' hPic' D (fun Q => Iff.rfl) hΛ σ hσ htr
  have key := hfrob
  refine ⟨CupDuality.tG t, fun s => (Subgroup.mem_inf.1 (t s).2).2,
    CDBridge.clause_cup H htr, CDBridge.cpair H DD, CDBridge.clause_formula H DD htr,
    CDBridge.clause_left H DD htr hperf, CDBridge.clause_right H DD htr hperf,
    CDBridge.clause_surjL H DD htr hperf, CDBridge.clause_surjR H DD htr hperf, fun φ hφ => ?_⟩
  have kφ := key φ hφ
  refine ⟨CP4a.trueTau D φ⁻¹, CP4a.trueH D φ⁻¹, fun s b => ?_,
    CDBridge.clause_frob H DD htr φ _ _ (CP4a.trueCompat D φ⁻¹) _ kφ⟩
  have hs := CP4a.trueTau_spec D φ⁻¹ s
  rw [inv_inv] at hs
  have h1 := CDBridge.mem_smul_iff (Places.Rinf Fq F) φ (D.P s) b
  have h2 := CDBridge.mem_smul_iff (Places.Rinf Fq F)
    ((CP4a.trueH D φ⁻¹ s : CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq)) :
      Pi1 (FunctionField.ringOfIntegers Fq F) F) (D.P (CP4a.trueTau D φ⁻¹ s)) b
  rw [hs] at h1
  exact h1.symm.trans h2


