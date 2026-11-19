-- Prove2me | Definitions.Def_RPLib_S4_CDPack05
-- name    : RPLib_S4_CDPack05
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:33:38.425132+00:00
-- url     : https://prove2.me/theorems/1efe90e5-f11d-438b-88f5-9905435a3f35
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 5 of 71
-- statement:
--   Part 5 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_PerfectCx_Pkg`: S4-PD (5), E3: the perfect complex as a Hattori–Stallings package
--   * `Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
--   * `Def_RP_CupDuality_CupFrob`: S4-CurveDuality O2b: Frobenius compatibility of the cup product
--   * `Def_RP_ConeDuality_Const`: S4-CurveDuality O3: constant coefficients, the cone `H²` and the boundary block
--   * `Def_RP_CupDuality_GysA`: S4-CurveDuality O4G-1: the Gysin count for a unipotent family
--   * `Def_RP_ConeDuality_Frob`: S4-CurveDuality O6b: Frobenius on the constant-coefficient pairing
--   * `Def_RP_PerfectCx_Red`: S4-PD (5), E3: reduction mod `t` (e.g. `ℓⁿ → ℓᵐ`)
--   * `Def_RP_PerfectCx_RedPC`: S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack04
import Definitions.Def_RPLib_S4_CDPack03
import Definitions.Def_RPLib_S4_CDPack01

/-!
# Curve-duality library package, part 5 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_PerfectCx_Pkg`: S4-PD (5), E3: the perfect complex as a Hattori–Stallings package
* `Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
* `Def_RP_CupDuality_CupFrob`: S4-CurveDuality O2b: Frobenius compatibility of the cup product
* `Def_RP_ConeDuality_Const`: S4-CurveDuality O3: constant coefficients, the cone `H²` and the boundary block
* `Def_RP_CupDuality_GysA`: S4-CurveDuality O4G-1: the Gysin count for a unipotent family
* `Def_RP_ConeDuality_Frob`: S4-CurveDuality O6b: Frobenius on the constant-coefficient pairing
* `Def_RP_PerfectCx_Red`: S4-PD (5), E3: reduction mod `t` (e.g. `ℓⁿ → ℓᵐ`)
* `Def_RP_PerfectCx_RedPC`: S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_PerfectCx_Pkg =====
section

/-!
# S4-PD (5), E3: the perfect complex as a Hattori–Stallings package

`PC Λ π Γ I = [A → E_Γ × A^S → Π_s E_s]` (`A = Λ[Gf]`, `E_Δ = Z¹(Δ; A)`) as the `ℕ`-indexed family consumed by
`HattoriStallings.lefschetz`, with its `Gf`-representations `ρPC`, projectivity (`isProj_ρPC`, from a Sylow subgroup:
`isProj_ρPC_of_sylow`), freeness and finiteness (`pc_free_finite`), the identifications `(PC i ⊗ M)_{Gf} ≅ K^i(M)`
(`pcIso0`, `pcIso1`, `pcIso2`) and the twisted trace formula (`lefschetz_PC`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct IsLocalRing LinearMap

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

variable (Λ) in
/-- The perfect complex `P = [A → E_Γ × A^S → Π_s E_s]` as an `ℕ`-indexed family. -/
abbrev PC : ℕ → Type :=
  Tri (MonoidAlgebra Λ Gf) (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf))
    ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s))

variable (Λ) in
/-- The `Gf`-representations on the terms of `PC` (right multiplication on `A`). -/
def ρPC : ∀ i, Representation Λ Gf (PC Λ π Γ I i) :=
  triRep (rRep Λ Gf) (rho1 Λ π Γ S) (rho2 Λ π Γ I)

theorem isProj_ρPC [Fintype Gf] (hE : IsProj (eRep (Λ := Λ) π Γ))
    (hEs : ∀ s, IsProj (eRep (Λ := Λ) π (Γ ⊓ I s))) : ∀ i, IsProj (ρPC Λ π Γ I i) :=
  isProj_tri isProj_rRep (isProj_rho1 π Γ hE) (isProj_rho2 π Γ I hEs)

section Hyps

variable [IsLocalRing Λ] [Finite Λ] {ϖ : Λ} (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) {n : ℕ}
  (hn : ϖ ^ n = 0) (hn' : ∀ m < n, ϖ ^ m ≠ 0) {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N) (hπ : IsOpen (π.ker : Set G))
  [Module.Finite Λ (Z1 (regRep Λ π) Γ)] [∀ s, Module.Finite Λ (Z1 (regRep Λ π) (Γ ⊓ I s))]

include hϖ hn hn' hΛ hall hallI hπ in
/-- Projectivity of all terms from an `ℓ`-Sylow subgroup `Q` of `Gf` (E2(b), `proj_E`). -/
theorem isProj_ρPC_of_sylow [Fintype Gf] [Fact l.Prime] [CharP (ResidueField Λ) l] (Q : Subgroup Gf) [Fintype Q]
    (hQ : IsPGroup l Q) (hindex : ¬ l ∣ Q.index) : ∀ i, IsProj (ρPC Λ π Γ I i) :=
  isProj_ρPC π Γ I (proj_E π Γ Q hϖ hn hn' hΛ hall hπ hQ hindex)
    (fun s => proj_E π (Γ ⊓ I s) Q hϖ hn hn' hΛ (hallI s) hπ hQ hindex)

include hϖ hn hn' hΛ hall hallI hπ in
/-- All terms of `PC` are free and finite over `Λ` (E2(a), `free_E`). -/
theorem pc_free_finite [Finite Gf] [Finite S] :
    (∀ i, Module.Free Λ (PC Λ π Γ I i)) ∧ ∀ i, Module.Finite Λ (PC Λ π Γ I i) := by
  have : Module.Free Λ (Z1 (regRep Λ π) Γ) := free_E π Γ hϖ hn hn' hΛ hall hπ
  have : ∀ s, Module.Free Λ (Z1 (regRep Λ π) (Γ ⊓ I s)) := fun s =>
    free_E π (Γ ⊓ I s) hϖ hn hn' hΛ (hallI s) hπ
  exact ⟨fun i => inferInstance, fun i => inferInstance⟩

end Hyps

section Iso

variable [Finite Λ] [Finite Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M)
  {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

/-- `(P⁰ ⊗ M)_{Gf} ≃ M`. -/
def pcIso0 : Coinvariants ((ρPC Λ π Γ I 0).tprod τ) ≃ₗ[Λ] M := coinvA τ

/-- `(P¹ ⊗ M)_{Gf} ≃ Z¹(Γ; M) × M^S`. -/
def pcIso1 [Fintype S] [DecidableEq S] :
    Coinvariants ((ρPC Λ π Γ I 1).tprod τ) ≃ₗ[Λ] Z1 (τ.comp π) Γ × (S → M) :=
  iso1 π Γ S hπ τ hΛ hall

/-- `(P² ⊗ M)_{Gf} ≃ Π_s Z¹(Γ ⊓ I s; M)`. -/
def pcIso2 [Fintype S] [DecidableEq S] :
    Coinvariants ((ρPC Λ π Γ I 2).tprod τ) ≃ₗ[Λ] ((s : S) → Z1 (τ.comp π) (Γ ⊓ I s)) :=
  iso2 π Γ I hπ τ hΛ hallI

end Iso

/-- **Twisted trace formula for the perfect complex** (SGA 4½, *Rapport*): for a free finite `Λ`-module `M` with a
`Gf`-action `τ`, an equivariant endomorphism `φ` of `PC` and an equivariant endomorphism `ψ` of `M`,
`Σ (-1)^i Tr(φ i ⊗ ψ | (PC i ⊗ M)_{Gf}) = Σ_c L(φ)[c] · Tr(c⁻¹ ∘ ψ | M)`. -/
theorem lefschetz_PC [IsLocalRing Λ] [Fintype Gf] [Fintype (ConjClasses Gf)]
    [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (hρ : ∀ i, IsProj (ρPC Λ π Γ I i)) {M : Type} [AddCommGroup M] [Module Λ M] [Module.Free Λ M]
    [Module.Finite Λ M] {τ : Representation Λ Gf M} {φ : ∀ i, PC Λ π Γ I i →ₗ[Λ] PC Λ π Γ I i}
    (hφ : ∀ i, IsEquivariant (ρPC Λ π Γ I i) (ρPC Λ π Γ I i) (φ i)) {ψ : M →ₗ[Λ] M}
    (hψ : IsEquivariant τ τ ψ) :
    trace Λ _ (coinvMap ((ρPC Λ π Γ I 0).tprod τ) (TensorProduct.map (φ 0) ψ) (isEquivariant_tensorMap (hφ 0) hψ)) -
      trace Λ _ (coinvMap ((ρPC Λ π Γ I 1).tprod τ) (TensorProduct.map (φ 1) ψ)
        (isEquivariant_tensorMap (hφ 1) hψ)) +
      trace Λ _ (coinvMap ((ρPC Λ π Γ I 2).tprod τ) (TensorProduct.map (φ 2) ψ)
        (isEquivariant_tensorMap (hφ 2) hψ)) =
      ∑ c : ConjClasses Gf, lefschetz (ρPC Λ π Γ I) 2 φ c * twChar τ ψ c := by
  have h := lefschetz_coinv_of_local hρ hφ hψ 2
  rw [sum_range_three_alt] at h
  exact h

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_FrobIso =====
section

/-!
# S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula

The cone Frobenius (`frob1`, `frob2` of `Def_RP_PerfectCx_Frob`) preserves `ker d¹` (`frobKer`), where it is the
`twistc` operator of `CurveCoh_Pair` (`kerEquivZ1c_frobKer`), so it induces `frobH1c` on `H¹_c` (`frobH1c_kerEquiv`);
it also induces `frobH2K` on `H²(K) = coker d¹`. On the perfect complex `PC` the Frobenius `frobPC` is
`Gf`-equivariant (`frobPC_equiv`) and the identifications `(PC i ⊗ M)_{Gf} ≅ K^i(M)` carry `frobPC i ⊗ id` to the
cone Frobenius with coefficients `τ ∘ π` (`pcIso0_frob`, `pcIso1_frob`, `pcIso2_frob`). Hence (`lefschetz_frob`)
`Tr(F | M) - Tr(F | K¹(M)) + Tr(F | K²(M)) = Σ_c L(frobPC)[c] · Tr(τ(c)⁻¹ | M)` (SGA 4½, *Rapport*).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct

noncomputable section

/-- Traces agree along a linear equivalence intertwining two endomorphisms. -/
theorem trace_eq_of_intertwine {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] (e : V ≃ₗ[R] W) (f : V →ₗ[R] V) (g : W →ₗ[R] W) (hfg : ∀ v, e (f v) = g (e v)) :
    LinearMap.trace R V f = LinearMap.trace R W g := by
  have hg : g = e.conj f := LinearMap.ext fun w => by
    rw [LinearEquiv.conj_apply_apply, hfg, LinearEquiv.apply_symm_apply]
  rw [hg, LinearMap.trace_conj']

section H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) [Γ.Normal] {S : Type}
  (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ) (hρ : IsOpen (ρ.ker : Set G))

theorem frob1_mem_ker (hI : BdryCompat Γ I ψ t h) {p : Z1 ρ Γ × (S → M)} (hp : p ∈ LinearMap.ker (cx1 ρ Γ I hρ)) :
    frob1 ρ Γ ψ t h p ∈ LinearMap.ker (cx1 ρ Γ I hρ) := by
  rw [LinearMap.mem_ker] at hp ⊢
  rw [← LinearMap.comp_apply, cx1_frob (ρ := ρ) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hρ := hρ) (hI := hI),
    LinearMap.comp_apply, hp, map_zero]

/-- The Frobenius on the cocycles `ker d¹` of the cone complex. -/
def frobKer (hI : BdryCompat Γ I ψ t h) : LinearMap.ker (cx1 ρ Γ I hρ) →ₗ[k] LinearMap.ker (cx1 ρ Γ I hρ) :=
  (frob1 ρ Γ ψ t h).restrict fun _ hp => frob1_mem_ker ρ Γ I ψ t h hρ hI hp

/-- On `ker d¹ ≃ Z1c` the cone Frobenius is the `twistc` operator of `CurveCoh_Pair`. -/
theorem kerEquivZ1c_frobKer (hI : BdryCompat Γ I ψ t h) (p : LinearMap.ker (cx1 ρ Γ I hρ)) :
    kerEquivZ1c ρ Γ I hρ (frobKer ρ Γ I ψ t h hρ hI p) =
      (twistc ρ Γ ψ t h).restrict (fun _ hq => twistc_mem_Z1c ρ Γ I ψ t h hI hq) (kerEquivZ1c ρ Γ I hρ p) :=
  rfl

/-- The cone Frobenius induces `frobH1c` on `H¹_c`. -/
theorem frobH1c_kerEquiv (hI : BdryCompat Γ I ψ t h) (p : LinearMap.ker (cx1 ρ Γ I hρ)) :
    frobH1c ρ Γ I ψ t h hI (H1c.mk ρ Γ I (kerEquivZ1c ρ Γ I hρ p)) =
      H1c.mk ρ Γ I (kerEquivZ1c ρ Γ I hρ (frobKer ρ Γ I ψ t h hρ hI p)) :=
  rfl

/-- The Frobenius on `H²(K) = coker d¹`. -/
def frobH2K (hI : BdryCompat Γ I ψ t h) : H2K ρ Γ I hρ →ₗ[k] H2K ρ Γ I hρ :=
  Submodule.mapQ _ _ (frob2 ρ Γ I ψ t h hI) fun x hx => by
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
    exact Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨frob1 ρ Γ ψ t h p,
      LinearMap.congr_fun (cx1_frob (ρ := ρ) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hρ := hρ) (hI := hI)) p⟩)

theorem frobH2K_mk (hI : BdryCompat Γ I ψ t h) (e : (s : S) → Z1 ρ (Γ ⊓ I s)) :
    frobH2K ρ Γ I ψ t h hρ hI (Submodule.Quotient.mk e) = Submodule.Quotient.mk (frob2 ρ Γ I ψ t h hI e) :=
  rfl

end H

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

variable (Λ) in
/-- The Frobenius endomorphism of the perfect complex `PC`. -/
def frobPC : ∀ i, PC Λ π Γ I i →ₗ[Λ] PC Λ π Γ I i :=
  triMap (regRep Λ π ψ) (frob1 (regRep Λ π) Γ ψ t h) (frob2 (regRep Λ π) Γ I ψ t h hI)

theorem frobPC_equiv : ∀ i, IsEquivariant (ρPC Λ π Γ I i) (ρPC Λ π Γ I i) (frobPC Λ π Γ I ψ t h hI i) :=
  triMap_equiv (show IsEquivariant (rRep Λ Gf) (rRep Λ Gf) (regRep Λ π ψ) from
      fun x => LinearMap.ext fun a => (mulRight_regRep π (single x⁻¹ 1) ψ a).symm)
    (frob1_equiv (Λ := Λ) (π := π) (Γ := Γ) (ψ := ψ) (t := t) (h := h))
    (frob2_equiv (Λ := Λ) (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) hI)

variable [Finite Λ] [Fintype Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M)
  {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

theorem coinvA_frob_mk (a : MonoidAlgebra Λ Gf) (m : M) :
    coinvA τ (Coinvariants.mk _ (regRep Λ π ψ a ⊗ₜ m)) = τ (π ψ) (coinvA τ (Coinvariants.mk _ (a ⊗ₜ m))) := by
  rw [coinvA_mk_tmul, coinvA_mk_tmul, regRep_apply, act_single_mul]

theorem iso1_frob_mk [Fintype S] [DecidableEq S] (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) (m : M) :
    iso1 π Γ S hπ τ hΛ hall (Coinvariants.mk _ (frob1 (regRep Λ π) Γ ψ t h p ⊗ₜ m)) =
      frob1 (τ.comp π) Γ ψ t h (iso1 π Γ S hπ τ hΛ hall (Coinvariants.mk _ (p ⊗ₜ m))) := by
  refine Prod.ext (Subtype.ext (funext fun g => ?_)) (funext fun s => ?_)
  · simp only [iso1_mk_tmul, frob1_fst, conjMap_apply, Phi_mk_tmul, regRep_apply, act_single_mul,
      MonoidHom.comp_apply]
  · simp only [iso1_mk_tmul, frob1_snd, Phi_mk_tmul, regRep_apply, act_single_mul, map_sub, LinearMap.sub_apply,
      MonoidHom.comp_apply]

theorem iso2_frob_mk [Fintype S] [DecidableEq S] (p : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M) :
    iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (frob2 (regRep Λ π) Γ I ψ t h hI p ⊗ₜ m)) =
      frob2 (τ.comp π) Γ I ψ t h hI (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (p ⊗ₜ m))) := by
  refine funext fun s => Subtype.ext (funext fun g => ?_)
  simp only [iso2_mk_tmul, Phi_mk_tmul, frob2_apply, regRep_apply, act_single_mul, MonoidHom.comp_apply]

/-- Degree 0: `(P⁰ ⊗ M)_{Gf} ≃ M` carries `frobPC 0 ⊗ id` to `τ (π ψ)`. -/
theorem pcIso0_frob (u : Coinvariants ((ρPC Λ π Γ I 0).tprod τ)) :
    pcIso0 π Γ I τ (coinvMap ((ρPC Λ π Γ I 0).tprod τ) (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 0) LinearMap.id)
      (isEquivariant_tensorMap (frobPC_equiv π Γ I ψ t h hI 0) (isEquivariant_id (ρ := τ))) u) =
      τ (π ψ) (pcIso0 π Γ I τ u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m =>
    rw [coinvMap_mk, TensorProduct.map_tmul, LinearMap.id_apply]
    exact coinvA_frob_mk (π := π) (ψ := ψ) τ a m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Degree 1: `(P¹ ⊗ M)_{Gf} ≃ Z¹(Γ; M) × M^S` carries `frobPC 1 ⊗ id` to `frob1`. -/
theorem pcIso1_frob [Fintype S] [DecidableEq S] (u : Coinvariants ((ρPC Λ π Γ I 1).tprod τ)) :
    pcIso1 π Γ I τ hΛ hall hπ (coinvMap ((ρPC Λ π Γ I 1).tprod τ)
      (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 1) LinearMap.id)
      (isEquivariant_tensorMap (frobPC_equiv π Γ I ψ t h hI 1) (isEquivariant_id (ρ := τ))) u) =
      frob1 (τ.comp π) Γ ψ t h (pcIso1 π Γ I τ hΛ hall hπ u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p m =>
    rw [coinvMap_mk, TensorProduct.map_tmul, LinearMap.id_apply]
    exact iso1_frob_mk (π := π) (Γ := Γ) (ψ := ψ) (t := t) (h := h) (τ := τ) (hΛ := hΛ) (hall := hall)
      (hπ := hπ) p m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Degree 2: `(P² ⊗ M)_{Gf} ≃ Π_s Z¹(Γ ⊓ I s; M)` carries `frobPC 2 ⊗ id` to `frob2`. -/
theorem pcIso2_frob [Fintype S] [DecidableEq S] (u : Coinvariants ((ρPC Λ π Γ I 2).tprod τ)) :
    pcIso2 π Γ I τ hΛ hallI hπ (coinvMap ((ρPC Λ π Γ I 2).tprod τ)
      (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 2) LinearMap.id)
      (isEquivariant_tensorMap (frobPC_equiv π Γ I ψ t h hI 2) (isEquivariant_id (ρ := τ))) u) =
      frob2 (τ.comp π) Γ I ψ t h hI (pcIso2 π Γ I τ hΛ hallI hπ u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p m =>
    rw [coinvMap_mk, TensorProduct.map_tmul, LinearMap.id_apply]
    exact iso2_frob_mk (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hI := hI) (τ := τ) (hΛ := hΛ)
      (hallI := hallI) (hπ := hπ) p m
  | add x y hx hy => simp only [map_add, hx, hy]

include hΛ hall hallI hπ in
/-- **Lefschetz trace formula for the Frobenius on the cone complex** (SGA 4½, *Rapport*): with the Frobenius acting
on `M` through `τ ∘ π`, `Tr(F | M) - Tr(F | K¹(M)) + Tr(F | K²(M)) = Σ_c L(frobPC)[c] · Tr(τ(c)⁻¹ | M)`. -/
theorem lefschetz_frob [IsLocalRing Λ] [Fintype (ConjClasses Gf)] [Fintype S] [DecidableEq S]
    [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (hρ : ∀ i, IsProj (ρPC Λ π Γ I i)) [Module.Free Λ M] [Module.Finite Λ M] :
    LinearMap.trace Λ M (τ (π ψ)) - LinearMap.trace Λ _ (frob1 (τ.comp π) Γ ψ t h) +
      LinearMap.trace Λ _ (frob2 (τ.comp π) Γ I ψ t h hI) =
      ∑ c : ConjClasses Gf, lefschetz (ρPC Λ π Γ I) 2 (frobPC Λ π Γ I ψ t h hI) c * twChar τ LinearMap.id c := by
  have H := lefschetz_PC π Γ I hρ (frobPC_equiv π Γ I ψ t h hI) (isEquivariant_id (ρ := τ))
  rw [trace_eq_of_intertwine (pcIso0 π Γ I τ) _ _ (pcIso0_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hI := hI) (τ := τ)),
    trace_eq_of_intertwine (pcIso1 π Γ I τ hΛ hall hπ) _ _ (pcIso1_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hI := hI) (τ := τ)
      (hΛ := hΛ) (hall := hall) (hπ := hπ)),
    trace_eq_of_intertwine (pcIso2 π Γ I τ hΛ hallI hπ) _ _ (pcIso2_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hI := hI) (τ := τ)
      (hΛ := hΛ) (hallI := hallI) (hπ := hπ))] at H
  exact H

end Model

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_CupDuality_CupFrob =====
section

/-!
# S4-CurveDuality O2b: Frobenius compatibility of the cup product

`cupPair (frobH1c x) (frobH1 y) = frobH2K (cupPair x y)` for a Frobenius lift `ψ` with boundary data `(τ, h)`
(`BdryCompat`). On cocycles: the twisted primitive is `g ↦ σ ψ (u (ψ⁻¹ g ψ))`, and the two boundary cocycles differ
by `d¹ (0, s ↦ -σ ψ w_s)` with `w_s = β (c x) (d x) + u x - β (ρ x m_{τ s}) (d x)`, `x = h s` (`frob_core`).
Also `CupHyp` from `H2All` (`cupHyp_of_all`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {M' : Type} [AddCommGroup M'] [Module k M']
  {L : Type} [AddCommGroup L] [Module k L]
  {ρ : Representation k G M} {ρ' : Representation k G M'} {σ : Representation k G L}
  {β : M →ₗ[k] M' →ₗ[k] L} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}

/-- `H²(Γ, L) = 0` from `H2All`. -/
theorem h2Van_top_of_all {l n : ℕ} (hall : H2All k G Γ l n) [Finite L] (hL : ∀ m : L, (l ^ n) • m = 0)
    (hσ : IsOpen (σ.ker : Set G)) : H2Van σ Γ ⊤ := fun f hf _ hc => by
  obtain ⟨b, hb, hfb⟩ := hall L σ hL hσ f hf hc
  exact ⟨b, hb, fun _ => Submodule.mem_top, hfb⟩

/-- The cup-product hypotheses from `H2All`. -/
theorem cupHyp_of_all {l n : ℕ} (hall : H2All k G Γ l n) [Finite L] (hL : ∀ m : L, (l ^ n) • m = 0)
    (equiv : ∀ (g : G) (x : M) (y : M'), β (ρ g x) (ρ' g y) = σ g (β x y))
    (h' : IsOpen (ρ'.ker : Set G)) (hσ : IsOpen (σ.ker : Set G)) : CupHyp ρ ρ' σ β Γ :=
  ⟨equiv, h', hσ, h2Van_top_of_all hall hL hσ⟩

/-- The algebraic core of Frobenius compatibility (`gt x = x g2`, `g2 ∈ I`). -/
theorem frob_core (H : CupHyp ρ ρ' σ β Γ) {c : Γ → M} {d : Γ → M'} {u : Γ → L} (hc : c ∈ Z1 ρ Γ)
    (hd : d ∈ Z1 ρ' Γ) (hu : IsPrim ρ' σ β Γ c d u) (x gt g2 : Γ) (m : M) (hmul : gt * x = x * g2)
    (hcg : c g2 = ρ (g2 : G) m - m) :
    β (ρ (x : G) m - c x) (d gt) - u gt - σ (x : G) (β m (d g2) - u g2) =
      σ (gt : G) (β (c x) (d x) + u x - β (ρ (x : G) m) (d x)) -
        (β (c x) (d x) + u x - β (ρ (x : G) m) (d x)) := by
  have R1 : β (c gt) (ρ' (gt : G) (d x)) = σ (gt : G) (u x) - u (gt * x) + u gt := hu.2 gt x
  have R2 : β (c x) (ρ' (x : G) (d g2)) = σ (x : G) (u g2) - u (x * g2) + u x := hu.2 x g2
  have D1 : d (gt * x) = d gt + ρ' (gt : G) (d x) := hd.2 gt x
  have D2 : d (x * g2) = d x + ρ' (x : G) (d g2) := hd.2 x g2
  have C1 : c (gt * x) = c gt + ρ (gt : G) (c x) := hc.2 gt x
  have C2 : c (x * g2) = c x + ρ (x : G) (c g2) := hc.2 x g2
  rw [hmul] at R1 D1 C1
  have Dx : ρ' (x : G) (d g2) = d gt + ρ' (gt : G) (d x) - d x := by
    rw [← D1, D2]; abel
  have Cgt : c gt = c x + ρ (x : G) (c g2) - ρ (gt : G) (c x) := by
    rw [eq_sub_iff_add_eq, ← C1, C2]
  have Rgx : ρ (x : G) (ρ (g2 : G) m) = ρ (gt : G) (ρ (x : G) m) := by
    have e := congrArg (fun z : Γ => ρ (z : G) m) hmul
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply] at e
    exact e.symm
  rw [Cgt, hcg, map_sub (ρ (x : G)), Rgx] at R1
  rw [Dx] at R2
  rw [map_sub (σ (x : G)), ← H.equiv (x : G) m (d g2), Dx]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, H.equiv] at R1 R2 ⊢
  linear_combination (norm := module) R1 - R2

section Frob

variable [Γ.Normal] (H : CupHyp ρ ρ' σ β Γ) (ψ : G) (τ : S → S) (h : S → Γ)

include H in
/-- The twisted primitive: `T_ψ u` is a primitive of `T_ψ c ∪ T_ψ d`. -/
theorem prim_twist {c : Γ → M} {d : Γ → M'} {u : Γ → L} (hu : IsPrim ρ' σ β Γ c d u) :
    IsPrim ρ' σ β Γ (twist ρ Γ ψ c) (twist ρ' Γ ψ d) (twist σ Γ ψ u) := by
  refine ⟨(hu.1.comp_continuous (continuous_conjΓ Γ ψ)).comp (σ ψ), fun g j => ?_⟩
  have e : β (c (conjΓ Γ ψ g)) (ρ' (conjΓ Γ ψ g : G) (d (conjΓ Γ ψ j))) =
      σ (conjΓ Γ ψ g : G) (u (conjΓ Γ ψ j)) - u (conjΓ Γ ψ g * conjΓ Γ ψ j) + u (conjΓ Γ ψ g) := hu.2 _ _
  show β (ρ ψ (c (conjΓ Γ ψ g))) (ρ' (g : G) (ρ' ψ (d (conjΓ Γ ψ j)))) =
    σ (g : G) (σ ψ (u (conjΓ Γ ψ j))) - σ ψ (u (conjΓ Γ ψ (g * j))) + σ ψ (u (conjΓ Γ ψ g))
  rw [← rho_conj ρ' Γ ψ g, H.equiv, ← rho_conj σ Γ ψ g, conjΓ_mul, e, map_add, map_sub]

/-- Frobenius compatibility of the cup product on cocycles. -/
theorem cupH_frob (hI : BdryCompat Γ I ψ τ h) {c : Γ → M} {mv : S → M} (hp : (c, mv) ∈ Z1c ρ Γ I)
    {dd : Γ → M'} (hd : dd ∈ Z1 ρ' Γ) :
    cupH H ⟨twistc ρ Γ ψ τ h (c, mv), twistc_mem_Z1c ρ Γ I ψ τ h hI hp⟩
        ⟨twist ρ' Γ ψ dd, twist_mem_Z1 ρ' Γ ψ hd⟩ =
      frobH2K σ Γ I ψ τ h H.openL hI (cupH H ⟨(c, mv), hp⟩ ⟨dd, hd⟩) := by
  obtain ⟨u, hu⟩ := exists_prim H hp.1 hd
  rw [cupH_eq H ⟨(c, mv), hp⟩ ⟨dd, hd⟩ u hu, frobH2K_mk,
    cupH_eq H ⟨twistc ρ Γ ψ τ h (c, mv), twistc_mem_Z1c ρ Γ I ψ τ h hI hp⟩
      ⟨twist ρ' Γ ψ dd, twist_mem_Z1 ρ' Γ ψ hd⟩ (twist σ Γ ψ u) (prim_twist H ψ hu),
    Submodule.Quotient.eq]
  refine ⟨(0, fun s => -σ ψ (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))), ?_⟩
  funext s
  apply Subtype.ext
  funext ⟨g, hg⟩
  obtain ⟨hgΓ, -⟩ := Subgroup.mem_inf.1 hg
  have hb := bdry_mem Γ I ψ τ h hI s g hg
  have hm2 : (ψ * (h s : G))⁻¹ * g * (ψ * (h s : G)) ∈ Γ := (Subgroup.mem_inf.1 hb).1
  have hcg : c ⟨_, hm2⟩ = ρ ((ψ * (h s : G))⁻¹ * g * (ψ * (h s : G))) (mv (τ s)) - mv (τ s) :=
    hp.2 (τ s) ⟨_, hm2⟩ (Subgroup.mem_inf.1 hb).2
  have hmul : conjΓ Γ ψ ⟨g, hgΓ⟩ * h s = h s * ⟨_, hm2⟩ := by
    apply Subtype.ext
    show ψ⁻¹ * g * ψ * (h s : G) = (h s : G) * ((ψ * (h s : G))⁻¹ * g * (ψ * (h s : G)))
    group
  have K := frob_core H hp.1 hd hu (h s) (conjΓ Γ ψ ⟨g, hgΓ⟩) ⟨_, hm2⟩ (mv (τ s)) hmul hcg
  have e5 : σ g (σ ψ (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))) =
      σ ψ (σ (conjΓ Γ ψ ⟨g, hgΓ⟩ : G)
        (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))) :=
    (rho_conj σ Γ ψ ⟨g, hgΓ⟩ _).symm
  change (0 : Γ → L) ⟨g, hgΓ⟩ -
      (σ g (-σ ψ (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))) -
        -σ ψ (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))) =
    (β (ρ ψ (ρ (h s : G) (mv (τ s)) - c (h s))) (ρ' ψ (dd (conjΓ Γ ψ ⟨g, hgΓ⟩))) -
        σ ψ (u (conjΓ Γ ψ ⟨g, hgΓ⟩))) -
      σ (ψ * (h s : G)) (β (mv (τ s)) (dd ⟨_, hm2⟩) - u ⟨_, hm2⟩)
  rw [H.equiv, map_mul σ ψ (h s : G), Module.End.mul_apply, ← map_sub (σ ψ), ← map_sub (σ ψ), K, map_neg,
    e5, Pi.zero_apply]
  simp only [map_sub, map_add]
  abel

/-- **Frobenius compatibility of the cup product**: `F(x) ∪ F(y) = F(x ∪ y)`. -/
theorem cupPair_frob (hI : BdryCompat Γ I ψ τ h) (x : H1c ρ Γ I) (y : H1 ρ' Γ) :
    cupPair H (frobH1c ρ Γ I ψ τ h hI x) (frobH1 ρ' Γ ψ y) =
      frobH2K σ Γ I ψ τ h H.openL hI (cupPair H x y) := by
  obtain ⟨⟨⟨c, mv⟩, hp⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨dd, hd⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact cupH_frob H ψ τ h hI hp hd

end Frob

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_ConeDuality_Const =====
section

/-!
# S4-CurveDuality O3: constant coefficients, the cone `H²` and the boundary block

Constant coefficients: `M = k` with the trivial action, `M' = L = k` with a twist `σ` that is trivial on `Γ`,
`β = mul`. Under the abstract tame-inertia / residue hypotheses `ConstData σ Γ I t` (`t s` generates tame inertia):
* `h2kEquiv : H2K σ Γ I hσ ≃ₗ[k] k`, `[e] ↦ Σ_s e_s(t_s)`;
* `constPair H D : H1c (trivial) Γ I →ₗ H1 σ Γ →ₗ k` (cup product, then `h2kEquiv`); `constPair_mk`;
* `constPair_bdry`: on boundary classes `[(0, m)]` it is `Σ_s m_s d(t_s)`; `constPair_h0`: zero on `im × H1par`;
* `blockA_isPerfPair`: the block `im(k^S → H¹_c) × H¹/H¹_par → k` is the residue pairing `resPair`, so perfect;
* `constPair_isPerfPair`: `constPair` is perfect once the parabolic block `H¹_c/im × H¹_par → k` is (O5).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation k G k) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (t : (s : S) → ↥(Γ ⊓ I s))

variable {Γ I} in
/-- `t s ∈ Γ ⊓ I s`, viewed in `Γ`. -/
def tG (s : S) : Γ := ⟨(t s).1, (Subgroup.mem_inf.1 (t s).2).1⟩

/-- `CupHyp` for constant coefficients `k × k(1) → k(1)`. -/
theorem constCupHyp (hσ : IsOpen (σ.ker : Set G)) (van : H2Van σ Γ ⊤) :
    CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ :=
  ⟨fun g x y => by
    rw [Representation.trivial_apply, LinearMap.mul_apply', LinearMap.mul_apply']
    have h := map_smul (σ g) x y
    exact h.symm, hσ, hσ, van⟩

variable [Fintype S]

/-- Constant-coefficient data: `σ` trivial on `Γ`; `Hom(Γ ⊓ I s, k) ≅ k` by evaluation at `t s`; the residue
theorem `Σ_s d(t_s) = 0` on `Z¹(Γ, k(1))` and its converse (divisibility of `Pic⁰`). -/
structure ConstData : Prop where
  triv : ∀ (g : Γ) (x : k), σ g x = x
  inj : ∀ (s : S) (e : Z1 σ (Γ ⊓ I s)), (e : ↥(Γ ⊓ I s) → k) (t s) = 0 → e = 0
  surj : ∀ (s : S) (a : k), ∃ e : Z1 σ (Γ ⊓ I s), (e : ↥(Γ ⊓ I s) → k) (t s) = a
  resSum : ∀ d : Z1 σ Γ, ∑ s, (d : Γ → k) (tG t s) = 0
  resOnto : ∀ r : S → k, ∑ s, r s = 0 → ∃ d : Z1 σ Γ, ∀ s, (d : Γ → k) (tG t s) = r s

/-- `e ↦ Σ_s e_s(t_s)` on `Π_s Z¹(Γ ⊓ I s, k)`. -/
def evalSum : ((s : S) → Z1 σ (Γ ⊓ I s)) →ₗ[k] k where
  toFun e := ∑ s, (e s : ↥(Γ ⊓ I s) → k) (t s)
  map_add' e e' := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' a e := by
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem evalSum_apply (e : (s : S) → Z1 σ (Γ ⊓ I s)) :
    evalSum σ Γ I t e = ∑ s, (e s : ↥(Γ ⊓ I s) → k) (t s) := rfl

variable {σ Γ I t}

theorem cx1_eval (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) (p : Z1 σ Γ × (S → k)) (s : S) :
    (cx1 σ Γ I hσ p s : ↥(Γ ⊓ I s) → k) (t s) = (p.1 : Γ → k) (tG t s) := by
  show (p.1 : Γ → k) (tG t s) - (σ (tG t s : G) (p.2 s) - p.2 s) = _
  rw [D.triv (tG t s) (p.2 s), sub_self, sub_zero]

theorem evalSum_cx1 (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) (p : Z1 σ Γ × (S → k)) :
    evalSum σ Γ I t (cx1 σ Γ I hσ p) = 0 := by
  rw [evalSum_apply]
  simp only [cx1_eval D hσ p]
  exact D.resSum p.1

/-- `H²(K) → k`, `[e] ↦ Σ_s e_s(t_s)`. -/
def h2kMap (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) : H2K σ Γ I hσ →ₗ[k] k :=
  (LinearMap.range (cx1 σ Γ I hσ)).liftQ (evalSum σ Γ I t) (by
    intro x hx
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (evalSum_cx1 D hσ p))

theorem h2kMap_mk (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) (e : (s : S) → Z1 σ (Γ ⊓ I s)) :
    h2kMap D hσ (Submodule.Quotient.mk e) = evalSum σ Γ I t e := rfl

theorem h2kMap_injective (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) :
    Function.Injective (h2kMap D hσ) := by
  rw [← LinearMap.ker_eq_bot, h2kMap]
  apply Submodule.ker_liftQ_eq_bot
  intro e he
  rw [LinearMap.mem_ker, evalSum_apply] at he
  obtain ⟨d, hd⟩ := D.resOnto (fun s => (e s : ↥(Γ ⊓ I s) → k) (t s)) he
  refine LinearMap.mem_range.2 ⟨(d, 0), funext fun s => ?_⟩
  have h0 : cx1 σ Γ I hσ (d, 0) s - e s = 0 := D.inj s _ (by
    show (cx1 σ Γ I hσ (d, 0) s : ↥(Γ ⊓ I s) → k) (t s) - (e s : ↥(Γ ⊓ I s) → k) (t s) = 0
    rw [cx1_eval D hσ]
    exact sub_eq_zero.2 (hd s))
  exact sub_eq_zero.1 h0

theorem h2kMap_surjective [Nonempty S] (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) :
    Function.Surjective (h2kMap D hσ) := by
  classical
  intro a
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  choose E hE using D.surj
  refine ⟨Submodule.Quotient.mk (fun s => E s (if s = s0 then a else 0)), ?_⟩
  rw [h2kMap_mk, evalSum_apply]
  simp only [hE]
  simp

/-- `H²(K) ≃ k` for constant coefficients. -/
def h2kEquiv [Nonempty S] (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) : H2K σ Γ I hσ ≃ₗ[k] k :=
  LinearEquiv.ofBijective (h2kMap D hσ) ⟨h2kMap_injective D hσ, h2kMap_surjective D hσ⟩

theorem h2kEquiv_mk [Nonempty S] (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G))
    (e : (s : S) → Z1 σ (Γ ⊓ I s)) : h2kEquiv D hσ (Submodule.Quotient.mk e) = evalSum σ Γ I t e := rfl

/-! ## The pairing and its boundary block -/

variable (Γ I) in
theorem zero_mem_Z1c (m : S → k) : ((0 : Γ → k), m) ∈ Z1c (Representation.trivial k G k) Γ I :=
  ⟨(Z1 _ Γ).zero_mem, fun s g _ => by simp⟩

variable (Γ I) in
/-- `k^S → H¹_c(Ū, k)`, `m ↦ [(0, m)]`. -/
def bdryMap : (S → k) →ₗ[k] H1c (Representation.trivial k G k) Γ I :=
  H1c.mk (Representation.trivial k G k) Γ I ∘ₗ
    LinearMap.codRestrict (Z1c (Representation.trivial k G k) Γ I) (LinearMap.inr k (Γ → k) (S → k))
      (zero_mem_Z1c Γ I)

theorem bdryMap_apply (m : S → k) :
    bdryMap (k := k) Γ I m =
      H1c.mk (Representation.trivial k G k) Γ I ⟨((0 : Γ → k), m), zero_mem_Z1c Γ I m⟩ := rfl

variable [Nonempty S]

/-- The constant-coefficient pairing `H¹_c(Ū, k) × H¹(Ū, k(1)) → H²(K) ≅ k`. -/
def constPair (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ) (D : ConstData σ Γ I t) :
    H1c (Representation.trivial k G k) Γ I →ₗ[k] H1 σ Γ →ₗ[k] k :=
  (cupPair (I := I) H).compr₂ (h2kEquiv D H.openL).toLinearMap

theorem constPair_mk (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (p : Z1c (Representation.trivial k G k) Γ I) (d : Z1 σ Γ) (u : Γ → k)
    (hu : IsPrim σ σ (LinearMap.mul k k) Γ (p : (Γ → k) × (S → k)).1 d u) :
    constPair H D (H1c.mk (Representation.trivial k G k) Γ I p) (H1.mk σ Γ d) =
      ∑ s, ((p : (Γ → k) × (S → k)).2 s * (d : Γ → k) (tG t s) - u (tG t s)) := by
  show h2kEquiv D H.openL (cupH H p d) = _
  rw [cupH_eq H p d u hu, h2kEquiv_mk, evalSum_apply]
  rfl

theorem constPair_bdry (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (m : S → k) (d : Z1 σ Γ) :
    constPair H D (bdryMap (k := k) Γ I m) (H1.mk σ Γ d) = ∑ s, m s * (d : Γ → k) (tG t s) := by
  have hu : IsPrim σ σ (LinearMap.mul k k) Γ (0 : Γ → k) d 0 :=
    ⟨IsLocallyConstant.const 0, fun g h => by simp [cupCochain]⟩
  rw [bdryMap_apply, constPair_mk H D ⟨((0 : Γ → k), m), zero_mem_Z1c Γ I m⟩ d 0 hu]
  simp

theorem par_eval (D : ConstData σ Γ I t) {d : Z1 σ Γ} (hd : (d : Γ → k) ∈ Z1par σ Γ I) (s : S) :
    (d : Γ → k) (tG t s) = 0 := by
  obtain ⟨-, hd'⟩ := hd
  obtain ⟨b, hb⟩ := hd' s
  rw [hb (tG t s) (Subgroup.mem_inf.1 (t s).2).2, D.triv, sub_self]

theorem constPair_h0 (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) :
    ∀ x ∈ LinearMap.range (bdryMap (k := k) Γ I), ∀ y ∈ H1par σ Γ I, constPair H D x y = 0 := by
  intro x hx y hy
  obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 hx
  obtain ⟨d, hd, rfl⟩ := Submodule.mem_map.1 hy
  rw [constPair_bdry]
  simp [par_eval D (Submodule.mem_comap.1 hd)]

/-! ## Residues `H¹(Ū, k(1)) / H¹_par → ker Σ` -/

variable (σ t) in
/-- Residues `d ↦ (d(t_s))_s`. -/
def resZ : Z1 σ Γ →ₗ[k] (S → k) := LinearMap.pi fun s => LinearMap.proj (tG t s) ∘ₗ (Z1 σ Γ).subtype

/-- Residues land in `ker Σ` (residue theorem). -/
def resZ' (D : ConstData σ Γ I t) : Z1 σ Γ →ₗ[k] sumKer S k :=
  LinearMap.codRestrict (sumKer S k) (resZ σ t) (fun d => (mem_sumKer _).2 (D.resSum d))

/-- Residues on `H¹(Γ, k(1))`. -/
def resH (D : ConstData σ Γ I t) : H1 σ Γ →ₗ[k] sumKer S k :=
  ((B1 σ Γ).comap (Z1 σ Γ).subtype).liftQ (resZ' D) (by
    intro d hd
    obtain ⟨-, b, hb⟩ := hd
    rw [LinearMap.mem_ker]
    refine Subtype.ext (funext fun s => ?_)
    show (d : Γ → k) (tG t s) = 0
    rw [show (d : Γ → k) (tG t s) = σ (tG t s : G) b - b from hb (tG t s), D.triv, sub_self])

theorem resH_mk (D : ConstData σ Γ I t) (d : Z1 σ Γ) : resH D (H1.mk σ Γ d) = resZ' D d := rfl

theorem resH_surjective (D : ConstData σ Γ I t) : Function.Surjective (resH D) := by
  rintro ⟨r, hr⟩
  obtain ⟨d, hd⟩ := D.resOnto r ((mem_sumKer r).1 hr)
  exact ⟨H1.mk σ Γ d, Subtype.ext (funext hd)⟩

theorem ker_resH (D : ConstData σ Γ I t) : LinearMap.ker (resH D) = H1par σ Γ I := by
  ext x
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h' : ∀ s, (d : Γ → k) (tG t s) = 0 := fun s => congrFun (congrArg Subtype.val h) s
    refine Submodule.mem_map.2 ⟨d, ?_, rfl⟩
    refine ⟨d.2, fun s => ⟨0, fun g hg => ?_⟩⟩
    have he := D.inj s (PerfectCx.res σ Γ inf_le_left d) (h' s)
    have h2 : (d : Γ → k) g = 0 := congrFun (congrArg Subtype.val he) ⟨g.1, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩
    rw [map_zero, sub_zero]
    exact h2
  · intro h
    obtain ⟨d', hd', hdd⟩ := Submodule.mem_map.1 h
    rw [← hdd, resH_mk]
    exact Subtype.ext (funext fun s => par_eval D (Submodule.mem_comap.1 hd') s)

variable (k Γ I) in
theorem ker_bdryMap : LinearMap.ker (bdryMap (k := k) Γ I) = constSub S k := by
  ext m
  rw [LinearMap.mem_ker, mem_constSub, bdryMap_apply, H1c.mk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  constructor
  · rintro ⟨-, c, -, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨zero_mem_Z1c Γ I m, c, fun g => by simp, hc⟩

variable (Γ I) in
/-- `k^S / k ≃ im(k^S → H¹_c)`. -/
def bdryQuotEquiv : ((S → k) ⧸ constSub S k) ≃ₗ[k] LinearMap.range (bdryMap (k := k) Γ I) :=
  (Submodule.quotEquivOfEq _ _ (ker_bdryMap k Γ I).symm).trans (bdryMap (k := k) Γ I).quotKerEquivRange

theorem bdryQuotEquiv_mk (m : S → k) :
    (bdryQuotEquiv (k := k) Γ I (Submodule.Quotient.mk m) : H1c (Representation.trivial k G k) Γ I) =
      bdryMap (k := k) Γ I m := rfl

/-- `H¹ / H¹_par ≃ ker Σ` via residues. -/
def h1QuotEquiv (D : ConstData σ Γ I t) : (H1 σ Γ ⧸ H1par σ Γ I) ≃ₗ[k] sumKer S k :=
  (Submodule.quotEquivOfEq _ _ (ker_resH D).symm).trans ((resH D).quotKerEquivOfSurjective (resH_surjective D))

theorem h1QuotEquiv_mk (D : ConstData σ Γ I t) (d : Z1 σ Γ) :
    h1QuotEquiv D (Submodule.Quotient.mk (H1.mk σ Γ d)) = resZ' D d := rfl

/-- Block A is the residue pairing. -/
theorem blockA_eq (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) :
    pairSubQuot (constPair H D) _ _ (constPair_h0 H D) =
      (resPair S k).compl₁₂ (bdryQuotEquiv (k := k) Γ I).symm.toLinearMap (h1QuotEquiv D).toLinearMap := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  obtain ⟨q, rfl⟩ := (bdryQuotEquiv (k := k) Γ I).surjective x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ y'
  rw [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    pairSubQuot_apply, bdryQuotEquiv_mk, show (Submodule.Quotient.mk d : H1 σ Γ) = H1.mk σ Γ d from rfl,
    constPair_bdry, h1QuotEquiv_mk, resPair_mk]
  rfl

theorem blockA_isPerfPair (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) : (pairSubQuot (constPair H D) _ _ (constPair_h0 H D)).IsPerfPair := by
  have : (resPair S k).IsPerfPair := resPair_isPerfPair
  rw [blockA_eq H D]
  infer_instance

/-- Constant-coefficient duality, reduced to the parabolic block (O5). -/
theorem constPair_isPerfPair (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (hB : (pairQuotSub (constPair H D) _ _ (constPair_h0 H D)).IsPerfPair) :
    (constPair H D).IsPerfPair := by
  have := blockA_isPerfPair H D
  exact isPerfPair_of_block (constPair_h0 H D)

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_CupDuality_GysA =====
section

/-!
# S4-CurveDuality O4G-1: the Gysin count for a unipotent family

Route G (session 44). On `V = (ι → k) × (ι → k)` let `Γ` act by `(a, b) ↦ (a + (d_i g · b_i)_i, b)` (`IsUniFam`) with
parabolic `d_i` (zero on every `Γ ⊓ I s`). If every `d_i` is in the right kernel of `constPair`, the cone's `H²(K)`
has at least `#(ι → k)²` elements (`card_sq_le_h2K`); the coinvariants of `V` have fewer than `#V` elements as soon as
some `d_i ≠ 0` (`card_coinv_lt`). With `H²(K) ≃ H²_c` (S4-PD) this forces `d = 0`.
* `card_sq_le_quot`: an abstract count (`(a₁, a₂) ↦ [z₁ a₁ + z₂ a₂]` is injective);
* `rho_inf`, `cx1_inf`: the action and `d¹` on `Γ ⊓ I s`; `zmk`: a cocycle on `Γ ⊓ I s` with a prescribed value;
* `snd_mem_Z1`, `prim_fst`: the components of a `V`-cocycle, and the primitive `C₁ - C₂ d` of `C₂ ∪ d`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

/-- An abstract count: `p₂` onto and killing `B ⊔ Z'`, `p₁` onto on `Z'` and killing `B ⊓ Z'`. -/
theorem card_sq_le_quot {k Z A : Type} [CommRing k] [AddCommGroup Z] [Module k Z] [AddCommGroup A] [Module k A]
    (B Z' : Submodule k Z) (p1 p2 : Z →ₗ[k] A) (h2 : Function.Surjective p2)
    (h1 : ∀ a, ∃ z ∈ Z', p1 z = a) (hB2 : ∀ z ∈ B, p2 z = 0) (hZ2 : ∀ z ∈ Z', p2 z = 0)
    (hB1 : ∀ z ∈ B, z ∈ Z' → p1 z = 0) [Finite (Z ⧸ B)] :
    Nat.card A * Nat.card A ≤ Nat.card (Z ⧸ B) := by
  classical
  choose z1 hz1 hp1 using h1
  choose z2 hp2 using h2
  have hinj : Function.Injective (fun a : A × A => (Submodule.Quotient.mk (z1 a.1 + z2 a.2) : Z ⧸ B)) := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    have h' : (z1 a1 + z2 a2) - (z1 b1 + z2 b2) ∈ B := (Submodule.Quotient.eq B).1 h
    have hm := hB2 _ h'
    rw [map_sub, map_add, map_add, hp2, hp2, hZ2 _ (hz1 a1), hZ2 _ (hz1 b1), zero_add, zero_add,
      sub_eq_zero] at hm
    subst hm
    have hd : z1 a1 - z1 b1 ∈ B := by
      have : (z1 a1 + z2 a2) - (z1 b1 + z2 a2) = z1 a1 - z1 b1 := by abel
      rwa [this] at h'
    have h0 := hB1 _ hd (Z'.sub_mem (hz1 a1) (hz1 b1))
    rw [map_sub, hp1, hp1, sub_eq_zero] at h0
    rw [h0]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

section Gys

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {ι : Type} [Fintype ι]

/-- `Γ` acts on `(ι → k) × (ι → k)` by `(a, b) ↦ (a + (d_i g · b_i)_i, b)`. -/
def IsUniFam (ρ : Representation k G ((ι → k) × (ι → k))) (d : ι → Γ → k) : Prop :=
  ∀ (g : Γ) (v : (ι → k) × (ι → k)), ρ (g : G) v = (v.1 + fun i => d i g * v.2 i, v.2)

variable {ρ : Representation k G ((ι → k) × (ι → k))} {d : ι → Γ → k}

theorem rho_inf (hρΓ : IsUniFam ρ d) (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0) (s : S)
    (g : ↥(Γ ⊓ I s)) (v : (ι → k) × (ι → k)) : ρ (g : G) v = v := by
  have h0 : ∀ i, d i ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ = 0 := fun i => hpar i s _ (Subgroup.mem_inf.1 g.2).2
  have := hρΓ ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ v
  refine this.trans ?_
  ext i <;> simp [h0]

theorem cx1_inf (hρ : IsOpen (ρ.ker : Set G)) (hρΓ : IsUniFam ρ d)
    (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0) (p : Z1 ρ Γ × (S → (ι → k) × (ι → k))) (s : S)
    (g : ↥(Γ ⊓ I s)) :
    (cx1 ρ Γ I hρ p s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) g =
      (p.1 : Γ → (ι → k) × (ι → k)) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ := by
  rw [cx1_apply, rho_inf hρΓ hpar s g, sub_self, sub_zero]

/-- `g ↦ e(g) • v` is a cocycle on `Γ ⊓ I s` (`e` a hom, the action trivial there). -/
def zmk (DD : ConstData σ Γ I t) (hρΓ : IsUniFam ρ d) (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0)
    (s : S) (e : Z1 σ (Γ ⊓ I s)) (v : (ι → k) × (ι → k)) : Z1 ρ (Γ ⊓ I s) :=
  ⟨fun g => (e : ↥(Γ ⊓ I s) → k) g • v, (mem_Z1 ρ _ _).2 ⟨((mem_Z1 σ _ _).1 e.2).1.comp (· • v), fun g h => by
    rw [((mem_Z1 σ _ _).1 e.2).2 g h, DD.triv ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, rho_inf hρΓ hpar s g, add_smul]⟩⟩

theorem zmk_apply (DD : ConstData σ Γ I t) (hρΓ : IsUniFam ρ d)
    (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0) (s : S) (e : Z1 σ (Γ ⊓ I s)) (v : (ι → k) × (ι → k))
    (g : ↥(Γ ⊓ I s)) :
    (zmk DD hρΓ hpar s e v : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) g = (e : ↥(Γ ⊓ I s) → k) g • v := rfl

variable (ρ t) in
/-- `z ↦ Σ_s r(z_s(t_s))`. -/
def prR (r : (ι → k) × (ι → k) →ₗ[k] (ι → k)) : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] (ι → k) where
  toFun z := ∑ s, r ((z s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) (t s))
  map_add' z z' := by simp [Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.smul_sum]

theorem prR_apply (r : (ι → k) × (ι → k) →ₗ[k] (ι → k)) (z : (s : S) → Z1 ρ (Γ ⊓ I s)) :
    prR t ρ r z = ∑ s, r ((z s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) (t s)) := rfl

variable (ρ I) in
/-- Boundary families with vanishing second component. -/
def zSnd0 : Submodule k ((s : S) → Z1 ρ (Γ ⊓ I s)) where
  carrier := {z | ∀ (s : S) (g : ↥(Γ ⊓ I s)), ((z s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) g).2 = 0}
  add_mem' := by
    intro z z' hz hz' s g
    simp [hz s g, hz' s g]
  zero_mem' := fun s g => by simp
  smul_mem' := by
    intro a z hz s g
    simp [hz s g]

theorem mem_zSnd0 (z : (s : S) → Z1 ρ (Γ ⊓ I s)) : z ∈ zSnd0 I ρ ↔
    ∀ (s : S) (g : ↥(Γ ⊓ I s)), ((z s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) g).2 = 0 := Iff.rfl

/-- The `i`-th second component of a `V`-cocycle is a hom, i.e. lies in `Z¹(Γ, k(1))`. -/
theorem snd_mem_Z1 (DD : ConstData σ Γ I t) (hρΓ : IsUniFam ρ d) (C : Z1 ρ Γ) (i : ι) :
    (fun g => ((C : Γ → (ι → k) × (ι → k)) g).2 i) ∈ Z1 σ Γ := by
  refine (mem_Z1 σ Γ _).2 ⟨((mem_Z1 ρ Γ _).1 C.2).1.comp (fun v => v.2 i), fun g h => ?_⟩
  rw [((mem_Z1 ρ Γ _).1 C.2).2 g h, DD.triv g, hρΓ g]
  rfl

theorem snd_mem_Z1_triv (hρΓ : IsUniFam ρ d) (C : Z1 ρ Γ) (i : ι) :
    (fun g => ((C : Γ → (ι → k) × (ι → k)) g).2 i) ∈ Z1 (Representation.trivial k G k) Γ := by
  refine (mem_Z1 _ Γ _).2 ⟨((mem_Z1 ρ Γ _).1 C.2).1.comp (fun v => v.2 i), fun g h => ?_⟩
  rw [((mem_Z1 ρ Γ _).1 C.2).2 g h, Representation.trivial_apply, hρΓ g]
  rfl

/-- `C₁ - C₂ d` is a primitive of `C₂ ∪ d` (componentwise). -/
theorem prim_fst (DD : ConstData σ Γ I t) (hρΓ : IsUniFam ρ d) (hd : ∀ i, d i ∈ Z1 σ Γ) (C : Z1 ρ Γ) (i : ι) :
    IsPrim σ σ (LinearMap.mul k k) Γ (fun g => ((C : Γ → (ι → k) × (ι → k)) g).2 i) (d i)
      (fun g => ((C : Γ → (ι → k) × (ι → k)) g).1 i - ((C : Γ → (ι → k) × (ι → k)) g).2 i * d i g) := by
  have hC := ((mem_Z1 ρ Γ _).1 C.2).2
  have hdi := ((mem_Z1 σ Γ _).1 (hd i)).2
  refine ⟨(((mem_Z1 ρ Γ _).1 C.2).1.comp (fun v => v.1 i)).sub
    ((((mem_Z1 ρ Γ _).1 C.2).1.comp (fun v => v.2 i)).mul ((mem_Z1 σ Γ _).1 (hd i)).1), fun g h => ?_⟩
  simp only [cupCochain, LinearMap.mul_apply', DD.triv]
  have e1 : ((C : Γ → (ι → k) × (ι → k)) (g * h)).1 i =
      ((C : Γ → (ι → k) × (ι → k)) g).1 i + ((C : Γ → (ι → k) × (ι → k)) h).1 i +
        d i g * ((C : Γ → (ι → k) × (ι → k)) h).2 i := by
    rw [hC g h, hρΓ g]
    simp only [Prod.fst_add, Pi.add_apply]
    ring
  have e2 : ((C : Γ → (ι → k) × (ι → k)) (g * h)).2 i =
      ((C : Γ → (ι → k) × (ι → k)) g).2 i + ((C : Γ → (ι → k) × (ι → k)) h).2 i := by
    rw [hC g h, hρΓ g]
    rfl
  have e3 : d i (g * h) = d i g + d i h := by rw [hdi g h, DD.triv]
  rw [e1, e2, e3]
  ring

variable [DecidableEq S] [Nonempty S]

/-- **Gysin count**: if every `d_i` is in the right kernel of `constPair`, `#H²(K; V) ≥ #(ι → k)²`. -/
theorem card_sq_le_h2K (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (DD : ConstData σ Γ I t) (hρ : IsOpen (ρ.ker : Set G)) (hρΓ : IsUniFam ρ d)
    (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0) (hd : ∀ i, d i ∈ Z1 σ Γ)
    (hR : ∀ i (p : Z1c (Representation.trivial k G k) Γ I),
      constPair H DD (H1c.mk (Representation.trivial k G k) Γ I p) (H1.mk σ Γ ⟨d i, hd i⟩) = 0)
    [Finite (H2K ρ Γ I hρ)] :
    Nat.card (ι → k) * Nat.card (ι → k) ≤ Nat.card (H2K ρ Γ I hρ) := by
  classical
  choose e he using fun s => DD.surj s 1
  have hsum : ∀ (r : (ι → k) × (ι → k) →ₗ[k] (ι → k)) (v : (ι → k) × (ι → k)) (s0 : S),
      prR t ρ r (fun s => zmk DD hρΓ hpar s (e s) (if s = s0 then v else 0)) = r v := by
    intro r v s0
    rw [prR_apply, Finset.sum_eq_single s0]
    · rw [zmk_apply, he, one_smul, if_pos rfl]
    · intro s _ hs
      rw [zmk_apply, if_neg hs, smul_zero, map_zero]
    · intro h
      exact absurd (Finset.mem_univ s0) h
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  refine card_sq_le_quot (LinearMap.range (cx1 ρ Γ I hρ)) (zSnd0 I ρ) (prR t ρ (LinearMap.fst k _ _))
    (prR t ρ (LinearMap.snd k _ _)) (fun a => ⟨_, hsum _ (0, a) s0⟩)
    (fun a => ⟨_, (mem_zSnd0 _).2 fun s g => ?_, hsum _ (a, 0) s0⟩) ?_ ?_ ?_
  · rw [zmk_apply]
    split_ifs <;> simp
  · rintro z ⟨p, rfl⟩
    funext i
    rw [prR_apply, Finset.sum_apply]
    simp only [LinearMap.snd_apply, cx1_inf hρ hρΓ hpar]
    exact DD.resSum ⟨_, snd_mem_Z1 DD hρΓ p.1 i⟩
  · intro z hz
    funext i
    rw [prR_apply, Finset.sum_apply]
    simp only [LinearMap.snd_apply]
    exact Finset.sum_eq_zero fun s _ => by rw [(mem_zSnd0 _).1 hz s (t s)]; rfl
  · rintro z ⟨p, rfl⟩ hz
    funext i
    rw [prR_apply, Finset.sum_apply]
    simp only [LinearMap.fst_apply, cx1_inf hρ hρΓ hpar]
    have hun : ∀ (s : S) (g : Γ), (g : G) ∈ I s → ((p.1 : Γ → (ι → k) × (ι → k)) g).2 i = 0 := by
      intro s g hg
      have := (mem_zSnd0 _).1 hz s ⟨g.1, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩
      rw [cx1_inf hρ hρΓ hpar] at this
      exact congrFun this i
    have hpc : ((fun g => ((p.1 : Γ → (ι → k) × (ι → k)) g).2 i), (0 : S → k)) ∈
        Z1c (Representation.trivial k G k) Γ I :=
      (mem_Z1c _ Γ I _).2 ⟨snd_mem_Z1_triv hρΓ p.1 i, fun s g hg => (hun s g hg).trans (by simp)⟩
    have hc := constPair_mk H DD ⟨_, hpc⟩ ⟨d i, hd i⟩ _ (prim_fst DD hρΓ hd p.1 i)
    rw [hR i ⟨_, hpc⟩] at hc
    have ht : ∀ s, ((p.1 : Γ → (ι → k) × (ι → k)) (tG t s)).2 i = 0 :=
      fun s => hun s (tG t s) (Subgroup.mem_inf.1 (t s).2).2
    simp only [Pi.zero_apply, zero_mul, zero_sub, ht, Finset.sum_neg_distrib] at hc
    simpa [tG] using hc.symm

omit [DecidableEq S] [Nonempty S] in
/-- The coinvariants are smaller than `V` as soon as some `d_i ≠ 0`. -/
theorem card_coinv_lt [Finite k] (hρΓ : IsUniFam ρ d) {i : ι} {g : Γ} (hg : d i g ≠ 0) :
    Nat.card (H2c ρ Γ) < Nat.card ((ι → k) × (ι → k)) := by
  classical
  let v : (ι → k) × (ι → k) := (0, Pi.single i 1)
  have hw : (ρ.comp Γ.subtype) g v - v ∈ Representation.Coinvariants.ker (ρ.comp Γ.subtype) :=
    Representation.Coinvariants.sub_mem_ker g v
  have hne : (ρ.comp Γ.subtype) g v - v ≠ 0 := by
    intro h
    have h1 := congrArg (fun w : (ι → k) × (ι → k) => w.1 i) h
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hρΓ g, v] at h1
    simp at h1
    exact hg h1
  have hK : 1 < Nat.card (Representation.Coinvariants.ker (ρ.comp Γ.subtype)) := by
    have : Nontrivial (Representation.Coinvariants.ker (ρ.comp Γ.subtype)) :=
      ⟨⟨⟨_, hw⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hcard := Submodule.card_eq_card_quotient_mul_card (Representation.Coinvariants.ker (ρ.comp Γ.subtype))
  have hQ : Nat.card (H2c ρ Γ) =
      Nat.card (((ι → k) × (ι → k)) ⧸ Representation.Coinvariants.ker (ρ.comp Γ.subtype)) := rfl
  have hfin : Finite (((ι → k) × (ι → k)) ⧸ Representation.Coinvariants.ker (ρ.comp Γ.subtype)) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hpos : 0 < Nat.card (((ι → k) × (ι → k)) ⧸ Representation.Coinvariants.ker (ρ.comp Γ.subtype)) :=
    Nat.card_pos
  rw [hQ, hcard]
  exact lt_mul_of_one_lt_left hpos hK

end Gys

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_ConeDuality_Frob =====
section

/-!
# S4-CurveDuality O6b: Frobenius on the constant-coefficient pairing

* `frobH2c_eq_smul`: on `H²_c` with one-dimensional coefficients `σ : Representation k G k`, Frobenius
  `frobH2c σ Γ ψ χ` is the scalar `χ · σ(ψ)(1)` (no hypothesis on `σ`);
* `frobH2K_eq_smul`: hence the same holds on the cone's `H²(K)` as soon as some `k`-linear `E : H²(K) ≃ H²_c`
  intertwines the two Frobenius maps (S4-PD's `h2Equiv_lisse` provides such an `E`);
* `constPair_frob`: if Frobenius is the scalar `c` on `H²(K)`, the constant-coefficient pairing satisfies
  `⟨F x, F y⟩ = c · ⟨x, y⟩`; `constPair_frob_of_equiv` with `c = χ · σ(ψ)(1)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

/-- A map conjugate (through a linear equivalence) to a scalar is that scalar. -/
theorem eq_smul_of_conj {k : Type} [CommRing k] {A B : Type} [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (E : A ≃ₗ[k] B) {FA : A →ₗ[k] A} {FB : B →ₗ[k] B} {c : k} (hE : ∀ x, E (FA x) = FB (E x))
    (hB : ∀ y, FB y = c • y) (x : A) : FA x = c • x :=
  E.injective (by rw [hE, hB, map_smul])

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation k G k) (Γ : Subgroup G) [Γ.Normal]

/-- On `H²_c` with one-dimensional coefficients, Frobenius is the scalar `χ · σ(ψ)(1)`. -/
theorem frobH2c_eq_smul (ψ : G) (χ : k) (z : H2c σ Γ) : frobH2c σ Γ ψ χ z = (χ * σ ψ 1) • z := by
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  have hx : σ ψ x = σ ψ 1 • x := by
    rw [smul_eq_mul, mul_comm]
    conv_lhs => rw [← mul_one x]
    rw [← smul_eq_mul x (1 : k), map_smul, smul_eq_mul]
  rw [frobH2c_mk, hx, map_smul, smul_smul]

variable {S : Type} (I : S → Subgroup G)

/-- Frobenius on the cone's `H²` is the scalar `χ · σ(ψ)(1)` when it is conjugate to `frobH2c`. -/
theorem frobH2K_eq_smul (hσ : IsOpen (σ.ker : Set G)) (ψ : G) (τ : S → S) (h : S → Γ)
    (hI : BdryCompat Γ I ψ τ h) (χ : k) (E : H2K σ Γ I hσ ≃ₗ[k] H2c σ Γ)
    (hE : ∀ x, E (frobH2K σ Γ I ψ τ h hσ hI x) = frobH2c σ Γ ψ χ (E x)) (z : H2K σ Γ I hσ) :
    frobH2K σ Γ I ψ τ h hσ hI z = (χ * σ ψ 1) • z :=
  eq_smul_of_conj E hE (frobH2c_eq_smul σ Γ ψ χ) z

variable [Fintype S] [Nonempty S] {σ Γ I} {t : (s : S) → ↥(Γ ⊓ I s)}

/-- Frobenius on the constant-coefficient pairing: `⟨F x, F y⟩ = c · ⟨x, y⟩` when `F = c` on `H²(K)`. -/
theorem constPair_frob (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (c : k)
    (hF : ∀ z, frobH2K σ Γ I ψ τ h H.openL hI z = c • z)
    (x : H1c (Representation.trivial k G k) Γ I) (y : H1 σ Γ) :
    constPair H D (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI x) (frobH1 σ Γ ψ y) =
      c * constPair H D x y := by
  show h2kEquiv D H.openL (cupPair H (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI x)
      (frobH1 σ Γ ψ y)) = c * h2kEquiv D H.openL (cupPair H x y)
  rw [cupPair_frob H ψ τ h hI x y, hF, map_smul, smul_eq_mul]

/-- `constPair_frob` with the scalar read off from an intertwiner `E : H²(K) ≃ H²_c` (S4-PD). -/
theorem constPair_frob_of_equiv (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (χ : k)
    (E : H2K σ Γ I H.openL ≃ₗ[k] H2c σ Γ)
    (hE : ∀ x, E (frobH2K σ Γ I ψ τ h H.openL hI x) = frobH2c σ Γ ψ χ (E x))
    (x : H1c (Representation.trivial k G k) Γ I) (y : H1 σ Γ) :
    constPair H D (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI x) (frobH1 σ Γ ψ y) =
      (χ * σ ψ 1) * constPair H D x y :=
  constPair_frob H D ψ τ h hI _ (frobH2K_eq_smul σ Γ I H.openL ψ τ h hI χ E hE) x y

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_Red =====
section

/-!
# S4-PD (5), E3: reduction mod `t` (e.g. `ℓⁿ → ℓᵐ`)

`Λ' = Λ/(t)` is encoded as a `Λ`-algebra with `algebraMap` onto, `t ↦ 0` and kernel `t Λ`. A `Λ`-linear `f : V → V'`
onto a `Λ'`-module with kernel in `t V` induces `Λ' ⊗ V ≃ V'` (`redEquiv`), which intertwines base changes of maps
compatible with the reductions (`redEquiv_comm`); Hattori–Stallings traces then reduce (`hs_red_of`). For
`A = Λ[Gf]`: coefficientwise reduction `redA` (onto, kernel `t A`) and the induced map on cocycles
`redZ1 : Z¹(Δ; Λ[Gf]) → Z¹(Δ; Λ'[Gf])`, onto with kernel `t Z¹` under `H2All` (`redZ1_surjective`, `redZ1_ker`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings TensorProduct

noncomputable section

section BC

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] (t : Λ)
  (hsurj : Function.Surjective (algebraMap Λ Λ')) (ht : algebraMap Λ Λ' t = 0)
  {V V' : Type} [AddCommGroup V] [Module Λ V] [AddCommGroup V'] [Module Λ V'] [Module Λ' V']
  [IsScalarTower Λ Λ' V']

include hsurj in
/-- Every element of `Λ' ⊗ V` is `1 ⊗ x` (`algebraMap` onto). -/
theorem exists_one_tmul_of_surj (u : Λ' ⊗[Λ] V) : ∃ x : V, u = 1 ⊗ₜ x := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, (tmul_zero _ _).symm⟩
  | tmul r v =>
    obtain ⟨a, rfl⟩ := hsurj r
    exact ⟨a • v, by rw [← smul_tmul, Algebra.algebraMap_eq_smul_one]⟩
  | add u v hu hv =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x + y, (tmul_add _ _ _).symm⟩

include hsurj ht in
/-- If `f : V → V'` is onto with kernel inside `t • V`, then `Λ' ⊗ V → V'` is bijective. -/
theorem bijective_liftBaseChange (f : V →ₗ[Λ] V') (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 → ∃ y, x = t • y) : Function.Bijective (f.liftBaseChange Λ') := by
  refine ⟨fun u v huv => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := exists_one_tmul_of_surj hsurj u
    obtain ⟨x', rfl⟩ := exists_one_tmul_of_surj hsurj v
    rw [LinearMap.liftBaseChange_one_tmul, LinearMap.liftBaseChange_one_tmul, ← sub_eq_zero, ← map_sub] at huv
    obtain ⟨z, hz⟩ := hk _ huv
    rw [← sub_eq_zero, ← tmul_sub, hz, ← smul_tmul, ← Algebra.algebraMap_eq_smul_one, ht, zero_tmul]
  · obtain ⟨x, rfl⟩ := hf y
    exact ⟨1 ⊗ₜ x, LinearMap.liftBaseChange_one_tmul _ _ _⟩

/-- `Λ' ⊗ V ≃ V'` from `f` onto with kernel in `t • V`. -/
def redEquiv (f : V →ₗ[Λ] V') (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → ∃ y, x = t • y) :
    Λ' ⊗[Λ] V ≃ₗ[Λ'] V' :=
  LinearEquiv.ofBijective _ (bijective_liftBaseChange t hsurj ht f hf hk)

theorem redEquiv_one_tmul (f : V →ₗ[Λ] V') (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 → ∃ y, x = t • y) (x : V) : redEquiv t hsurj ht f hf hk (1 ⊗ₜ x) = f x :=
  LinearMap.liftBaseChange_one_tmul _ _ _

variable {W W' : Type} [AddCommGroup W] [Module Λ W] [AddCommGroup W'] [Module Λ W'] [Module Λ' W']
  [IsScalarTower Λ Λ' W']

/-- `redEquiv` intertwines `d ⊗ Λ'` with `d'` when `g ∘ d = d' ∘ f`. -/
theorem redEquiv_comm (f : V →ₗ[Λ] V') (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → ∃ y, x = t • y)
    (g : W →ₗ[Λ] W') (hg : Function.Surjective g) (hkg : ∀ x, g x = 0 → ∃ y, x = t • y)
    (d : V →ₗ[Λ] W) (d' : V' →ₗ[Λ'] W') (hd : ∀ x, g (d x) = d' (f x)) (u : Λ' ⊗[Λ] V) :
    redEquiv t hsurj ht g hg hkg (d.baseChange Λ' u) = d' (redEquiv t hsurj ht f hf hk u) := by
  obtain ⟨x, rfl⟩ := exists_one_tmul_of_surj hsurj u
  rw [LinearMap.baseChange_tmul, redEquiv_one_tmul, redEquiv_one_tmul, hd]

variable {G : Type} [Group G] [Fintype G]

include hsurj ht in
/-- **Reduction of Hattori–Stallings traces**: if `f : V → V'` is onto with kernel in `t • V` and intertwines `ρ, φ`
with `ρ', φ'`, then `hs ρ' φ' = algebraMap (hs ρ φ)`. -/
theorem hs_red_of [Module.Free Λ V] [Module.Finite Λ V] [Module.Free Λ' V'] [Module.Finite Λ' V']
    {ρ : Representation Λ G V} (hρ : IsProj ρ) {ρ' : Representation Λ' G V'} {φ : V →ₗ[Λ] V}
    (hφ : IsEquivariant ρ ρ φ) (φ' : V' →ₗ[Λ'] V') (f : V →ₗ[Λ] V') (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 → ∃ y, x = t • y) (hfρ : ∀ g x, f (ρ g x) = ρ' g (f x))
    (hfφ : ∀ x, f (φ x) = φ' (f x)) (c : ConjClasses G) :
    hs ρ' φ' c = algebraMap Λ Λ' (hs ρ φ c) := by
  let e := redEquiv t hsurj ht f hf hk
  have he : IsEquivariant (repBaseChange Λ' ρ) ρ' e.toLinearMap := isEquivariant_iff.2 fun g u =>
    redEquiv_comm t hsurj ht f hf hk f hf hk (ρ g) (ρ' g) (hfρ g) u
  have hφ' : e.toLinearMap ∘ₗ φ.baseChange Λ' ∘ₗ e.symm.toLinearMap = φ' := LinearMap.ext fun y => by
    obtain ⟨u, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact redEquiv_comm t hsurj ht f hf hk f hf hk φ φ' hfφ u
  rw [← hφ', hs_conj hρ.baseChange e he hφ.baseChange]
  exact hs_baseChange hρ hφ c

end BC

section RedA

variable (Λ Λ' : Type) [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] (Gf : Type) [Group Gf]

/-- Coefficientwise reduction `Λ[Gf] → Λ'[Gf]`. -/
def redA : MonoidAlgebra Λ Gf →ₗ[Λ] MonoidAlgebra Λ' Gf :=
  (mapAlgHom Gf (Algebra.ofId Λ Λ')).toLinearMap

variable {Λ Λ' Gf}

theorem redA_coeff (a : MonoidAlgebra Λ Gf) (x : Gf) :
    (redA Λ Λ' Gf a).coeff x = algebraMap Λ Λ' (a.coeff x) :=
  coeff_mapAlgHom _ _ _

theorem redA_mul (a b : MonoidAlgebra Λ Gf) : redA Λ Λ' Gf (a * b) = redA Λ Λ' Gf a * redA Λ Λ' Gf b :=
  map_mul (mapAlgHom Gf (Algebra.ofId Λ Λ')) a b

theorem redA_single (x : Gf) : redA Λ Λ' Gf (single x 1) = single x 1 := by
  show mapAlgHom Gf (Algebra.ofId Λ Λ') (single x 1) = single x 1
  rw [mapAlgHom_single, map_one]

theorem redA_mul_single (x : Gf) (a : MonoidAlgebra Λ Gf) :
    redA Λ Λ' Gf (single x 1 * a) = single x 1 * redA Λ Λ' Gf a := by
  rw [redA_mul, redA_single]

theorem redA_mul_single' (a : MonoidAlgebra Λ Gf) (x : Gf) :
    redA Λ Λ' Gf (a * single x 1) = redA Λ Λ' Gf a * single x 1 := by
  rw [redA_mul, redA_single]

theorem redA_surjective [Finite Gf] (hsurj : Function.Surjective (algebraMap Λ Λ')) :
    Function.Surjective (redA Λ Λ' Gf) := fun b => by
  choose y hy using fun x => hsurj (b.coeff x)
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm y), ?_⟩
  ext x
  rw [redA_coeff]
  exact hy x

theorem redA_ker [Finite Gf] {t : Λ} (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s)
    (a : MonoidAlgebra Λ Gf) (ha : redA Λ Λ' Gf a = 0) : ∃ b : MonoidAlgebra Λ Gf, a = t • b := by
  have hx : ∀ x : Gf, ∃ y, a.coeff x = t * y := fun x => hk _ (by rw [← redA_coeff, ha]; rfl)
  choose y hy using hx
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm y), ?_⟩
  ext x
  rw [coeff_smul_apply, hy x, smul_eq_mul]
  rfl

end RedA

section RedZ1

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf)

theorem redA_regRep (g : G) (a : MonoidAlgebra Λ Gf) :
    redA Λ Λ' Gf (regRep Λ π g a) = regRep Λ' π g (redA Λ Λ' Gf a) :=
  redA_mul_single _ _

variable (Λ Λ') in
/-- `G` acting on `Λ'[Gf]` by left multiplication through `π`, as a `Λ`-representation. -/
def regRepR : Representation Λ G (MonoidAlgebra Λ' Gf) where
  toFun g := (regRep Λ' π g).restrictScalars Λ
  map_one' := LinearMap.ext fun a => show regRep Λ' π 1 a = a by rw [map_one]; rfl
  map_mul' x y := LinearMap.ext fun a =>
    show regRep Λ' π (x * y) a = regRep Λ' π x (regRep Λ' π y a) by rw [map_mul]; rfl

variable (Λ Λ') in
/-- Reduction of cocycles `Z¹(Δ; Λ[Gf]) → Z¹(Δ; Λ'[Gf])` (values reduced coefficientwise). -/
def redZ1 (Δ : Subgroup G) : Z1 (regRep Λ π) Δ →ₗ[Λ] Z1 (regRep Λ' π) Δ where
  toFun c := ⟨fun g => redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g), (mem_Z1 (regRep Λ' π) Δ _).2
    ⟨((mem_Z1 (regRep Λ π) Δ _).1 c.2).1.comp _, fun g g' => by
      simp only [((mem_Z1 (regRep Λ π) Δ _).1 c.2).2 g g', map_add, redA_regRep]⟩⟩
  map_add' c d := Subtype.ext (funext fun g => by
    show redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g + (d : Δ → MonoidAlgebra Λ Gf) g) =
      redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g) + redA Λ Λ' Gf ((d : Δ → MonoidAlgebra Λ Gf) g)
    exact map_add _ _ _)
  map_smul' r c := Subtype.ext (funext fun g => by
    show redA Λ Λ' Gf (r • (c : Δ → MonoidAlgebra Λ Gf) g) = r • redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g)
    exact map_smul _ _ _)

theorem redZ1_apply (Δ : Subgroup G) (c : Z1 (regRep Λ π) Δ) (g : Δ) :
    (redZ1 Λ Λ' π Δ c : Δ → MonoidAlgebra Λ' Gf) g = redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g) := rfl

/-- Reduction of cocycles is onto (`H2All`). -/
theorem redZ1_surjective [Finite Λ] [Finite Gf] (hsurj : Function.Surjective (algebraMap Λ Λ')) {l N : ℕ}
    (hΛ : ((l ^ N : ℕ) : Λ) = 0) (Δ : Subgroup G) (hall : H2All Λ G Δ l N) (hπ : IsOpen (π.ker : Set G)) :
    Function.Surjective (redZ1 Λ Λ' π Δ) := fun z => by
  have := finite_A Λ Gf
  obtain ⟨c, hc⟩ := z1Map_surjective_of_all (regRep Λ π) (regRepR Λ Λ' π) Δ hall (nsmul_eq_zero_of_cast hΛ)
    (isOpen_regRep_ker π hπ) (redA Λ Λ' Gf) (redA_regRep π) (redA_surjective hsurj)
    ⟨(z : Δ → MonoidAlgebra Λ' Gf), (mem_Z1 (regRepR Λ Λ' π) Δ _).2 ((mem_Z1 (regRep Λ' π) Δ _).1 z.2)⟩
  exact ⟨c, Subtype.ext (congrArg Subtype.val hc)⟩

/-- The kernel of the reduction of cocycles is `t • Z¹` (`H2All`). -/
theorem redZ1_ker [Finite Λ] [Finite Gf] {t : Λ} (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s) {l N : ℕ}
    (hΛ : ((l ^ N : ℕ) : Λ) = 0) (Δ : Subgroup G) (hall : H2All Λ G Δ l N) (hπ : IsOpen (π.ker : Set G))
    (c : Z1 (regRep Λ π) Δ) (hc : redZ1 Λ Λ' π Δ c = 0) : ∃ d, c = t • d := by
  have := finite_A Λ Gf
  have hv : ∀ g, (c : Δ → MonoidAlgebra Λ Gf) g ∈ (smulRep π t).toSubmodule := fun g => by
    have h0 : redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g) = 0 := by
      have := congrArg (fun z : Z1 (regRep Λ' π) Δ => (z : Δ → MonoidAlgebra Λ' Gf) g) hc
      exact this
    obtain ⟨b, hb⟩ := redA_ker hk _ h0
    exact ⟨b, by simp [hb]⟩
  obtain ⟨d, hd⟩ := lift_of_values (regRep Λ π) (regRep Λ π) Δ hall (nsmul_eq_zero_of_cast hΛ)
    (isOpen_regRep_ker π hπ) (LinearMap.lsmul Λ (MonoidAlgebra Λ Gf) t) (fun g a => by simp)
    (smulRep π t) (fun a => ⟨a, rfl⟩) (fun w hw => hw) c hv
  refine ⟨d, Subtype.ext (funext fun g => ?_)⟩
  rw [coe_smul_Z1, ← hd g]
  rfl

end RedZ1

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_RedPC =====
section

/-!
# S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)

Termwise reductions `redA`, `red1`, `red2` of `PC Λ → PC Λ'` are onto with kernel `t • PC` (`H2All`), commute with
the `Gf`-actions, the Frobenius and the differentials, so `Λ' ⊗ PC Λ i ≃ PC Λ' i` (`pcRed0`, `pcRed1`, `pcRed2`,
compatibilities via `redEquiv_comm`) and the Lefschetz numbers of the Frobenius reduce (`lefschetz_frob_red`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings TensorProduct

noncomputable section

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

theorem redA_rRep (x : Gf) (a : MonoidAlgebra Λ Gf) :
    redA Λ Λ' Gf (rRep Λ Gf x a) = rRep Λ' Gf x (redA Λ Λ' Gf a) := redA_mul_single' _ _

theorem redZ1_eRep (Δ : Subgroup G) (x : Gf) (c : Z1 (regRep Λ π) Δ) :
    redZ1 Λ Λ' π Δ (eRep (Λ := Λ) π Δ x c) = eRep (Λ := Λ') π Δ x (redZ1 Λ Λ' π Δ c) :=
  Subtype.ext (funext fun _ => redA_mul_single' _ _)

theorem redZ1_conj (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (c : Z1 (regRep Λ π) Δ') :
    redZ1 Λ Λ' π Δ (conjMap (regRep Λ π) x hx c) = conjMap (regRep Λ' π) x hx (redZ1 Λ Λ' π Δ' c) :=
  Subtype.ext (funext fun _ => redA_regRep π x _)

variable (Λ Λ') in
/-- Reduction on `P¹ = E_Γ × A^S`. -/
def red1 : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf) →ₗ[Λ] Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf) :=
  (redZ1 Λ Λ' π Γ).prodMap (LinearMap.piMap fun _ => redA Λ Λ' Gf)

variable (Λ Λ') in
/-- Reduction on `P² = Π_s E_s`. -/
def red2 : ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) →ₗ[Λ] ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) :=
  LinearMap.piMap fun s => redZ1 Λ Λ' π (Γ ⊓ I s)

theorem red1_rho1 (x : Gf) (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :
    red1 Λ Λ' π Γ (rho1 Λ π Γ S x p) = rho1 Λ' π Γ S x (red1 Λ Λ' π Γ p) :=
  Prod.ext (redZ1_eRep π Γ x p.1) (funext fun s => redA_rRep x (p.2 s))

theorem red2_rho2 (x : Gf) (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    red2 Λ Λ' π Γ I (rho2 Λ π Γ I x e) = rho2 Λ' π Γ I x (red2 Λ Λ' π Γ I e) :=
  funext fun s => redZ1_eRep π (Γ ⊓ I s) x (e s)

theorem red1_d0 (hπ : IsOpen (π.ker : Set G)) (a : MonoidAlgebra Λ Gf) :
    red1 Λ Λ' π Γ (d0 Λ π Γ S hπ a) = d0 Λ' π Γ S hπ (redA Λ Λ' Gf a) :=
  Prod.ext (Subtype.ext (funext fun g => by
    show redA Λ Λ' Gf (regRep Λ π g a - a) = regRep Λ' π g (redA Λ Λ' Gf a) - redA Λ Λ' Gf a
    rw [map_sub, redA_regRep])) rfl

theorem red2_d1 (hπ : IsOpen (π.ker : Set G)) (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :
    red2 Λ Λ' π Γ I (d1 Λ π Γ I hπ p) = d1 Λ' π Γ I hπ (red1 Λ Λ' π Γ p) :=
  funext fun s => Subtype.ext (funext fun g => by
    show redA Λ Λ' Gf ((p.1 : Γ → MonoidAlgebra Λ Gf) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ -
        (regRep Λ π g (p.2 s) - p.2 s)) =
      redA Λ Λ' Gf ((p.1 : Γ → MonoidAlgebra Λ Gf) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩) -
        (regRep Λ' π g (redA Λ Λ' Gf (p.2 s)) - redA Λ Λ' Gf (p.2 s))
    rw [map_sub, map_sub, redA_regRep])

section Frob

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

theorem red1_frob (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :
    red1 Λ Λ' π Γ (frob1 (regRep Λ π) Γ ψ t h p) = frob1 (regRep Λ' π) Γ ψ t h (red1 Λ Λ' π Γ p) :=
  Prod.ext (redZ1_conj π ψ (conj_mem_normal Γ ψ) p.1) (funext fun s => by
    show redA Λ Λ' Gf (regRep Λ π ψ (regRep Λ π (h s) (p.2 (t s)) - (p.1 : Γ → MonoidAlgebra Λ Gf) (h s))) =
      regRep Λ' π ψ (regRep Λ' π (h s) (redA Λ Λ' Gf (p.2 (t s))) -
        redA Λ Λ' Gf ((p.1 : Γ → MonoidAlgebra Λ Gf) (h s)))
    rw [redA_regRep, map_sub, redA_regRep])

theorem red2_frob (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    red2 Λ Λ' π Γ I (frob2 (regRep Λ π) Γ I ψ t h hI e) = frob2 (regRep Λ' π) Γ I ψ t h hI (red2 Λ Λ' π Γ I e) :=
  funext fun s => redZ1_conj π (ψ * h s) (bdry_mem Γ I ψ t h hI s) (e (t s))

end Frob

section Red

variable [Finite Λ] [Fintype Gf] {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ'))
  (ht : algebraMap Λ Λ' ϖ = 0) (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {l N : ℕ}
  (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

include hsurj hΛ hall hπ in
theorem red1_surjective : Function.Surjective (red1 Λ Λ' π Γ (S := S)) := fun p => by
  obtain ⟨c, hc⟩ := redZ1_surjective π hsurj hΛ Γ hall hπ p.1
  choose a ha using fun s => redA_surjective (Gf := Gf) hsurj (p.2 s)
  exact ⟨(c, a), Prod.ext hc (funext ha)⟩

include hk hΛ hall hπ in
theorem red1_ker (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) (hp : red1 Λ Λ' π Γ p = 0) :
    ∃ q, p = ϖ • q := by
  obtain ⟨d, hd⟩ := redZ1_ker π hk hΛ Γ hall hπ p.1 (congrArg Prod.fst hp)
  choose b hb using fun s => redA_ker hk (p.2 s) (congrFun (congrArg Prod.snd hp) s)
  exact ⟨(d, b), Prod.ext hd (funext hb)⟩

include hsurj hΛ hallI hπ in
theorem red2_surjective : Function.Surjective (red2 Λ Λ' π Γ I) := fun e => by
  choose c hc using fun s => redZ1_surjective π hsurj hΛ (Γ ⊓ I s) (hallI s) hπ (e s)
  exact ⟨c, funext hc⟩

include hk hΛ hallI hπ in
theorem red2_ker (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (he : red2 Λ Λ' π Γ I e = 0) : ∃ q, e = ϖ • q := by
  choose d hd using fun s => redZ1_ker π hk hΛ (Γ ⊓ I s) (hallI s) hπ (e s) (congrFun he s)
  exact ⟨d, funext hd⟩

/-- `Λ' ⊗ P⁰_Λ ≃ P⁰_Λ'`. -/
def pcRed0 : Λ' ⊗[Λ] MonoidAlgebra Λ Gf ≃ₗ[Λ'] MonoidAlgebra Λ' Gf :=
  redEquiv ϖ hsurj ht (redA Λ Λ' Gf) (redA_surjective hsurj) (redA_ker hk)

/-- `Λ' ⊗ P¹_Λ ≃ P¹_Λ'`. -/
def pcRed1 : Λ' ⊗[Λ] (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) ≃ₗ[Λ'] Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf) :=
  redEquiv ϖ hsurj ht (red1 Λ Λ' π Γ) (red1_surjective π Γ hsurj hΛ hall hπ) (red1_ker π Γ hk hΛ hall hπ)

/-- `Λ' ⊗ P²_Λ ≃ P²_Λ'`. -/
def pcRed2 : Λ' ⊗[Λ] ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ≃ₗ[Λ'] ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) :=
  redEquiv ϖ hsurj ht (red2 Λ Λ' π Γ I) (red2_surjective π Γ I hsurj hΛ hallI hπ) (red2_ker π Γ I hk hΛ hallI hπ)

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

include hsurj ht hk in
/-- Degree 0 of `lefschetz_frob_red`, on the native type `Λ[Gf]`. -/
theorem hs_red0 [Module.Free Λ (MonoidAlgebra Λ Gf)] [Module.Finite Λ (MonoidAlgebra Λ Gf)]
    [Module.Free Λ' (MonoidAlgebra Λ' Gf)] [Module.Finite Λ' (MonoidAlgebra Λ' Gf)] (hρ : IsProj (rRep Λ Gf))
    (c : ConjClasses Gf) :
    hs (rRep Λ' Gf) (regRep Λ' π ψ) c = algebraMap Λ Λ' (hs (rRep Λ Gf) (regRep Λ π ψ) c) :=
  hs_red_of ϖ hsurj ht hρ
    (show IsEquivariant (rRep Λ Gf) (rRep Λ Gf) (regRep Λ π ψ) from
      fun x => LinearMap.ext fun a => (mulRight_regRep π (single x⁻¹ 1) ψ a).symm)
    _ (redA Λ Λ' Gf) (redA_surjective hsurj) (redA_ker hk) (fun x a => redA_rRep x a)
    (fun a => redA_regRep π ψ a) c

include hsurj ht hk hΛ hall hπ in
/-- Degree 1 of `lefschetz_frob_red`, on the native type `E_Γ × A^S`. -/
theorem hs_red1 [Module.Free Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf))]
    [Module.Finite Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf))]
    [Module.Free Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf))]
    [Module.Finite Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf))] (hρ : IsProj (rho1 Λ π Γ S))
    (c : ConjClasses Gf) :
    hs (rho1 Λ' π Γ S) (frob1 (regRep Λ' π) Γ ψ t h) c =
      algebraMap Λ Λ' (hs (rho1 Λ π Γ S) (frob1 (regRep Λ π) Γ ψ t h) c) :=
  hs_red_of ϖ hsurj ht hρ (frob1_equiv (Λ := Λ) (π := π) (Γ := Γ) (ψ := ψ) (t := t) (h := h)) _
    (red1 Λ Λ' π Γ) (red1_surjective π Γ hsurj hΛ hall hπ) (red1_ker π Γ hk hΛ hall hπ) (red1_rho1 π Γ)
    (red1_frob π Γ ψ t h) c

include hsurj ht hk hΛ hallI hπ in
/-- Degree 2 of `lefschetz_frob_red`, on the native type `Π_s E_s`. -/
theorem hs_red2 [Module.Free Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s))]
    [Module.Finite Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s))]
    [Module.Free Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s))]
    [Module.Finite Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s))] (hρ : IsProj (rho2 Λ π Γ I))
    (c : ConjClasses Gf) :
    hs (rho2 Λ' π Γ I) (frob2 (regRep Λ' π) Γ I ψ t h hI) c =
      algebraMap Λ Λ' (hs (rho2 Λ π Γ I) (frob2 (regRep Λ π) Γ I ψ t h hI) c) :=
  hs_red_of ϖ hsurj ht hρ (frob2_equiv (Λ := Λ) (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) hI) _
    (red2 Λ Λ' π Γ I) (red2_surjective π Γ I hsurj hΛ hallI hπ) (red2_ker π Γ I hk hΛ hallI hπ)
    (red2_rho2 π Γ I) (red2_frob π Γ I ψ t h hI) c

include hsurj ht hk hΛ hall hallI hπ in
/-- **Mod `ϖ` compatibility of the Lefschetz numbers of the Frobenius** (`Pₙ ⊗ Λₘ ≅ Pₘ`). -/
theorem lefschetz_frob_red [hF : ∀ i, Module.Free Λ (PC Λ π Γ I i)] [hT : ∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    [hF' : ∀ i, Module.Free Λ' (PC Λ' π Γ I i)] [hT' : ∀ i, Module.Finite Λ' (PC Λ' π Γ I i)]
    (hρ : ∀ i, IsProj (ρPC Λ π Γ I i)) (c : ConjClasses Gf) :
    lefschetz (ρPC Λ' π Γ I) 2 (frobPC Λ' π Γ I ψ t h hI) c =
      algebraMap Λ Λ' (lefschetz (ρPC Λ π Γ I) 2 (frobPC Λ π Γ I ψ t h hI) c) := by
  have key : ∀ i ∈ Finset.range (2 + 1), hs (ρPC Λ' π Γ I i) (frobPC Λ' π Γ I ψ t h hI i) c =
      algebraMap Λ Λ' (hs (ρPC Λ π Γ I i) (frobPC Λ π Γ I ψ t h hI i) c) := by
    intro i hi
    match i, hi with
    | 0, _ =>
      have : Module.Free Λ (MonoidAlgebra Λ Gf) := hF 0
      have : Module.Finite Λ (MonoidAlgebra Λ Gf) := hT 0
      have : Module.Free Λ' (MonoidAlgebra Λ' Gf) := hF' 0
      have : Module.Finite Λ' (MonoidAlgebra Λ' Gf) := hT' 0
      exact hs_red0 π hsurj ht hk ψ (hρ 0) c
    | 1, _ =>
      have : Module.Free Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) := hF 1
      have : Module.Finite Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) := hT 1
      have : Module.Free Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf)) := hF' 1
      have : Module.Finite Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf)) := hT' 1
      exact hs_red1 π Γ hsurj ht hk hΛ hall hπ ψ t h (hρ 1) c
    | 2, _ =>
      have : Module.Free Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) := hF 2
      have : Module.Finite Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) := hT 2
      have : Module.Free Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) := hF' 2
      have : Module.Finite Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) := hT' 2
      exact hs_red2 π Γ I hsurj ht hk hΛ hallI hπ ψ t h hI (hρ 2) c
    | k + 3, hk3 => exact absurd (Finset.mem_range.1 hk3) (by omega)
  simp only [lefschetz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_pow, map_neg,
    map_one]
  exact Finset.sum_congr rfl fun i hi => by rw [key i hi]

end Red

end

end PerfectCx
end RamanujanPetersson

end


