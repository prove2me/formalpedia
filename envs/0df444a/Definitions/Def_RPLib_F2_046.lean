-- Prove2me | Definitions.Def_RPLib_F2_046
-- name    : RPLib_F2_046
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T14:25:14.739495+00:00
-- url     : https://prove2.me/theorems/bf94e01b-115e-4c37-be19-56eda04a90fc
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 046 of 70
-- statement:
--   File 046 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_ZFin1`: S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part
--   * `S4.Def_RP_Lefschetz_PtE`: S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count
--   * `S4.Def_RP_Lefschetz_PtAsm`: S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`
--   * `S4.Def_RP_Lefschetz_PtSum`: S4-Lefschetz, L5c5: the alternating trace of `γ⁻¹ ∘ F^m` is `|Z(γ)|` times a point count
--   * `S4.Def_RP_Lefschetz_PDiv1c`: S4-Lefschetz, L6e (1c): divisibility of base divisors at a finite constant level
--   * `S4.Def_RP_Lefschetz_PDiv2`: S4-Lefschetz, L6e (2): transport of Dedekind models and valuations along field isomorphisms
--   * `S4.Def_RP_Lefschetz_ZFin2`: S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)
--   * `S4.Def_RP_Lefschetz_PDiv3`: S4-Lefschetz, L6e (3): a finite extension `M ⊆ K̄` as a function field over its constant field `k'`
--   * `S4.Def_RP_Lefschetz_PDiv4`: S4-Lefschetz, L6e (4): the divisibility hypothesis `PicDivU` holds
--   * `S4.Def_RP_Lefschetz_PDiv5`: S4-Lefschetz, L6e (5): places over `∞` of `M` and of its constant levels
--   * `S4.Def_RP_Lefschetz_TwistCount`: S4-Lefschetz, L6a: the Lefschetz trace formula mod `l^n` on the cone complex, as a sum over points
--   * `S4.Def_RP_Lefschetz_Pkg`: S4-Lefschetz, L6c: the perfect-complex package of `lefschetz_twist`, discharged
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_028
import Definitions.Def_RPLib_F2_041

/-!
# Ramanujan-Petersson curve library (flat edition), file 046 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_ZFin1`: S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part
* `S4.Def_RP_Lefschetz_PtE`: S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count
* `S4.Def_RP_Lefschetz_PtAsm`: S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`
* `S4.Def_RP_Lefschetz_PtSum`: S4-Lefschetz, L5c5: the alternating trace of `γ⁻¹ ∘ F^m` is `|Z(γ)|` times a point count
* `S4.Def_RP_Lefschetz_PDiv1c`: S4-Lefschetz, L6e (1c): divisibility of base divisors at a finite constant level
* `S4.Def_RP_Lefschetz_PDiv2`: S4-Lefschetz, L6e (2): transport of Dedekind models and valuations along field isomorphisms
* `S4.Def_RP_Lefschetz_ZFin2`: S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)
* `S4.Def_RP_Lefschetz_PDiv3`: S4-Lefschetz, L6e (3): a finite extension `M ⊆ K̄` as a function field over its constant field `k'`
* `S4.Def_RP_Lefschetz_PDiv4`: S4-Lefschetz, L6e (4): the divisibility hypothesis `PicDivU` holds
* `S4.Def_RP_Lefschetz_PDiv5`: S4-Lefschetz, L6e (5): places over `∞` of `M` and of its constant levels
* `S4.Def_RP_Lefschetz_TwistCount`: S4-Lefschetz, L6a: the Lefschetz trace formula mod `l^n` on the cone complex, as a sum over points
* `S4.Def_RP_Lefschetz_Pkg`: S4-Lefschetz, L6c: the perfect-complex package of `lefschetz_twist`, discharged
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_ZFin1 =====
section

/-!
# S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part

* `HomLC D A`: locally constant homomorphisms `D → A`.
* `z1_eq_of_reps`: a cocycle on `Δ` is determined by its values on `Δ ∩ ker π` and on representatives of `π(Δ)`.
* `finite_Z1_regRep`: `Z¹(Δ, Λ[Gf])` is finite once `Hom_lc(Δ ∩ ker π, Λ)` is (`Λ`, `Gf` finite).
* `finite_Z1_inertia`: from a residue hypothesis (`Ldet`), every `Z¹(Γ ⊓ I_s, Λ[Gf])` is finite.
* `finite_Z1_triv`: `Z¹(Γ, Λ)` (trivial action) is finite once `H¹_c(Γ, {I_s}; Λ)` and all `Z¹(Γ ⊓ I_s, Λ)` are.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

section Gen

theorem finite_of_ker_range {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (f : X →+ Y) [Finite Y]
    (hk : Finite f.ker) : Finite X := by
  have : Finite (X ⧸ f.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange f).symm.toEquiv
  exact Finite.of_addSubgroup_quotient f.ker

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G]
  {A : Type} [AddCommGroup A] [Module Λ A] (ρ : Representation Λ G A)

/-- A cocycle on `Δ` is determined by its values on `Δ ∩ ker π` and on representatives of `π(Δ)`. -/
theorem z1_eq_of_reps {Gf : Type} [Group Gf] (π : G →* Gf) (Δ : Subgroup G) (R : Gf → Δ)
    (hR : ∀ g : Δ, π (R (π g) : G) = π g) (c1 c2 : Z1 ρ Δ)
    (hK : ∀ g : Δ, π g = 1 → (c1 : Δ → A) g = (c2 : Δ → A) g)
    (hRc : ∀ y, (c1 : Δ → A) (R y) = (c2 : Δ → A) (R y)) : c1 = c2 := by
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨r, hr⟩ : ∃ r, r = R (π g) := ⟨_, rfl⟩
  have hg : g = r * (r⁻¹ * g) := by group
  have hh : π ((r⁻¹ * g : Δ) : G) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hr, hR g, inv_mul_cancel]
  have e1 := ((mem_Z1 _ _ _).1 c1.2).2 r (r⁻¹ * g)
  have e2 := ((mem_Z1 _ _ _).1 c2.2).2 r (r⁻¹ * g)
  rw [← hg] at e1 e2
  rw [e1, e2, hK _ hh, hr, hRc]

/-- Representatives of `π(Δ)` in `Δ`. -/
theorem exists_reps {Gf : Type} [Group Gf] (π : G →* Gf) (Δ : Subgroup G) :
    ∃ R : Gf → Δ, ∀ g : Δ, π (R (π g) : G) = π g := by
  classical
  refine ⟨fun y => if h : ∃ g : Δ, π g = y then h.choose else 1, fun g => ?_⟩
  have h : ∃ g' : Δ, π g' = π g := ⟨g, rfl⟩
  show π ((if h : ∃ g' : Δ, π g' = π g then h.choose else 1 : Δ) : G) = π g
  rw [dif_pos h]
  exact h.choose_spec

variable [Finite Λ] [IsTopologicalGroup G] {Gf : Type} [Group Gf] [Finite Gf]

/-- `Z¹(Δ, Λ[Gf])` is finite once `Hom_lc(Δ ∩ ker π, Λ)` is. -/
theorem finite_Z1_regRep (π : G →* Gf) (Δ K : Subgroup G) (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1)
    (hfin : Finite (HomLC K Λ)) : Finite (Z1 (regRep Λ π) Δ) := by
  classical
  haveI := hfin
  haveI := finite_A Λ Gf
  obtain ⟨R, hR⟩ := exists_reps π Δ
  let Φ : Z1 (regRep Λ π) Δ → (Gf → HomLC K Λ) × (Gf → MonoidAlgebra Λ Gf) := fun c =>
    (fun y => ⟨fun k => (resK π Δ K hK c k).coeff y,
      (resK_lc π Δ K hK c).comp (fun a : MonoidAlgebra Λ Gf => a.coeff y),
      fun a b => by beta_reduce; rw [resK_add, MonoidAlgebra.coeff_add, Finsupp.add_apply]⟩,
      fun y => (c : Δ → MonoidAlgebra Λ Gf) (R y))
  refine Finite.of_injective Φ fun c1 c2 h => ?_
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine z1_eq_of_reps (regRep Λ π) π Δ R hR c1 c2 (fun g hg => ?_) (fun y => congrFun h2 y)
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun y => ?_)
  exact congrArg (fun f : HomLC K Λ => f.1 ⟨g, (hK g).2 ⟨g.2, hg⟩⟩) (congrFun h1 y)

variable (π : G →* Gf) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S]
  (I : S → Subgroup G) [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]

end Gen

section Triv

variable {Λ : Type} [CommRing Λ] [Finite Λ] {G : Type} [Group G] [TopologicalSpace G]

/-- `Z¹(Γ, Λ)` (trivial action) is finite once `H¹_c(Γ, {I_s}; Λ)` and all `Z¹(Γ ⊓ I_s, Λ)` are. -/
theorem finite_Z1_triv {S : Type} [Finite S] (Γ : Subgroup G) (I : S → Subgroup G)
    (hH : Finite (H1c (Representation.trivial Λ G Λ) Γ I))
    (hI : ∀ s, Finite (Z1 (Representation.trivial Λ G Λ) (Γ ⊓ I s))) :
    Finite (Z1 (Representation.trivial Λ G Λ) Γ) := by
  haveI := hI
  let res : Z1 (Representation.trivial Λ G Λ) Γ →+
      ((s : S) → Z1 (Representation.trivial Λ G Λ) (Γ ⊓ I s)) :=
    { toFun := fun c s => ⟨fun g => (c : Γ → Λ) ⟨(g : G), (Subgroup.mem_inf.1 g.2).1⟩,
        ((mem_Z1 _ _ _).1 c.2).1.comp_continuous (continuous_subtype_val.subtype_mk _),
        fun g h => by
          beta_reduce
          exact ((mem_Z1 _ _ _).1 c.2).2 ⟨(g : G), (Subgroup.mem_inf.1 g.2).1⟩ ⟨(h : G), (Subgroup.mem_inf.1 h.2).1⟩⟩
      map_zero' := funext fun s => Subtype.ext (funext fun g => rfl)
      map_add' := fun _ _ => funext fun s => Subtype.ext (funext fun g => rfl) }
  have hker : ∀ c : Z1 (Representation.trivial Λ G Λ) Γ, c ∈ res.ker →
      ∀ s (g : Γ), (g : G) ∈ I s → (c : Γ → Λ) g = 0 := by
    intro c hc s g hg
    exact congrArg (fun f => ((f s : Z1 (Representation.trivial Λ G Λ) (Γ ⊓ I s)) : ↥(Γ ⊓ I s) → Λ)
      ⟨g, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩) ((AddMonoidHom.mem_ker).1 hc)
  let ψ : res.ker → H1c (Representation.trivial Λ G Λ) Γ I := fun c =>
    Submodule.Quotient.mk ⟨(((c : Z1 (Representation.trivial Λ G Λ) Γ) : Γ → Λ), (0 : S → Λ)),
      (mem_Z1c _ _ _ _).2 ⟨(c : Z1 (Representation.trivial Λ G Λ) Γ).2, fun s g hg => by
        first
          | (dsimp only; rw [hker _ c.2 s g hg]; simp)
          | simp [hker _ c.2 s g hg]⟩⟩
  have hψ : Function.Injective ψ := by
    intro c1 c2 h
    have h' := (Submodule.Quotient.eq _).1 h
    obtain ⟨-, m, hm, -⟩ := (mem_B1c _ _ _ _).1 (Submodule.mem_comap.1 h')
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have := hm g
    simp only [Submodule.coe_subtype, Submodule.coe_sub, Prod.fst_sub, Pi.sub_apply,
      Representation.trivial_apply, sub_self, sub_eq_zero] at this
    exact this
  have : Finite res.ker := Finite.of_injective ψ hψ
  exact finite_of_ker_range res inferInstance

end Triv

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtE =====
section

/-!
# S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count

* `mem_range_thetaE_iff_fix`: `range thetaE` = the automorphisms of `K_U` fixing `E` pointwise;
* `resPt_mem_fix_iff`: `resPt x ∈ Gal(L/E) ↔ x` fixes `E`;
* `rfixE`: the `Gal(L/E)`-invariants of the integral closure of `R_fin` in `L`; `rfixEquiv : R_E ≃+* rfixE`;
* `kcInc`, `toStar`, `kappaE`: the constants of `E` in `K_U`, in `kStar`, in `rfixE`;
* `frob_apply_kStar`: a normalized Frobenius acts on `kStar` as `x ↦ x^Q`;
* `hGH_ptE`, `hcond_ptE`, `hRpG_ptE`, `hRpD_ptE`: the hypotheses of `card_fixed_blk_lift`;
* `card_pt_blk`: the `k_E`-points of `R_E` over a point `u` of `U` = `#{p ∈ π(Γ) | (p a)⁻¹ π(F_u) (p a) = γ}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section PtE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

variable {K}

section RFix

variable {E L : IntermediateField K (AlgebraicClosure K)} (hEL : E ≤ L)

end RFix

section Hyp

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)
variable {E L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E] [Algebra.IsSeparable K E]

variable (hEL : E ≤ L) [FiniteDimensional K L] [IsGalois K L]

variable (hE : E ≤ maxUnram Fq[X] K) (hLU : L ≤ maxUnram (Rfin Fq K) K)
variable {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
variable {φ c0 : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
  (hc0 : c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) {m : ℕ} (hm : 0 < m)
  [NeZero ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1)] {ζ : maxUnram (Rfin Fq K) K}
  (hζ : IsPrimitiveRoot ζ ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1))
  (hblk : ∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ)

include hφ hc0 hm hblk in
/-- `hRpD`: an automorphism of `L` satisfying the normalization is `resPt y * h` with `y` geometric and
`h ∈ Gal(L/E)`. -/
theorem hRpD_ptE {n : ℕ} (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (hmn : m ∣ n)
    (hQ : 1 < p ^ (e * n)) {Ω : Type} [Field Ω] (ιS : kStar (Rfin Fq K) K hq n →+* Ω)
    (w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω) (hwι : ∀ x, w (incStar (Rfin Fq K) K hq n hQ x) = ιS x)
    (x : L ≃ₐ[K] L) (hx : ∀ c, ptResE Fq hEL Ω (w.comp (jPt (Rfin Fq K) K hLU)) x (kappaE Fq hEL c) =
      ιS (toStar Fq hq (hEL.trans hLU) hcard hmn c)) :
    ∃ y ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), ∃ h ∈ galLE hEL, x = resPt (Rfin Fq K) K hLU y * h := by
  obtain ⟨x', rfl⟩ := resPt_surjective (Rfin Fq K) K hLU x
  have hEU : E ≤ maxUnram (Rfin Fq K) K := hEL.trans hLU
  have hfix : ∀ c : Kc Fq E, x' (kcInc Fq hEU c) = kcInc Fq hEU c := by
    intro c
    have hmem : x' (kcInc Fq hEU c) ∈ kStar (Rfin Fq K) K hq n := by
      rw [mem_kStar, ← map_pow]
      exact congrArg x' ((mem_kStar _ _ hq n _).1 (toStar Fq hq hEU hcard hmn c).2)
    have h1 : x' • incStar (Rfin Fq K) K hq n hQ (toStar Fq hq hEU hcard hmn c) =
        incStar (Rfin Fq K) K hq n hQ ⟨x' (kcInc Fq hEU c), hmem⟩ := Subtype.ext rfl
    have h2 : w (jPt (Rfin Fq K) K hLU (resPt (Rfin Fq K) K hLU x' •
        algebraMap (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) (kappaE Fq hEL c))) =
          ιS (toStar Fq hq hEU hcard hmn c) := hx c
    have h3 := jPt_smul (Rfin Fq K) K hLU x'
      (algebraMap (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) (kappaE Fq hEL c))
    have h4 : w (x' • jPt (Rfin Fq K) K hLU
        (algebraMap (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) (kappaE Fq hEL c))) =
          ιS (toStar Fq hq hEU hcard hmn c) := (congrArg w h3).symm.trans h2
    rw [jPt_kappaE Fq hq hEL hLU hcard hmn hQ c, h1, hwι] at h4
    exact congrArg Subtype.val (ιS.injective h4)
  have hq2 : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  obtain ⟨j, z0, hz0, nn, hnn, hdec⟩ := CupDuality.exists_frobPow_mul hφ _ (isOpen_fixRestrict hLU) x'
  have hnnF := (mem_fixRestrict_iff hLU nn).1 hnn
  have hcL : ∀ c : Kc Fq E, ((kcInc Fq hEU c : maxUnram (Rfin Fq K) K) : AlgebraicClosure K) ∈ L :=
    fun c => hEL (c : E).2
  have hpowj : ∀ c : Kc Fq E, kcInc Fq hEU c ^ (Fintype.card Fq ^ j) = kcInc Fq hEU c := by
    intro c
    have hcst := isConst_kcInc Fq hEU hm hcard c
    have h1 := hfix c
    rw [hdec, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hnnF _ (hcL c), (mem_pi1geo _ _ _ z0).1 hz0 _ hcst,
      frob_pow_apply hφ hcst j] at h1
    exact h1
  obtain ⟨g0, hg0⟩ := IsCyclic.exists_generator (α := (Kc Fq E)ˣ)
  have hord : orderOf g0 = Fintype.card Fq ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg0, Nat.card_units, Nat.card_eq_fintype_card, hcard]
  have hprim : IsPrimitiveRoot (kcInc Fq hEU (g0 : Kc Fq E)) (Fintype.card Fq ^ m - 1) := by
    have h1 := IsPrimitiveRoot.orderOf g0
    rw [hord] at h1
    exact (IsPrimitiveRoot.coe_units_iff.2 h1).map_of_injective (kcInc Fq hEU).injective
  obtain ⟨t, rfl⟩ : m ∣ j := dvd_of_pow_fix hq2 hm hprim (hpowj _)
  have hg : ∀ v : maxUnram (Rfin Fq K) K, IsConst (Fintype.card Fq) v →
      (c0⁻¹ * φ⁻¹ ^ m)⁻¹ v = v ^ (Fintype.card Fq ^ m) := fun v hv => ginv_apply hφ hc0 m v hv
  refine ⟨φ ^ (m * t) * z0 * ((c0⁻¹ * φ⁻¹ ^ m)⁻¹ ^ t)⁻¹, ?_,
    resPt (Rfin Fq K) K hLU ((c0⁻¹ * φ⁻¹ ^ m)⁻¹ ^ t * nn), ?_, ?_⟩
  · rw [mem_pi1geo]
    intro v hv
    have hv' : IsConst (Fintype.card Fq) (((c0⁻¹ * φ⁻¹ ^ m)⁻¹ ^ t)⁻¹ v) := hv.map _
    have hback : ((c0⁻¹ * φ⁻¹ ^ m)⁻¹ ^ t) (((c0⁻¹ * φ⁻¹ ^ m)⁻¹ ^ t)⁻¹ v) = v := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, (mem_pi1geo _ _ _ z0).1 hz0 _ hv', frob_pow_apply hφ hv' (m * t),
      pow_mul, ← ginv_pow_apply (c0⁻¹ * φ⁻¹ ^ m) _ hg hv' t]
    exact hback
  · rw [resPt_mem_fix_iff Fq hEL hLU,
      ← mem_range_thetaE_iff_fix Fq K E hE ((c0⁻¹ * φ⁻¹ ^ m)⁻¹ ^ t * nn)]
    have hgr : c0⁻¹ * φ⁻¹ ^ m ∈ (thetaE Fq K E hE).range := (hblk _).2 (g_mem_blkH π _ ζ hζ)
    have hnr : nn ∈ (thetaE Fq K E hE).range :=
      (mem_range_thetaE_iff_fix Fq K E hE nn).2 fun v hv => hnnF v (hEL hv)
    exact mul_mem (pow_mem (inv_mem hgr) t) hnr
  · rw [← map_mul, hdec]
    congr 1
    group

end Hyp

end PtE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtAsm =====
section

/-!
# S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`

* `pow_pow_fix`, `coe_algebraMap_kc`, `toStar_algebraMap_ptA`, `algebraMap_rfixE_fq`: compatibilities;
* `rfixHomEquiv`, `card_fixed_rfin_eq`: `k_E`-points of `R_E` = normalized `Fr`-fixed points of `rfixE`;
* `card_rfin_eq_sum`: `#R_E(k_E) = Σ_{u ∈ S} #{p ∈ π(Γ) | (p a)⁻¹ π(F_u) (p a) = γ}` for the `F_{q^m}`-points `S` of `U`
  (normalized by `ιS` on `𝔽_q`) and normalized Frobenius elements `F_u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section PtAsm

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {K : Type} [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)
variable {E L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E] [Algebra.IsSeparable K E]

variable (hEL : E ≤ L) [FiniteDimensional K L] [IsGalois K L]

variable (Ω : Type) [Field Ω]

/-- Precomposition with `rfixEquiv⁻¹`. -/
def rfixHomEquiv : (Rfin (Kc Fq E) E →+* Ω) ≃ (rfixE Fq hEL →+* Ω) where
  toFun v := v.comp (rfixEquiv Fq hEL).symm.toRingHom
  invFun v' := v'.comp (rfixEquiv Fq hEL).toRingHom
  left_inv v := RingHom.ext fun r => by
    show v ((rfixEquiv Fq hEL).symm ((rfixEquiv Fq hEL) r)) = v r
    rw [RingEquiv.symm_apply_apply]
  right_inv v' := RingHom.ext fun r => by
    show v' ((rfixEquiv Fq hEL) ((rfixEquiv Fq hEL).symm r)) = v' r
    rw [RingEquiv.apply_symm_apply]

theorem rfixHomEquiv_kappaE (v : Rfin (Kc Fq E) E →+* Ω) (c : Kc Fq E) :
    rfixHomEquiv Fq hEL Ω v (kappaE Fq hEL c) = v (algebraMap (Kc Fq E) (Rfin (Kc Fq E) E) c) := by
  show v ((rfixEquiv Fq hEL).symm ((rfixEquiv Fq hEL) (algebraMap (Kc Fq E) (Rfin (Kc Fq E) E) c))) = _
  rw [RingEquiv.symm_apply_apply]

/-- **`k_E`-points of `R_E` as normalized `Fr`-fixed points of `rfixE`.** -/
theorem card_fixed_rfin_eq {m : ℕ} (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (Fr : Ω →+* Ω)
    (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m)) (ι : Kc Fq E →+* Ω) :
    Nat.card {v : Rfin (Kc Fq E) E →+* Ω // v.comp (algebraMap (Kc Fq E) (Rfin (Kc Fq E) E)) = ι ∧
        ∀ r, v r ^ Fintype.card (Kc Fq E) = v r} =
      Nat.card {v : rfixE Fq hEL →+* Ω // Fr.comp v = v ∧ ∀ c, v (kappaE Fq hEL c) = ι c} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (rfixHomEquiv Fq hEL Ω) fun v => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨RingHom.ext fun r => ?_, fun c => ?_⟩
    · show Fr (v ((rfixEquiv Fq hEL).symm r)) = v ((rfixEquiv Fq hEL).symm r)
      rw [hFr, ← hcard]
      exact h2 _
    · rw [rfixHomEquiv_kappaE]
      exact RingHom.congr_fun h1 c
  · rintro ⟨h1, h2⟩
    refine ⟨RingHom.ext fun c => ?_, fun r => ?_⟩
    · exact (rfixHomEquiv_kappaE Fq hEL Ω v c).symm.trans (h2 c)
    · have h3 : Fr (v ((rfixEquiv Fq hEL).symm ((rfixEquiv Fq hEL) r))) =
          v ((rfixEquiv Fq hEL).symm ((rfixEquiv Fq hEL) r)) := RingHom.congr_fun h1 ((rfixEquiv Fq hEL) r)
      rw [RingEquiv.symm_apply_apply, hFr, ← hcard] at h3
      exact h3

end PtAsm

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {K : Type} [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)

end Main

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtSum =====
section

/-!
# S4-Lefschetz, L5c5: the alternating trace of `γ⁻¹ ∘ F^m` is `|Z(γ)|` times a point count

* `ptCount S f γ`: the number of `u ∈ S` with `f u` conjugate to `γ`;
* group counting: `card_conj_fiber`, `card_conj_fiber_zero`, `sum_card_conj_eq`, `card_coset_conj`,
  `sum_fixed_blk_card`;
* `pi_mem_geo_of_fix`: an element of `π₁` fixing a primitive `(q^N0 - 1)`-th root of unity (`|Gf| ∣ N0`) maps into
  `π(π₁^geo)`;
* `euler_eq_count`: `Σ_i (-1)^i Tr(ρPC γ⁻¹ ∘ frobPC^m | PC^i) = |Z(γ)| · #{u ∈ S | π(F_u) ~ γ}` (the `hcount`
  hypothesis of `lefschetz_pow_eq_count`), `S` the `F_{q^m}`-points of `U` and `F_u` normalized Frobenius elements.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation

section Count

variable {G : Type} [Group G]

theorem card_conj_fiber (X γ : G) (h : IsConj X γ) :
    Nat.card {b : G // b⁻¹ * X * b = γ} = Nat.card {z : G // z⁻¹ * γ * z = γ} := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hX : X = c⁻¹ * γ * c := by
    rw [← hc]
    group
  subst hX
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft c) fun b => ?_)
  show b⁻¹ * (c⁻¹ * γ * c) * b = γ ↔ (c * b)⁻¹ * γ * (c * b) = γ
  rw [show (c * b)⁻¹ * γ * (c * b) = b⁻¹ * (c⁻¹ * γ * c) * b by group]

theorem card_conj_fiber_zero (X γ : G) (h : ¬ IsConj X γ) : Nat.card {b : G // b⁻¹ * X * b = γ} = 0 := by
  haveI : IsEmpty {b : G // b⁻¹ * X * b = γ} := ⟨fun b => h (isConj_iff.2 ⟨b.1⁻¹, by rw [inv_inv]; exact b.2⟩)⟩
  exact Nat.card_of_isEmpty

theorem sum_card_conj_eq [Finite G] {X : Type} (S : Finset X) (f : X → G) (γ : G) :
    ∑ u ∈ S, Nat.card {b : G // b⁻¹ * f u * b = γ} = Nat.card {z : G // z⁻¹ * γ * z = γ} * ptCount S f γ := by
  classical
  unfold ptCount
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine (Finset.sum_filter_of_ne fun u _ h => ?_).symm.trans (Finset.sum_congr rfl fun u hu => ?_)
  · by_contra hc
    exact h (card_conj_fiber_zero (f u) γ hc)
  · exact card_conj_fiber (f u) γ (Finset.mem_filter.1 hu).2

theorem card_coset_conj (P : Subgroup G) (a X γ : G) :
    Nat.card {p : G // p ∈ P ∧ (p * a)⁻¹ * X * (p * a) = γ} =
      Nat.card {b : G // blk P b = blk P a ∧ b⁻¹ * X * b = γ} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight a) fun p => ?_)
  show p ∈ P ∧ (p * a)⁻¹ * X * (p * a) = γ ↔ blk P (p * a) = blk P a ∧ (p * a)⁻¹ * X * (p * a) = γ
  refine and_congr_left' ?_
  rw [blk_eq_iff, show a * (p * a)⁻¹ = p⁻¹ by group, inv_mem_iff]

theorem sum_fixed_blk_card [Finite G] (P : Subgroup G) (u0 γ X : G)
    (hu : u0 ∈ Subgroup.normalizer (P : Set G)) (hX : u0 * X ∈ P) :
    ∑ ω ∈ Finset.univ.filter (fun ω => blkShift P u0 γ hu ω = ω),
        Nat.card {b : G // blk P b = ω ∧ b⁻¹ * X * b = γ} = Nat.card {b : G // b⁻¹ * X * b = γ} := by
  refine (card_eq_sum_fiber (blk P) (fun b => b⁻¹ * X * b = γ) _ fun b hb => ?_).symm
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (blkShift_fixed_iff P u0 γ hu b).2 ?_⟩
  have e : u0 * b * γ * b⁻¹ = u0 * X := by
    rw [← hb]
    group
  rw [e]
  exact hX

end Count

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

/-- An element of `π₁` fixing a primitive `(q^N0 - 1)`-th root of unity with `|Gf| ∣ N0` maps into `π(π₁^geo)`. -/
theorem pi_mem_geo_of_fix {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K))) {N0 : ℕ} (hN0 : 0 < N0) (hdvd : Fintype.card Gf ∣ N0)
    {ζ : maxUnram (Rfin Fq K) K} (hζ : IsPrimitiveRoot ζ (Fintype.card Fq ^ N0 - 1)) (y : Pi1 (Rfin Fq K) K)
    (hy : y ζ = ζ) : π y ∈ (pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π := by
  have hq2 : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hQ1 : 1 ≤ Fintype.card Fq ^ N0 := Nat.one_le_pow _ _ (by omega)
  have hcst : IsConst (Fintype.card Fq) ζ := ⟨N0, hN0, prim_pow_fix hQ1 hζ⟩
  have hint : IsIntegral K ζ := by
    rw [IntermediateField.isIntegral_iff]
    exact Algebra.IsIntegral.isIntegral _
  haveI : FiniteDimensional K (IntermediateField.adjoin K ({ζ} : Set (maxUnram (Rfin Fq K) K))) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hopen := IntermediateField.fixingSubgroup_isOpen
    (IntermediateField.adjoin K ({ζ} : Set (maxUnram (Rfin Fq K) K)))
  obtain ⟨j, z0, hz0, nn, hnn, hdec⟩ := CupDuality.exists_frobPow_mul hφ
    (π.ker ⊓ (IntermediateField.adjoin K ({ζ} : Set (maxUnram (Rfin Fq K) K))).fixingSubgroup)
    (hπ.inter hopen) y
  obtain ⟨hnk, hnf⟩ := Subgroup.mem_inf.1 hnn
  have hnζ : nn ζ = ζ := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hnf
    exact hnf ζ (IntermediateField.mem_adjoin_simple_self K ζ)
  have hj : ζ ^ (Fintype.card Fq ^ j) = ζ := by
    have h := hy
    rw [hdec, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hnζ, (mem_pi1geo _ _ _ z0).1 hz0 _ hcst,
      frob_pow_apply hφ hcst j] at h
    exact h
  obtain ⟨t, rfl⟩ := dvd_of_pow_fix hq2 hN0 hζ hj
  refine Subgroup.mem_map.2 ⟨z0, hz0, ?_⟩
  rw [hdec, map_mul, map_mul, MonoidHom.mem_ker.1 hnk, mul_one, map_pow]
  obtain ⟨s, rfl⟩ := hdvd
  rw [pow_mul, pow_mul, pow_card_eq_one, one_pow, one_pow, one_mul]

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end Main

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv1c =====
section

/-!
# S4-Lefschetz, L6e (1c): divisibility of base divisors at a finite constant level

For a divisor `D` on the base `F` (constant field `Fq`, `hk`) and `l ∤ q`, at some level `(j+1)!`:
* `exists_base_fin_div`: `D ∘ contract = l^n • z + div f` at every finite place of `F_{(j+1)!}`;
* `exists_base_div0`: if `deg D = 0`, `D ∘ contract = l^n • z + div f` at every place.
Here `contract` is the contraction of the constant field extension `F_N / F` (`isConstExt_Fc`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places ZetaSB

section PicBase

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

include hk in
/-- Contraction to the base through an intermediate level. -/
theorem contract_Fc_trans {m N : ℕ} [NeZero m] [NeZero N] [Fact (m ∣ N)] (P : Place (Lc Fq Ω N) (Fc Fq F Ω N)) :
    contract (isConstExt_Fc Fq F Ω hk m) (contractNN Ω hk m N P) = contract (isConstExt_Fc Fq F Ω hk N) P := by
  refine place_ext_ord ?_ fun f => ?_
  · rw [isLeft_contract, isLeft_contract, isLeft_contractNN]
  · rw [ord_contract, ord_contract, ord_contractNN, algebraMap_FF_F]

variable [IsAlgClosed Ω]

end PicBase

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv2 =====
section

/-!
# S4-Lefschetz, L6e (2): transport of Dedekind models and valuations along field isomorphisms

* `subalgEquiv`: a field isomorphism `φ : L1 ≃+* L2` restricts to subalgebras `S1 ⊆ L1`, `S2 ⊆ L2` with
  `x ∈ S1 ↔ φ x ∈ S2`.
* `valuation_comap_equiv`: valuations of Dedekind domains are transported along a ring isomorphism compatible with a
  field isomorphism of the fraction fields.
* `isIntegral_iff_mem_Rinf`: in a constant field extension `F'/F`, `x ∈ F'` is integral over `Rinf(F)` iff it is
  integral over `O_∞(L)` (the analogue of `Kummer.isIntegral_iff_mem_Rfin`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain
open scoped Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section SubalgEquiv

variable {R1 R2 L1 L2 : Type*} [CommRing R1] [CommRing R2] [Field L1] [Field L2] [Algebra R1 L1] [Algebra R2 L2]

/-- A field isomorphism restricted to subalgebras with corresponding members. -/
def subalgEquiv (S1 : Subalgebra R1 L1) (S2 : Subalgebra R2 L2) (φ : L1 ≃+* L2) (h : ∀ x, x ∈ S1 ↔ φ x ∈ S2) :
    S1 ≃+* S2 where
  toFun x := ⟨φ x.1, (h x.1).1 x.2⟩
  invFun y := ⟨φ.symm y.1, (h _).2 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.1)
  map_mul' a b := Subtype.ext (map_mul φ a.1 b.1)
  map_add' a b := Subtype.ext (map_add φ a.1 b.1)

theorem coe_subalgEquiv (S1 : Subalgebra R1 L1) (S2 : Subalgebra R2 L2) (φ : L1 ≃+* L2)
    (h : ∀ x, x ∈ S1 ↔ φ x ∈ S2) (x : S1) : ((subalgEquiv S1 S2 φ h x : S2) : L2) = φ x := rfl

end SubalgEquiv

section ValTransport

variable {B1 B2 L1 L2 : Type*} [CommRing B1] [IsDedekindDomain B1] [CommRing B2] [IsDedekindDomain B2]
  [Field L1] [Field L2] [Algebra B1 L1] [Algebra B2 L2] [IsFractionRing B1 L1] [IsFractionRing B2 L2]

/-- **Transport of valuations** along `e : B1 ≃+* B2` compatible with `φ : L1 ≃+* L2`. -/
theorem valuation_comap_equiv (e : B1 ≃+* B2) (φ : L1 ≃+* L2)
    (he : ∀ b, algebraMap B2 L2 (e b) = φ (algebraMap B1 L1 b)) (w : HeightOneSpectrum B2) (x : L1) :
    (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).valuation L1 x = w.valuation L2 (φ x) := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B1) x
  simp only [map_div₀]
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    Kummer.intValuation_comap, Kummer.intValuation_comap, ← he a, ← he s,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

end ValTransport

section RinfConst

open PicDescent Places

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}

/-- In a constant field extension `F'/F`, the integral closure of `Rinf(F)` in `F'` is `Rinf(F')`. -/
theorem isIntegral_iff_mem_Rinf (h : RR.IsConstExt Fq F L F' c) (x : F') :
    IsIntegral (Rinf Fq F) x ↔ IsIntegral (Oinf L) x := by
  constructor
  · intro hx
    letI := algInf h
    haveI := towerInf h
    refine isIntegral_of_forall_algebraMap (A := Rinf Fq F) (fun a => ?_) hx
    rw [IsScalarTower.algebraMap_apply (Rinf Fq F) (Rinf L F') F']
    exact (algebraMap (Rinf Fq F) (Rinf L F') a).2
  · intro hx
    letI := algInf h
    haveI := towerInf h
    haveI := isIntegral_AA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf
    exact (Algebra.IsIntegral.isIntegral (R := Rinf Fq F) (⟨x, hx⟩ : Rinf L F')).algebraMap

end RinfConst

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ZFin2 =====
section

/-!
# S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)

* `finite_homLC_of_gen`: locally constant homomorphisms `J → ℤ/N` determined by their value at `τ` form a finite set.
* `finite_Z1_triv_of_eq`, `finite_homLC_of_Z1`: `Z¹(Δ, Λ)` (trivial action) and `Hom_lc(Δ, Λ)` are the same set.
* `finite_Z1_geo`: for a curve `U/𝔽_q` with full constant field, `Z¹(π₁^geo, ℤ/l^n)` is finite: `H¹_c` is finite
  (`free_curveH1c`) and each inertia group has a tame generator (`exists_norm_tau_fin` with `π = 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places CurveCoh Kummer GalCover CP4a Residue PerfectCx

section Gen

variable {G : Type} [Group G] [TopologicalSpace G]

/-- Locally constant homomorphisms `J → ℤ/N` that are all multiples of one `θ` (by their value at `τ`) are finitely
many. -/
theorem finite_homLC_of_gen (J : Subgroup G) (N : ℕ) [NeZero N] (τ : J) (θ : J → ZMod N)
    (h : ∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') → ∀ σ, χ σ = χ τ * θ σ) :
    Finite (HomLC J (ZMod N)) := by
  refine Finite.of_injective (fun χ : HomLC J (ZMod N) => χ.1 τ) fun χ1 χ2 hχ => ?_
  refine Subtype.ext (funext fun σ => ?_)
  have hχ' : χ1.1 τ = χ2.1 τ := hχ
  rw [h χ1.1 χ1.2.1 χ1.2.2 σ, h χ2.1 χ2.2.1 χ2.2.2 σ, hχ']

variable {Λ : Type} [CommRing Λ]

/-- `Z¹(Δ, Λ)` (trivial action) is finite when `Hom_lc(J, Λ)` is, for `Δ = J`. -/
theorem finite_Z1_triv_of_eq (Δ J : Subgroup G) (hΔ : Δ = J) (hJ : Finite (HomLC J Λ)) :
    Finite (Z1 (Representation.trivial Λ G Λ) Δ) := by
  subst hΔ
  refine Finite.of_injective (fun c : Z1 (Representation.trivial Λ G Λ) Δ =>
    (⟨(c : Δ → Λ), ((mem_Z1 _ _ _).1 c.2).1, fun a b => by
      have h := ((mem_Z1 _ _ _).1 c.2).2 a b
      rw [Representation.trivial_apply] at h
      exact h⟩ : HomLC Δ Λ)) fun c1 c2 h => ?_
  exact Subtype.ext (congrArg Subtype.val h)

/-- `Hom_lc(Δ, Λ)` is finite when `Z¹(Δ, Λ)` (trivial action) is. -/
theorem finite_homLC_of_Z1 (Δ : Subgroup G) (hZ : Finite (Z1 (Representation.trivial Λ G Λ) Δ)) :
    Finite (HomLC Δ Λ) := by
  refine Finite.of_injective (fun f : HomLC Δ Λ =>
    (⟨f.1, (mem_Z1 _ _ _).2 ⟨f.2.1, fun a b => by
      rw [Representation.trivial_apply]
      exact f.2.2 a b⟩⟩ : Z1 (Representation.trivial Λ G Λ) Δ)) fun f1 f2 h => ?_
  exact Subtype.ext (congrArg Subtype.val h)

end Gen

section Base

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- The trivial quotient `π = 1` is cut out by the base field. -/
theorem one_iff_fix_bot' (g : Pi1 (Rfin Fq F) F) :
    (1 : Pi1 (Rfin Fq F) F →* PUnit.{1}) g = 1 ↔
      g ∈ (IntermediateField.restrict
        (bot_le : (⊥ : IntermediateField F (AlgebraicClosure F)) ≤ maxUnram (Rfin Fq F) F)).fixingSubgroup := by
  refine iff_of_true rfl ((IntermediateField.mem_fixingSubgroup_iff _ g).2 fun x hx => ?_)
  rw [IntermediateField.mem_restrict, IntermediateField.mem_bot] at hx
  obtain ⟨r, hr⟩ := hx
  have hx : x = algebraMap F (maxUnram (Rfin Fq F) F) r := Subtype.ext hr.symm
  rw [hx, AlgEquiv.commutes]

end Base

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv3 =====
section

/-!
# S4-Lefschetz, L6e (3): a finite extension `M ⊆ K̄` as a function field over its constant field `k'`

`Ω = K̄ = AlgebraicClosure K`; `F_n(M) = Fc k' M Ω n`.
* `eBase`: `integralClosure (Rfin Fq K) M ≃+* Rfin k' M` (same elements).
* `restrictScalars_Fc_eq`: `F_n(M) = M ⊔ constLevel K p (e' n)` in `Ω` (`#k' = p ^ e'`); `levEquiv`.
* `eLev`: `Rfin (L_n) (F_n(M)) ≃+* integralClosure (Rfin Fq K) (M ⊔ constLevel K p (e' n))` (same elements).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places Kummer

section Gen

/-- Intermediate fields over different bases with the same members. -/
def ifEquiv {k1 k2 Ω : Type*} [Field k1] [Field k2] [Field Ω] [Algebra k1 Ω] [Algebra k2 Ω]
    (E1 : IntermediateField k1 Ω) (E2 : IntermediateField k2 Ω) (h : ∀ x, x ∈ E1 ↔ x ∈ E2) : E1 ≃+* E2 where
  toFun x := ⟨x.1, (h x.1).1 x.2⟩
  invFun y := ⟨y.1, (h y.1).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem coe_ifEquiv {k1 k2 Ω : Type*} [Field k1] [Field k2] [Field Ω] [Algebra k1 Ω] [Algebra k2 Ω]
    (E1 : IntermediateField k1 Ω) (E2 : IntermediateField k2 Ω) (h : ∀ x, x ∈ E1 ↔ x ∈ E2) (x : E1) :
    ((ifEquiv E1 E2 h x : E2) : Ω) = x := rfl

/-- Integrality over isomorphic rings with the same structure maps. -/
theorem isIntegral_iff_of_equiv {R R' T : Type*} [CommRing R] [CommRing R'] [CommRing T] [Algebra R T]
    [Algebra R' T] (e : R ≃+* R') (he : ∀ r, algebraMap R' T (e r) = algebraMap R T r) (x : T) :
    IsIntegral R x ↔ IsIntegral R' x := by
  have h1 : (algebraMap R' T).comp (e : R →+* R') = algebraMap R T := RingHom.ext he
  have h2 : (algebraMap R T).comp (e.symm : R' →+* R) = algebraMap R' T := RingHom.ext fun r => by
    show algebraMap R T (e.symm r) = _
    rw [← he, RingEquiv.apply_symm_apply]
  constructor
  · rintro ⟨q, hq, hqx⟩
    exact ⟨q.map (e : R →+* R'), hq.map _, by rw [Polynomial.eval₂_map, h1]; exact hqx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨q.map (e.symm : R' →+* R), hq.map _, by rw [Polynomial.eval₂_map, h2]; exact hqx⟩

end Gen

section MSetup

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [Algebra.IsSeparable K M]

theorem mem_intCl_base (x : M) :
    x ∈ integralClosure (Rfin Fq K) M ↔ x ∈ FunctionField.ringOfIntegers (Kc Fq M) M :=
  (isIntegral_iff_tower Fq[X] (Rfin Fq K) K M x).trans (isIntegral_polyKc_iff Fq M x).symm

/-- `B_M = Rfin(k', M)` (same elements of `M`). -/
def eBase : integralClosure (Rfin Fq K) M ≃+* Rfin (Kc Fq M) M :=
  subalgEquiv _ _ (RingEquiv.refl M) (mem_intCl_base Fq K M)

/-- `x ∈ K̄` lying in `M`: integral over `Rfin(k', M)` iff integral over `𝔽_q[X]`. -/
theorem isIntegral_rfinKc_iff (ω : AlgebraicClosure K) :
    IsIntegral (Rfin (Kc Fq M) M) ω ↔ IsIntegral Fq[X] ω := by
  rw [isIntegral_iff_of_equiv (rfinKcEquiv Fq M) (fun r => rfl)]
  haveI : IsScalarTower Fq[X] (Rfin Fq M) (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq fun r =>
    IsScalarTower.algebraMap_apply Fq[X] M (AlgebraicClosure K) r
  exact ⟨fun h => isIntegral_trans _ h, fun h => h.tower_top⟩

variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- **The constant levels of `M`** are `M ⊔ constLevel K p (e' n)` (`#k' = p ^ e'`). -/
theorem restrictScalars_Fc_eq {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') {n : ℕ} (hn : 0 < e' * n) :
    (Fc (Kc Fq M) M (AlgebraicClosure K) n).restrictScalars K = M ⊔ constLevel K p (e' * n) := by
  have hS : ((Lc (Kc Fq M) (AlgebraicClosure K) n : IntermediateField (Kc Fq M) (AlgebraicClosure K)) :
      Set (AlgebraicClosure K)) = ((X : K[X]) ^ (p ^ (e' * n)) - X).rootSet (AlgebraicClosure K) := by
    ext x
    rw [SetLike.mem_coe, mem_Lc, Polynomial.mem_rootSet, hqM, ← pow_mul]
    simp only [map_sub, map_pow, Polynomial.aeval_X, sub_eq_zero]
    constructor
    · intro h
      exact ⟨FiniteField.X_pow_card_sub_X_ne_zero K (one_lt_pow_p (p := p) hn), h⟩
    · intro h
      exact h.2
  rw [Fc, IntermediateField.restrictScalars_adjoin_eq_sup, hS]
  rfl

/-- The level field `F_n(M)` as `M ⊔ constLevel K p (e' n)` (identity on `K̄`). -/
def levEquiv {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) (hn : 0 < e' * n) :
    Fc (Kc Fq M) M (AlgebraicClosure K) n ≃+* (M ⊔ constLevel K p (e' * n) : IntermediateField K (AlgebraicClosure K)) :=
  ifEquiv _ _ fun x => by
    rw [← restrictScalars_Fc_eq Fq K M hqM hn, IntermediateField.mem_restrictScalars]

theorem coe_levEquiv {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) (hn : 0 < e' * n)
    (x : Fc (Kc Fq M) M (AlgebraicClosure K) n) :
    ((levEquiv Fq K M hqM n hn x : (M ⊔ constLevel K p (e' * n) : IntermediateField K (AlgebraicClosure K))) :
      AlgebraicClosure K) = x := coe_ifEquiv _ _ _ x

end MSetup

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv4 =====
section

/-!
# S4-Lefschetz, L6e (4): the divisibility hypothesis `PicDivU` holds

`picDivU`: for `K` a function field over `𝔽_q` with full constant field and `l ∤ q`, `CdOne.PicDivU (Rfin Fq K) K p l`:
every divisor `D` on the finite places of a finite `M ⊆ K_U` becomes `l`-divisible up to `div a` at some constant level
`M ⊔ constLevel K p m`. Proof: view `M` as a function field over its constant field `k'` (`PDiv3`), apply
`exists_base_fin_div` (`Pic⁰(X̄_M)` is `l`-divisible, a degree-one place at infinity absorbs the degree) and transport
places and valuations along `eBase`, `eLev`, `levEquiv`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places Kummer CdOne

section GenA

variable {K : Type} [Field K] (A : Type) [CommRing A] [Algebra A K]

/-- `integralClosure A L` with the generic instance `Algebra A L` (as in `CdOne.PicDivU`). -/
abbrev IC (L : IntermediateField K (AlgebraicClosure K)) : Type := integralClosure A L

theorem isIntegral_IC_iff (L : IntermediateField K (AlgebraicClosure K)) (x : L) :
    IsIntegral A x ↔ IsIntegral A (x : AlgebraicClosure K) := by
  haveI : IsScalarTower A L (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (isIntegral_algebraMap_iff (R := A) (B := AlgebraicClosure K) Subtype.val_injective).symm

theorem isIntegral_tower_Ω (R : Type) [CommRing R] [Algebra R A] [Algebra R K] [IsScalarTower R A K]
    [Algebra.IsIntegral R A] (ω : AlgebraicClosure K) : IsIntegral A ω ↔ IsIntegral R ω :=
  ⟨fun h => isIntegral_trans ω h, fun h => h.tower_top⟩

/-- A Dedekind model of `integralClosure A L` (generic instance), via a field isomorphism onto `L`. -/
def eIC (L : IntermediateField K (AlgebraicClosure K)) {R1 L1 : Type*} [CommRing R1] [Field L1] [Algebra R1 L1]
    (S1 : Subalgebra R1 L1) (φ : L1 ≃+* L) (h : ∀ x, x ∈ S1 ↔ IsIntegral A ((φ x : L) : AlgebraicClosure K)) :
    S1 ≃+* IC A L :=
  subalgEquiv S1 (integralClosure A L) φ fun x => (h x).trans (isIntegral_IC_iff A L (φ x)).symm

theorem coe_eIC (L : IntermediateField K (AlgebraicClosure K)) {R1 L1 : Type*} [CommRing R1] [Field L1]
    [Algebra R1 L1] (S1 : Subalgebra R1 L1) (φ : L1 ≃+* L)
    (h : ∀ x, x ∈ S1 ↔ IsIntegral A ((φ x : L) : AlgebraicClosure K)) (x : S1) :
    ((eIC A L S1 φ h x : IC A L) : L) = φ x := rfl

theorem coe_eIC_symm (L : IntermediateField K (AlgebraicClosure K)) {R1 L1 : Type*} [CommRing R1] [Field L1]
    [Algebra R1 L1] (S1 : Subalgebra R1 L1) (φ : L1 ≃+* L)
    (h : ∀ x, x ∈ S1 ↔ IsIntegral A ((φ x : L) : AlgebraicClosure K)) (y : IC A L) :
    (((eIC A L S1 φ h).symm y : S1) : L1) = φ.symm (y : L) := rfl

end GenA

section PicU

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [Algebra.IsSeparable K M]

theorem mem_base_Ω (x : M) :
    x ∈ FunctionField.ringOfIntegers (Kc Fq M) M ↔ IsIntegral (Rfin Fq K) ((RingEquiv.refl M x : M) : AlgebraicClosure K) := by
  refine (isIntegral_polyKc_iff Fq M x).trans (Iff.trans ?_ (isIntegral_tower_Ω (Rfin Fq K) Fq[X] _).symm)
  haveI : IsScalarTower Fq[X] M (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (isIntegral_algebraMap_iff (R := Fq[X]) (B := AlgebraicClosure K) Subtype.val_injective).symm

/-- `B_M ≃ Rfin(k', M)` with the generic instance on `B_M`. -/
def eBaseG : IC (Rfin Fq K) M ≃+* Rfin (Kc Fq M) M :=
  (eIC (Rfin Fq K) M (FunctionField.ringOfIntegers (Kc Fq M) M) (RingEquiv.refl M) (mem_base_Ω Fq K M)).symm

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem mem_lev_Ω {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n)
    (x : Fc (Kc Fq M) M (AlgebraicClosure K) n) :
    x ∈ FunctionField.ringOfIntegers (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n) ↔
      IsIntegral (Rfin Fq K) ((levEquiv Fq K M hqM n hn x : ↥(M ⊔ constLevel K p (e' * n))) : AlgebraicClosure K) := by
  show IsIntegral _ x ↔ _
  refine (isIntegral_iff_mem_Rfin (isConstExt_Fc (Kc Fq M) M (AlgebraicClosure K) (constField_eq_bot Fq M) n)
    x).symm.trans (Iff.trans ?_ (isIntegral_tower_Ω (Rfin Fq K) Fq[X] _).symm)
  haveI : IsScalarTower (Rfin (Kc Fq M) M) (Fc (Kc Fq M) M (AlgebraicClosure K) n) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← isIntegral_algebraMap_iff (R := Rfin (Kc Fq M) M) (B := AlgebraicClosure K) Subtype.val_injective,
    IntermediateField.algebraMap_apply, coe_levEquiv]
  exact isIntegral_rfinKc_iff Fq K M _

/-- `Rfin(L_n, F_n(M)) ≃ B_{M ⊔ constLevel}` with the generic instance. -/
def eLevG {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n) :
    Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n) ≃+*
      IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n)) :=
  eIC (Rfin Fq K) _ _ (levEquiv Fq K M hqM n hn) (mem_lev_Ω Fq K M hqM n hn)

theorem coe_eBaseG (x : IC (Rfin Fq K) M) : ((eBaseG Fq K M x : Rfin (Kc Fq M) M) : M) = (x : M) :=
  coe_eIC_symm (Rfin Fq K) M _ (RingEquiv.refl M) (mem_base_Ω Fq K M) x

theorem coe_eLevG {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n)
    (r : Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n)) :
    (((eLevG Fq K M hqM n hn r : IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n))) : ↥(M ⊔ constLevel K p (e' * n))) :
      AlgebraicClosure K) = ((r : Fc (Kc Fq M) M (AlgebraicClosure K) n) : AlgebraicClosure K) :=
  (congrArg Subtype.val (coe_eIC (Rfin Fq K) _ _ (levEquiv Fq K M hqM n hn) (mem_lev_Ω Fq K M hqM n hn) r)).trans
    (coe_levEquiv Fq K M hqM n hn _)

theorem algebraMap_eLevG {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n)
    (r : Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n)) :
    algebraMap (IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n))) ↥(M ⊔ constLevel K p (e' * n))
      (eLevG Fq K M hqM n hn r) = levEquiv Fq K M hqM n hn
        (algebraMap (Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n))
          (Fc (Kc Fq M) M (AlgebraicClosure K) n) r) :=
  coe_eIC (Rfin Fq K) _ _ (levEquiv Fq K M hqM n hn) (mem_lev_Ω Fq K M hqM n hn) r

set_option maxHeartbeats 800000 in
/-- **The base place under a level place**: `underI` matches the contraction `F_n(M) / M`. -/
theorem underI_eq_contFin {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n]
    (hn : 0 < e' * n) [IsDedekindDomain (IC (Rfin Fq K) M)]
    [IsDedekindDomain (IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n)))]
    (w : HeightOneSpectrum (IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n)))) :
    underI (Rfin Fq K) (le_sup_left : M ≤ M ⊔ constLevel K p (e' * n)) w =
      HeightOneSpectrum.comap (eBaseG Fq K M : IC (Rfin Fq K) M →+* Rfin (Kc Fq M) M) (eBaseG Fq K M).surjective
        (contFin (isConstExt_Fc (Kc Fq M) M (AlgebraicClosure K) (constField_eq_bot Fq M) n)
          (HeightOneSpectrum.comap (eLevG Fq K M hqM n hn : Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n)
            (Fc (Kc Fq M) M (AlgebraicClosure K) n) →+* IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n)))
            (eLevG Fq K M hqM n hn).surjective w)) := by
  letI := algFin (isConstExt_Fc (Kc Fq M) M (AlgebraicClosure K) (constField_eq_bot Fq M) n)
  apply HeightOneSpectrum.ext
  ext x
  have hx : RamanujanPetersson.incl (Rfin Fq K) K (le_sup_left : M ≤ M ⊔ constLevel K p (e' * n)) x =
      eLevG Fq K M hqM n hn (algebraMap (Rfin (Kc Fq M) M) (Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n)
        (Fc (Kc Fq M) M (AlgebraicClosure K) n)) (eBaseG Fq K M x)) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [RamanujanPetersson.incl_val, coe_eLevG, JacFrob.coe_algFin, coe_eBaseG]
    rfl
  show RamanujanPetersson.incl (Rfin Fq K) K _ x ∈ w.asIdeal ↔ eLevG Fq K M hqM n hn (algebraMap (Rfin (Kc Fq M) M)
    (Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n)) (eBaseG Fq K M x)) ∈ w.asIdeal
  rw [hx]

end PicU

section PicU2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

end PicU2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv5 =====
section

/-!
# S4-Lefschetz, L6e (5): places over `∞` of `M` and of its constant levels

The `Rinf` side of `PDiv4` (generic-instance `IC`): `eBaseInfG : IC (Rinf Fq K) M ≃+* Rinf k' M`,
`eLevInfG : Rinf (L_n) (F_n(M)) ≃+* IC (Rinf Fq K) (M ⊔ constLevel)`, `underI_eq_contInf`; and the two transport
steps of `picDivX`: `dvd_fin_of` (finite places) and `dvd_inf_of` (places over `∞`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places Kummer CdOne

section PicX

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [Algebra.IsSeparable K M]

/-- `x ∈ K̄`: integral over `Rinf(k', M)` iff integral over `O_∞`. -/
theorem isIntegral_rinfKc_Ω_iff (ω : AlgebraicClosure K) :
    IsIntegral (Rinf (Kc Fq M) M) ω ↔ IsIntegral (Oinf Fq) ω := by
  rw [isIntegral_iff_of_equiv (rinfKcEquiv Fq M) (fun r => rfl)]
  haveI : IsScalarTower (Oinf Fq) (Rinf Fq M) (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq fun r =>
    IsScalarTower.algebraMap_apply (Oinf Fq) M (AlgebraicClosure K) r
  exact ⟨fun h => isIntegral_trans _ h, fun h => h.tower_top⟩

variable {p : ℕ} [Fact p.Prime] [CharP K p]

end PicX

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_TwistCount =====
section

/-!
# S4-Lefschetz, L6a: the Lefschetz trace formula mod `l^n` on the cone complex, as a sum over points

* `ptCount_eq_card`, `sum_class_ptCount`: `Σ_c L(c) χ(c) = Σ_{u ∈ S} χ([g u])` when `L([γ]) = #{u ∈ S | g u ~ γ}`;
* **`lefschetz_twist`**: for a lisse `τ : Gf → GL(M)` over `ℤ/l^n` (through `π : π₁(U) → Gf`),
  `Tr(F^m | M) - Tr(F^m | K¹(M)) + Tr(F^m | K²(M)) = Σ_{u ∈ U(F_{q^m})} Tr(τ(π F_u)⁻¹ | M)`, with `F` the geometric
  Frobenius `φ⁻¹` on the cone complex `K(M)` and `F_u` (arithmetic) Frobenius elements at the `F_{q^m}`-points `u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings

section Gen

theorem ptCount_eq_card {X G : Type} [Group G] [DecidableEq (ConjClasses G)] (S : Finset X) (g : X → G) (γ : G) :
    ptCount S g γ = (S.filter fun u => ConjClasses.mk (g u) = ConjClasses.mk γ).card := by
  unfold ptCount
  congr 1
  ext u
  simp only [Finset.mem_filter, ConjClasses.mk_eq_mk_iff_isConj]

/-- **Class sums to point sums.** -/
theorem sum_class_ptCount {Λ : Type} [CommRing Λ] {G : Type} [Group G] [Fintype (ConjClasses G)] {X : Type}
    (S : Finset X) (g : X → G) (L : ConjClasses G → Λ) (hL : ∀ γ, L (ConjClasses.mk γ) = (ptCount S g γ : Λ))
    (χ : ConjClasses G → Λ) :
    ∑ c, L c * χ c = ∑ u ∈ S, χ (ConjClasses.mk (g u)) := by
  classical
  calc ∑ c, L c * χ c = ∑ c, ∑ u ∈ S.filter (fun u => ConjClasses.mk (g u) = c), χ c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        obtain ⟨γ, rfl⟩ := ConjClasses.mk_surjective c
        rw [hL, ptCount_eq_card, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ u ∈ S, χ (ConjClasses.mk (g u)) := Finset.sum_fiberwise' S (fun u => ConjClasses.mk (g u)) χ

end Gen

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end Main

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Pkg =====
section

/-!
# S4-Lefschetz, L6c: the perfect-complex package of `lefschetz_twist`, discharged

* `zmod_maximalIdeal_eq`, `zmod_l_pow_eq_zero`, `zmod_l_pow_ne_zero`, `charP_residue_zmod`: `ℤ/l^N` is a local ring
  with maximal ideal `(l)`, `l` of nilpotency index exactly `N`, residue characteristic `l`.
* **`lefschetz_pkg`**: `lefschetz_twist` with the residue hypothesis and its Frobenius twist (`exists_resHyp_tw`),
  `H²`-vanishing (`h2All_geo`, `cone_h3_eq_zero`), projectivity (a Sylow subgroup) and freeness/finiteness of the
  complex (`pc_free_finite`) all discharged. Remaining hypotheses: `PicDivU` (level `l`), `PicDivX` (level
  `l^(n+k)`), `π` cut out by a finite unramified `M`, and finiteness of `Z¹(Γ, Λ[Gf])` (`Γ = π₁^geo`, `π₁^geo ⊓ I_s`)
  at the two levels (L6z).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue

section ZModPow

variable (l N : ℕ) [Fact l.Prime]

/-- The maximal ideal of `ℤ/l^N` is `(l)`. -/
theorem zmod_maximalIdeal_eq (hN : 0 < N) [IsLocalRing (ZMod (l ^ N))] :
    IsLocalRing.maximalIdeal (ZMod (l ^ N)) = Ideal.span {(l : ZMod (l ^ N))} := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ N) := ⟨pow_ne_zero _ hl.ne_zero⟩
  refine le_antisymm (fun x hx => ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_))
  · have hx' : ¬ IsUnit ((x.val : ℕ) : ZMod (l ^ N)) := by
      rw [ZMod.natCast_zmod_val]
      exact (IsLocalRing.mem_maximalIdeal x).1 hx
    rw [ZMod.isUnit_natCast_iff_not_dvd_pow hl hN, not_not] at hx'
    obtain ⟨c, hc⟩ := hx'
    exact Ideal.mem_span_singleton.2 ⟨(c : ZMod (l ^ N)), by rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_mul]⟩
  · exact (IsLocalRing.mem_maximalIdeal _).2 (ZMod.prime_natCast_not_isUnit_pow hl hN)

theorem zmod_l_pow_eq_zero : (l : ZMod (l ^ N)) ^ N = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

theorem zmod_l_pow_ne_zero {m : ℕ} (hm : m < N) : (l : ZMod (l ^ N)) ^ m ≠ 0 := by
  rw [← Nat.cast_pow, Ne, ZMod.natCast_eq_zero_iff, Nat.pow_dvd_pow_iff_le_right (Fact.out : l.Prime).one_lt]
  omega

/-- The residue field of `ℤ/l^N` has characteristic `l`. -/
theorem charP_residue_zmod (hN : 0 < N) [IsLocalRing (ZMod (l ^ N))] :
    CharP (IsLocalRing.ResidueField (ZMod (l ^ N))) l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (IsLocalRing.residue (ZMod (l ^ N))) l,
    IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 (ZMod.prime_natCast_not_isUnit_pow (Fact.out : l.Prime) hN)

end ZModPow

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end Main

end

end Lefschetz
end RamanujanPetersson


end


