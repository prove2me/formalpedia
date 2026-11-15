-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobK4
-- name    : RPLib_S4_SwanGlobK4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:51:15.728747+00:00
-- url     : https://prove2.me/theorems/a5d08cfb-3b95-4765-b9ba-05e635e52af1
-- title:
--   Katz's (K4) at infinity for an Artin-Schreier cover
-- statement:
--   Let $C$ be a Galois cover with Artin-Schreier generator data: $y^q = y - f$, $f \ne 0$, $\deg f = N \ge 1$, $p \nmid N$, and only $1$ fixes $y$. For a character $\chi$ of $G$ that is nontrivial and a representation $\rho$ with $\mathrm{Sw}_\infty(\rho) < N$ (all breaks $< N$), the file proves $$\mathrm{Sw}_\infty(\rho \otimes \chi) = N \dim \rho, \qquad (\rho \otimes \chi)^{I_\infty} = 0,$$ i.e. the twist has all breaks $N$ (Katz's (K4)).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1 (property (K4)); J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter VI

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobAS2

/-!
# S4-Swan (K2), part 24: Katz's K4 at `∞` for an Artin-Schreier cover (cover level)

`IsASGen C Fq L y f N` bundles the Artin-Schreier hypotheses (`y^q = y - f`, `deg f = N ≥ 1`, `p ∤ N`, `y`
generates). For a representation `ρ` of the cover group with `Sw_∞(ρ) < N` and a nontrivial character `χ`
(e.g. `L_ψ(f)`): `ρ ⊗ χ` has all breaks `N` (`allBrkInf_twist_as`), `Sw_∞(ρ ⊗ χ) = N · dim V`
(`swanInf_twist_as`), and no invariants under the (wild) inertia (`fixd_twist_as`); a nontrivial character has
`Sw_∞ = N` (`swanInf_char_as`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open IsDedekindDomain Module

namespace RamanujanPetersson

namespace Swan

theorem twist_comp {G Q k V : Type*} [Group G] [Group Q] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k Q V) (χ : Q →* kˣ) (π : G →* Q) :
    (twist ρ χ).comp π = twist (ρ.comp π) (χ.comp π) := rfl

/-- A nontrivial character has `codim V^G = 1`. -/
theorem cod_char {G k : Type*} [Group G] [Field k] (χ : G →* kˣ) (hχ : ∃ σ, χ σ ≠ 1) :
    cod (twist (Representation.trivial k G k) χ) ⊤ = 1 := by
  have h : fixd (twist (Representation.trivial k G k) χ) ⊤ = ⊥ := by
    obtain ⟨σ, hσ⟩ := hχ
    rw [eq_bot_iff]
    intro v hv
    have h1 := (mem_fixd _).1 hv σ (Subgroup.mem_top σ)
    rw [twist_apply, LinearMap.smul_apply, Representation.trivial_apply] at h1
    have h2 : (((χ σ : kˣ) : k) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h3)) hσ
    · rw [h3]; exact Submodule.zero_mem _
  rw [cod, h, finrank_bot, Module.finrank_self]

end Swan

namespace GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

/-- Artin-Schreier generator data for a cover: `y^q = y - f`, `deg f = N ≥ 1`, `p ∤ N`, only `1` fixes `y`. -/
structure IsASGen {A : Type} [CommRing A] [IsDomain A] (C : GalCover A) (Fq : Type) [Field Fq] [Fintype Fq]
    (L : Type) [Field L] [Algebra (RatFunc Fq) L] [MulSemiringAction C.G L] (y : L) (f : RatFunc Fq) (N : ℕ) :
    Prop where
  eq : y ^ Fintype.card Fq = y - algebraMap (RatFunc Fq) L f
  ne_zero : f ≠ 0
  deg : f.intDegree = N
  one_le : 1 ≤ N
  coprime : Nat.Coprime N (Fintype.card Fq)
  gen : ∀ σ : C.G, σ • y = y → σ = 1

section K4

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]
variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq]
variable {C Fq L} {y : L} {f : RatFunc Fq} {N : ℕ}

attribute [local instance] infChartAction infChart_isGaloisGroup

theorem IsASGen.constI (h : C.IsASGen Fq L y f N) (P : HeightOneSpectrum (infChart Fq L)) :
    (C.infRamFn Fq L P).ConstI N :=
  infRamFn_constI_as C Fq L P h.eq h.ne_zero h.deg h.one_le h.coprime h.gen

theorem IsASGen.inertia_eq_top (h : C.IsASGen Fq L y f N) (P : HeightOneSpectrum (infChart Fq L)) :
    C.infInertia Fq L P.asIdeal = ⊤ :=
  infInertia_eq_top_as C Fq L P h.eq h.ne_zero h.deg h.one_le h.coprime h.gen

theorem IsASGen.chiAllBrk (h : C.IsASGen Fq L y f N) {k : Type} [Field k] (χ : C.G →* kˣ)
    (hχ : ∃ σ, χ σ ≠ 1) (P : HeightOneSpectrum (infChart Fq L)) :
    (C.infRamFn Fq L P).ChiAllBrk (χ.comp (C.infInertia Fq L P.asIdeal).subtype) N :=
  chiAllBrk_as C Fq L χ hχ P h.eq h.ne_zero h.deg h.one_le h.coprime h.gen

/-- **Katz K4 (breaks)**: `ρ ⊗ χ` has all breaks `N` at `∞` when `Sw_∞(ρ) < N`. -/
theorem allBrkInf_twist_as (h : C.IsASGen Fq L y f N) {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k C.G V) (χ : C.G →* kˣ) (hχ : ∃ σ, χ σ ≠ 1)
    (P : HeightOneSpectrum (infChart Fq L)) (hρ : C.swanInf Fq L ρ P < N) :
    (C.infRamFn Fq L P).AllBrk ((Swan.twist ρ χ).comp (C.infInertia Fq L P.asIdeal).subtype) N := by
  rw [Swan.twist_comp]
  exact (C.infRamFn Fq L P).allBrk_twist_of_lt _ _ hρ (h.chiAllBrk χ hχ P)

/-- **Katz K4 (Swan)**: `Sw_∞(ρ ⊗ χ) = N · dim V` when `Sw_∞(ρ) < N`. -/
theorem swanInf_twist_as (h : C.IsASGen Fq L y f N) {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k C.G V) (χ : C.G →* kˣ) (hχ : ∃ σ, χ σ ≠ 1)
    (P : HeightOneSpectrum (infChart Fq L)) (hρ : C.swanInf Fq L ρ P < N) :
    C.swanInf Fq L (Swan.twist ρ χ) P = N * finrank k V := by
  have hN : (0 : ℚ) < N := by exact_mod_cast h.one_le
  rw [swanInf, Swan.twist_comp]
  exact (C.infRamFn Fq L P).swan_twist _ _ hN hρ (h.chiAllBrk χ hχ P)

/-- **Katz K4 (totally wild)**: `ρ ⊗ χ` has no invariants under the cover group when `Sw_∞(ρ) < N`. -/
theorem fixd_twist_as (h : C.IsASGen Fq L y f N) {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k C.G V) (χ : C.G →* kˣ) (hχ : ∃ σ, χ σ ≠ 1)
    (P : HeightOneSpectrum (infChart Fq L)) (hρ : C.swanInf Fq L ρ P < N) :
    Swan.fixd (Swan.twist ρ χ) ⊤ = ⊥ := by
  have hN : (0 : ℚ) < N := by exact_mod_cast h.one_le
  have h1 := (C.infRamFn Fq L P).fixd_twist_lower_one _ _ hN hρ (h.chiAllBrk χ hχ P)
  rw [← Swan.twist_comp, Swan.fixd_comp, (h.constI P).lower_of_le h.one_le, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, h.inertia_eq_top P] at h1
  exact h1

/-- **`Sw_∞(L_ψ(f)) = deg f`**: a nontrivial character of an Artin-Schreier cover has Swan conductor `N`. -/
theorem swanInf_char_as (h : C.IsASGen Fq L y f N) {k : Type} [Field k] (χ : C.G →* kˣ) (hχ : ∃ σ, χ σ ≠ 1)
    (P : HeightOneSpectrum (infChart Fq L)) :
    C.swanInf Fq L (Swan.twist (Representation.trivial k C.G k) χ) P = N := by
  rw [swanInf_as C Fq L _ P h.eq h.ne_zero h.deg h.one_le h.coprime h.gen, Swan.cod_char χ hχ]
  simp

end K4

end GalCover

end RamanujanPetersson


