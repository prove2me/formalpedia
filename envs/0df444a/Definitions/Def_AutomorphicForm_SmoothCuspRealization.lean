-- Prove2me | Definitions.Def_AutomorphicForm_SmoothCuspRealization
-- name    : AutomorphicForm_SmoothCuspRealization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d4bc166d-afc7-5d89-aeff-1b34d966cb39
-- title:
--   Smooth cuspidal realizations of Hecke eigensystems
-- statement:
--   Fix a number field $F$ and write $G =$ `AdelicGL2 (𝓞 F) F`. The module first defines, for a tuple $r : \mathrm{Fin}\,n \to G$ of representatives and $\varphi : G \to \mathbb{C}$, the coset sum `SmoothCusp.heckeCosetSum` $= \sum_{i} \varphi(g\,r_i)$, records that it multiplies a constant function by $n$ and is unchanged if each $r_i$ is replaced by $r_i u_i$ with $u_i$ in a subgroup $U$ under which $\varphi$ is right invariant, and then defines `SmoothCusp.IsHeckeCosetEigenfunctionAt U g_v v φ c`: there exist $\mathrm{N}v+1$ elements of $G$ forming an `IsHeckeCosetSystem` for $(U, g_v)$ (the project's notion, from the imported Hecke coset module) whose coset sum satisfies $\sum_i \varphi(g r_i) = c\,\varphi(g)$ for all $g$. The main definition is the structure `SmoothCuspRealizationAt F pins Φ`, for a carrier bundle `pins : CarrierPins F` and a Hecke eigensystem $\Phi$ with complex coefficients: it carries a function $\varphi =$ `toFun`, a point where $\varphi \ne 0$, a character `centralChar` on the subgroup `pins.Z`, a proof that $\varphi$ satisfies the project's predicate `IsSmoothCuspAutomorphicFnAt` for that bundle and character, right invariance of $\varphi$ under `pins.U Φ.level`, a finite exceptional set $S$ of primes, and, for every $v \notin S$, both the coset eigenvalue equation with eigenvalue $\Phi.a\,v$ at the generator `pins.gen v` and the central relation $\varphi(\mathrm{diag}(\det(\mathrm{gen}\,v))\,g) = \Phi.b\,v\,\varphi(g)$. Realizability `IsSmoothCuspRealizable` is nonemptiness of this structure; `smoothCuspNotionOf` packages a field-indexed family of bundles into a `CuspidalityNotion ℂ`; `IsSmoothCuspRealizableVia ι Φ` applies it to $\Phi.\mathrm{map}\,\iota$ for a ring map $\iota : R \to \mathbb{C}$. Derived lemmas: $\varphi$ is left $\mathrm{GL}_2(F)$-invariant and `IsKfSmooth`; the central character is the ratio $\varphi(zg)/\varphi(g)$ at any non-vanishing point and equals $\Phi.b\,v$ when $z = \det(\mathrm{gen}\,v)$; no coset eigenfunction exists at $U = \top$ or $U = \bot$, so the level subgroup of a realization is neither. Finally an inhabitation section exhibits a degenerate bundle with zero measures and $Z = \top$, for which the constant function $1$ is a realization of the degenerate eigensystem $a_v = \mathrm{N}v + 1$, $b_v = 1$, provided coset systems exist; this shows the notion is non-vacuous and imposes no archimedean type or minimal-level condition.
--
--   **Relation to Mathlib.** Mathlib has no notion of adelic automorphic form on $\mathrm{GL}_2$ or of Hecke eigensystem; all notions here are the project's own, built on Mathlib's adele ring, height-one spectrum, absolute ideal norm and measure theory.
--
--   **Where it is used.** This is the complex-analytic side of the correspondence: it supplies the target of the statement that a mod-$\ell$ or $\ell$-adic Hecke eigensystem arising from a Galois representation is cuspidal, used when the eigensystem attached to the Frey curve is matched with an automorphic form. Many downstream modules of the tree take realizability at a bundle, in one of the three consumer forms given here, as their cuspidality hypothesis or conclusion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SmoothCuspRealization.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_HeckeEigensystemMap
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm HeckeIntegralSeam

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

namespace SmoothCusp

def heckeCosetSum {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∑ i, φ (g * reps i)

theorem heckeCosetSum_const {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 F) F) (c : ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    heckeCosetSum F reps (fun _ => c) g = (n : ℂ) * c := by
  simp [heckeCosetSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem heckeCosetSum_mul_right {n : ℕ} {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hinv : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (g * u) = φ g)
    (reps : Fin n → AdelicGL2 (𝓞 F) F) (u : Fin n → AdelicGL2 (𝓞 F) F)
    (hu : ∀ i, u i ∈ U) (g : AdelicGL2 (𝓞 F) F) :
    heckeCosetSum F (fun i => reps i * u i) φ g = heckeCosetSum F reps φ g := by
  unfold heckeCosetSum
  congr 1; ext i
  rw [← mul_assoc]
  exact hinv (g * reps i) (u i) (hu i)

def IsHeckeCosetEigenfunctionAt (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (gv : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) : Prop :=
  ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
    IsHeckeCosetSystem U gv reps ∧
    ∀ g : AdelicGL2 (𝓞 F) F, heckeCosetSum F reps φ g = c * φ g

end SmoothCusp

open SmoothCusp

structure SmoothCuspRealizationAt (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) where
  toFun : AdelicGL2 (𝓞 F) F → ℂ
  exists_ne_zero : ∃ g : AdelicGL2 (𝓞 F) F, toFun g ≠ 0
  centralChar : pins.Z →* ℂˣ
  smoothCusp : IsSmoothCuspAutomorphicFnAt F pins centralChar toFun
  level_invariant : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ pins.U Φ.level, toFun (g * u) = toFun g
  exceptionalSet : Finset (HeightOneSpectrum (𝓞 F))
  hecke_eigen : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ exceptionalSet →
    IsHeckeCosetEigenfunctionAt F (pins.U Φ.level) (pins.gen v) v toFun (Φ.a v)
  central_eigen : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ exceptionalSet →
    ∀ g : AdelicGL2 (𝓞 F) F,
      toFun (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (pins.gen v)) * g)
        = Φ.b v * toFun g

def smoothCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ => Nonempty (@SmoothCuspRealizationAt F _i1 _i2 (pins F) Φ)

def IsSmoothCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  Nonempty (SmoothCuspRealizationAt F pins Φ)

theorem isSmoothCuspRealizable_iff (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsSmoothCuspRealizable F pins Φ ↔ Nonempty (SmoothCuspRealizationAt F pins Φ) := Iff.rfl

theorem smoothCuspNotionOf_isCusp_iff
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) :
    (smoothCuspNotionOf pins).IsCusp F Φ ↔ IsSmoothCuspRealizable F (pins F) Φ := Iff.rfl

def IsSmoothCuspRealizableVia (pins : CarrierPins F) {R : Type*} [CommRing R]
    (ι : R →+* ℂ) (Φ : HeckeEigensystem F R) : Prop :=
  IsSmoothCuspRealizable F pins (Φ.map ι)

theorem isSmoothCuspRealizableVia_id (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsSmoothCuspRealizableVia F pins (RingHom.id ℂ) Φ ↔ IsSmoothCuspRealizable F pins Φ := by
  unfold IsSmoothCuspRealizableVia; rw [HeckeEigensystem.map_id]

variable {F}

theorem SmoothCuspRealizationAt.toFun_ne_zero {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ) :
    R.toFun ≠ fun _ => 0 := by
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  intro h; exact hg (congrFun h g)

theorem SmoothCuspRealizationAt.left_invariant {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ)
    (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (globalPoints (𝓞 F) F γ * g) = R.toFun g := by
  letI := pins.mS
  exact (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).left_invariant γ g

theorem SmoothCuspRealizationAt.isKfSmooth {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ) :
    IsKfSmooth F R.toFun :=
  R.smoothCusp.2

variable (F)

namespace SmoothCusp

theorem not_isHeckeCosetEigenfunctionAt_top (gv : AdelicGL2 (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    ¬ IsHeckeCosetEigenfunctionAt F ⊤ gv v φ c := by
  rintro ⟨reps, hsys, -⟩
  haveI : Subsingleton (AdelicGL2 (𝓞 F) F ⧸ (⊤ : Subgroup (AdelicGL2 (𝓞 F) F))) :=
    QuotientGroup.subsingleton_quotient_top
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : 1 < Ideal.absNorm v.asIdeal + 1 := by omega
  have heq : (0 : Fin (Ideal.absNorm v.asIdeal + 1)) = ⟨1, h1⟩ :=
    hsys.mk_injective (Subsingleton.elim _ _)
  have : (0 : ℕ) = 1 := congrArg Fin.val heq
  omega

theorem not_isHeckeCosetEigenfunctionAt_bot (gv : AdelicGL2 (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    ¬ IsHeckeCosetEigenfunctionAt F ⊥ gv v φ c := by
  rintro ⟨reps, hsys, -⟩
  have hall : ∀ i, reps i = gv := fun i => by
    obtain ⟨u, hu, w, hw, hx⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    rw [Subgroup.mem_bot] at hu hw
    rw [hu, hw, one_mul, mul_one] at hx; exact hx.symm
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : 1 < Ideal.absNorm v.asIdeal + 1 := by omega
  have heq : (0 : Fin (Ideal.absNorm v.asIdeal + 1)) = ⟨1, h1⟩ := by
    apply hsys.mk_injective
    show QuotientGroup.mk (reps 0) = QuotientGroup.mk (reps ⟨1, h1⟩)
    rw [hall 0, hall ⟨1, h1⟩]
  have : (0 : ℕ) = 1 := congrArg Fin.val heq
  omega

end SmoothCusp

variable {F}

theorem SmoothCuspRealizationAt.level_ne_top_ne_bot {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R.exceptionalSet) :
    pins.U Φ.level ≠ ⊤ ∧ pins.U Φ.level ≠ ⊥ :=
  ⟨fun h => not_isHeckeCosetEigenfunctionAt_top F _ v _ _ (h ▸ R.hecke_eigen v hv),
   fun h => not_isHeckeCosetEigenfunctionAt_bot F _ v _ _ (h ▸ R.hecke_eigen v hv)⟩

example (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ := smoothCuspNotionOf pins

theorem SmoothCuspRealizationAt.centralChar_apply_eq {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ)
    (z : pins.Z) {g : AdelicGL2 (𝓞 F) F} (hg : R.toFun g ≠ 0) :
    ((R.centralChar z : ℂˣ) : ℂ) =
      R.toFun (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) / R.toFun g := by
  letI := pins.mS
  have ht := (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform z g
  rw [ht, mul_div_assoc, div_self hg, mul_one]

theorem SmoothCuspRealizationAt.centralChar_det_gen_eq_b {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Φ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R.exceptionalSet) (z : pins.Z)
    (hz : (z : (AdeleRing (𝓞 F) F)ˣ) = Matrix.GeneralLinearGroup.det (pins.gen v)) :
    ((R.centralChar z : ℂˣ) : ℂ) = Φ.b v := by
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  rw [R.centralChar_apply_eq z hg, hz, R.central_eigen v hv g, mul_div_assoc, div_self hg,
    mul_one]

section Inhabitor

variable (F)

def degenerateZeroMeasurePins (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) : CarrierPins F where
  mS := ⊥
  μ := 0
  D := Set.univ
  Z := ⊤
  U := U
  gen := gen
  nS := ⊥
  ν := 0

theorem isSmoothCuspAutomorphicFnAt_one_zeroMeasure
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) :
    IsSmoothCuspAutomorphicFnAt F (degenerateZeroMeasurePins F U gen)
      (1 : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (fun _ => (1 : ℂ)) := by
  refine ⟨⟨isAutomorphicFnAt_one_trivial F _ ?_, ?_⟩, isKfSmooth_const F 1⟩
  · have hμ : (degenerateZeroMeasurePins F U gen).μ
        = (0 : @Measure _ (degenerateZeroMeasurePins F U gen).mS) := rfl
    rw [hμ]; simp only [Measure.coe_zero, Pi.zero_apply]; exact ENNReal.zero_lt_top
  · intro g
    have hν : (degenerateZeroMeasurePins F U gen).ν
        = (0 : @Measure _ (degenerateZeroMeasurePins F U gen).nS) := rfl
    rw [hν]; unfold constantTerm; exact integral_zero_measure _

def degenerateEigensystem (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) : HeckeEigensystem F ℂ where
  level := N
  level_ne_bot := hN
  a := fun v => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1
  b := fun _ => 1

@[simp] theorem degenerateEigensystem_a (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) :
    (degenerateEigensystem F N hN).a v = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1 := rfl

@[simp] theorem degenerateEigensystem_b (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) : (degenerateEigensystem F N hN).b v = 1 := rfl

def smoothCuspRealizationAt_one_of_cosetSystems
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (hsys : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (U N) (gen v) reps) :
    SmoothCuspRealizationAt F (degenerateZeroMeasurePins F U gen)
      (degenerateEigensystem F N hN) where
  toFun := fun _ => 1
  exists_ne_zero := ⟨1, one_ne_zero⟩
  centralChar := 1
  smoothCusp := isSmoothCuspAutomorphicFnAt_one_zeroMeasure F U gen
  level_invariant := fun _ _ _ => rfl
  exceptionalSet := ∅
  hecke_eigen := fun v _ => by
    obtain ⟨reps, hreps⟩ := hsys v
    refine ⟨reps, hreps, fun g => ?_⟩
    rw [heckeCosetSum_const, degenerateEigensystem_a, mul_one, mul_one]
    push_cast
    ring
  central_eigen := fun v _ g => by simp only [degenerateEigensystem_b, one_mul]

end Inhabitor

end AutomorphicForm

end


