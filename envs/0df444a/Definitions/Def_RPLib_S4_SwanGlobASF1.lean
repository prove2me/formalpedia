-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobASF1
-- name    : RPLib_S4_SwanGlobASF1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:53:22.217301+00:00
-- url     : https://prove2.me/theorems/b922dda1-87a3-4e59-b9e3-49a1d2578d8e
-- title:
--   The Artin-Schreier character of a cover and $\mathrm{Sw}_\infty(\mathcal{L}_\psi(f)) = \deg f$
-- statement:
--   For a Galois cover with Artin-Schreier generator $y$ ($y^q = y - f$, $\deg f = N \ge 1$, $p \nmid N$, only $1$ fixes $y$), every $\sigma \in G$ satisfies $\sigma y = y + a_\sigma$ with a unique $a_\sigma \in \mathbb{F}_q$, and $\sigma \mapsto a_\sigma$ is an isomorphism $G \cong \mathbb{F}_q$. For an additive character $\psi$ the character $\mathcal{L}_\psi(f) : \sigma \mapsto \psi(a_\sigma)$ of $G$ satisfies, when $\psi$ is nontrivial, $$\mathrm{Sw}_\infty(\mathcal{L}_\psi(f)) = N, \qquad \mathrm{Sw}_\infty(\rho \otimes \mathcal{L}_\psi(f)) = N \dim\rho \ \text{ if } \mathrm{Sw}_\infty(\rho) < N.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1 (p. 13); H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.7 (Artin-Schreier extensions)

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobK4

/-!
# S4-Swan (K2), part 25: the Artin-Schreier character of a cover and `Sw_∞(L_ψ(f)) = N` (cover level)

For Artin-Schreier generator data `h : C.IsASGen Fq L y f N` every `σ` of the cover group moves `y` by a
constant: `σ y = y + h.val σ` with `h.val σ ∈ Fq`. The map `h.val` is an injective additive character
(`h.char : C.G →* Multiplicative Fq`), bijective because `|G| = q`. For an additive character `ψ : Fq → k`
the rank-one character `h.lpsi ψ : σ ↦ ψ(σ y - y)` is the cover-level `L_ψ(f)`; for `ψ` nontrivial it has
`Sw_∞ = N` (`swanInf_lpsi`), and Katz's K4 holds for `ρ ⊗ L_ψ(f)` when `Sw_∞(ρ) < N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open IsDedekindDomain Module

namespace RamanujanPetersson

namespace GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

section ASChar

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A}
variable {Fq : Type} [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable {L : Type} [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]
variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq]
variable {y : L} {f : RatFunc Fq} {N : ℕ}

attribute [local instance] infChartAction infChart_isGaloisGroup

/-- The Artin-Schreier value `σ y - y ∈ Fq` of an element of the cover group. -/
def IsASGen.val (h : C.IsASGen Fq L y f N) (σ : C.G) : Fq :=
  (exists_smul_sub (C := C) h.eq σ).choose

theorem IsASGen.val_spec (h : C.IsASGen Fq L y f N) (σ : C.G) :
    σ • y = y + algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) (h.val σ)) :=
  (exists_smul_sub (C := C) h.eq σ).choose_spec

theorem IsASGen.val_mul (h : C.IsASGen Fq L y f N) (σ τ : C.G) :
    h.val (σ * τ) = h.val σ + h.val τ := by
  have h1 := h.val_spec (σ * τ)
  rw [mul_smul, h.val_spec τ, smul_add, smul_algebraMap_K C Fq L σ, h.val_spec σ, add_assoc] at h1
  have h2 : algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) (h.val (σ * τ))) =
      algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) (h.val σ + h.val τ)) := by
    rw [map_add, map_add]
    exact (add_left_cancel h1).symm
  exact ((algebraMap (RatFunc Fq) L).injective.comp (algebraMap Fq (RatFunc Fq)).injective) h2

theorem IsASGen.val_one (h : C.IsASGen Fq L y f N) : h.val 1 = 0 := by
  have h1 := h.val_mul 1 1
  rw [one_mul] at h1
  linear_combination -h1

/-- The Artin-Schreier character `σ ↦ σ y - y` of the cover group. -/
def IsASGen.char (h : C.IsASGen Fq L y f N) : C.G →* Multiplicative Fq where
  toFun σ := Multiplicative.ofAdd (h.val σ)
  map_one' := by rw [h.val_one]; rfl
  map_mul' σ τ := by rw [h.val_mul]; rfl

theorem IsASGen.char_apply (h : C.IsASGen Fq L y f N) (σ : C.G) :
    h.char σ = Multiplicative.ofAdd (h.val σ) := rfl

theorem IsASGen.val_injective (h : C.IsASGen Fq L y f N) : Function.Injective h.val := by
  intro σ τ hστ
  have h1 : σ • y = τ • y := by rw [h.val_spec σ, h.val_spec τ, hστ]
  have h2 : (τ⁻¹ * σ) • y = y := by rw [mul_smul, h1, inv_smul_smul]
  exact (inv_mul_eq_one.1 (h.gen _ h2)).symm

/-- `σ ↦ σ y - y` is a bijection `G ≃ Fq` (the cover has degree `q`). -/
theorem IsASGen.val_bijective (h : C.IsASGen Fq L y f N) (P : HeightOneSpectrum (infChart Fq L)) :
    Function.Bijective h.val := by
  have hc := (as_inertia_val C Fq L P h.eq h.ne_zero h.deg h.one_le h.coprime h.gen).2.1
  have := Fintype.ofFinite C.G
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨h.val_injective, ?_⟩
  rw [← Nat.card_eq_fintype_card]
  exact hc

/-- The cover-level `L_ψ(f)`: the character `σ ↦ ψ(σ y - y)` for an additive character `ψ : Fq → k`. -/
def IsASGen.lpsi (h : C.IsASGen Fq L y f N) {k : Type} [Field k] (ψ : AddChar Fq k) : C.G →* kˣ :=
  (ψ.toMonoidHom.comp h.char).toHomUnits

theorem IsASGen.lpsi_apply (h : C.IsASGen Fq L y f N) {k : Type} [Field k] (ψ : AddChar Fq k) (σ : C.G) :
    ((h.lpsi ψ σ : kˣ) : k) = ψ (h.val σ) := rfl

theorem IsASGen.exists_lpsi_ne_one (h : C.IsASGen Fq L y f N) {k : Type} [Field k] (ψ : AddChar Fq k)
    (hψ : ∃ a, ψ a ≠ 1) (P : HeightOneSpectrum (infChart Fq L)) : ∃ σ, h.lpsi ψ σ ≠ 1 := by
  obtain ⟨a, ha⟩ := hψ
  obtain ⟨σ, hσ⟩ := (h.val_bijective P).2 a
  refine ⟨σ, fun h1 => ha ?_⟩
  have h2 := congrArg Units.val h1
  rw [h.lpsi_apply, hσ, Units.val_one] at h2
  exact h2

/-- **`Sw_∞(L_ψ(f)) = N`** for a nontrivial additive character `ψ` (cover level). -/
theorem IsASGen.swanInf_lpsi (h : C.IsASGen Fq L y f N) {k : Type} [Field k] (ψ : AddChar Fq k)
    (hψ : ∃ a, ψ a ≠ 1) (P : HeightOneSpectrum (infChart Fq L)) :
    C.swanInf Fq L (Swan.twist (Representation.trivial k C.G k) (h.lpsi ψ)) P = N :=
  swanInf_char_as h _ (h.exists_lpsi_ne_one ψ hψ P) P

/-- **Katz K4 (Swan)** for `ρ ⊗ L_ψ(f)`: `Sw_∞ = N · dim V` when `Sw_∞(ρ) < N`. -/
theorem IsASGen.swanInf_twist_lpsi (h : C.IsASGen Fq L y f N) {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k C.G V) (ψ : AddChar Fq k)
    (hψ : ∃ a, ψ a ≠ 1) (P : HeightOneSpectrum (infChart Fq L)) (hρ : C.swanInf Fq L ρ P < N) :
    C.swanInf Fq L (Swan.twist ρ (h.lpsi ψ)) P = N * finrank k V :=
  swanInf_twist_as h ρ _ (h.exists_lpsi_ne_one ψ hψ P) P hρ

/-- **Katz K4 (breaks)** for `ρ ⊗ L_ψ(f)`: all breaks at `∞` equal `N` when `Sw_∞(ρ) < N`. -/
theorem IsASGen.allBrkInf_twist_lpsi (h : C.IsASGen Fq L y f N) {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k C.G V) (ψ : AddChar Fq k)
    (hψ : ∃ a, ψ a ≠ 1) (P : HeightOneSpectrum (infChart Fq L)) (hρ : C.swanInf Fq L ρ P < N) :
    (C.infRamFn Fq L P).AllBrk ((Swan.twist ρ (h.lpsi ψ)).comp (C.infInertia Fq L P.asIdeal).subtype) N :=
  allBrkInf_twist_as h ρ _ (h.exists_lpsi_ne_one ψ hψ P) P hρ

/-- **Katz K4 (totally wild)** for `ρ ⊗ L_ψ(f)`: no invariants when `Sw_∞(ρ) < N`. -/
theorem IsASGen.fixd_twist_lpsi (h : C.IsASGen Fq L y f N) {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k C.G V) (ψ : AddChar Fq k)
    (hψ : ∃ a, ψ a ≠ 1) (P : HeightOneSpectrum (infChart Fq L)) (hρ : C.swanInf Fq L ρ P < N) :
    Swan.fixd (Swan.twist ρ (h.lpsi ψ)) ⊤ = ⊥ :=
  fixd_twist_as h ρ _ (h.exists_lpsi_ne_one ψ hψ P) P hρ

end ASChar

end GalCover

end RamanujanPetersson


