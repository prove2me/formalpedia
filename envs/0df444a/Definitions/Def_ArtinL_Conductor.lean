-- Prove2me | Definitions.Def_ArtinL_Conductor
-- name    : ArtinL_Conductor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/9cd6d10c-bd1d-5c53-9a2b-2ad9c9aded8a
-- title:
--   Artin conductor of a complex Galois representation
-- statement:
--   Fix $n$ and write $\Gamma_{\mathbb Q}=\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ for the automorphism group of $\overline{\mathbb Q}=\mathtt{AlgebraicClosure}\ \mathbb Q$ over $\mathbb Q$. For a homomorphism $\rho\colon\Gamma_{\mathbb Q}\to\mathrm{GL}_n(\mathbb C)$, [`ArtinL.splittingField`](../def/ArtinL_Conductor.html#L18) is the intermediate field $K_\rho=\overline{\mathbb Q}^{\ker\rho}$, the fixed field of the kernel; [`ArtinL.apply_mem_splittingField`](../def/ArtinL_Conductor.html#L21) records that $K_\rho$ is stable under every $\sigma\in\Gamma_{\mathbb Q}$ (because $\ker\rho$ is normal), and the accompanying instance makes $K_\rho$ a $\Gamma_{\mathbb Q}$-set by semiring automorphisms, with the evident compatibility with the inclusion into $\overline{\mathbb Q}$. For a valuation subring $A\subseteq\overline{\mathbb Q}$, [`ArtinL.placeUnder`](../def/ArtinL_Conductor.html#L45) is the valuation subring $A\cap K_\rho$ of $K_\rho$, obtained as the comap of $A$ along $K_\rho\hookrightarrow\overline{\mathbb Q}$; [`ArtinL.smul_mem_placeUnder`](../def/ArtinL_Conductor.html#L52) shows it is preserved by the decomposition subgroup $D_A\subseteq\Gamma_{\mathbb Q}$ of $A$ over $\mathbb Q$, which consequently acts on it by ring automorphisms.
--
--   On this basis, [`ArtinL.ramificationGroup ρ A i`](../def/ArtinL_Conductor.html#L76) is the subgroup of $\Gamma_{\mathbb Q}$ cut out as the intersection of $A.\mathtt{inertiaSubgroupIn}\ \mathbb Q$ (the image in $\Gamma_{\mathbb Q}$ of the inertia subgroup of $A$) with the image of $\{\sigma\in D_A:\ \sigma x-x\in\mathfrak m^{\,i+1}\ \text{for all}\ x\in A\cap K_\rho\}$, where $\mathfrak m$ is the maximal ideal of $A\cap K_\rho$; this is the $i$-th lower ramification group of $K_\rho$ at the place $A$, intersected with inertia. Next, [`ArtinL.codimInvariants ρ H`](../def/ArtinL_Conductor.html#L82) is the truncated difference $n-\dim_{\mathbb C}(\mathbb C^n)^H$, the invariants being those of the matrix representation attached to $\rho$ restricted to $H$. The rational number [`ArtinL.swanConductor ρ A`](../def/ArtinL_Conductor.html#L85) is the finsum over $i:\mathbb N$ of $\frac{|\rho(G_{i+1})|}{|\rho(I_A)|}\cdot\operatorname{codim}(\mathbb C^n)^{G_{i+1}}$, with $G_j=$ `ramificationGroup ρ A j` and $I_A$ the inertia subgroup; [`ArtinL.conductorExponentAt`](../def/ArtinL_Conductor.html#L91) adds $\operatorname{codim}(\mathbb C^n)^{I_A}$ to the natural-number ceiling of the Swan term. Finally [`ArtinL.conductorExponent ρ p`](../def/ArtinL_Conductor.html#L96) is this quantity at a chosen valuation subring lying over $p$ (i.e. with $p$ a non-unit in it) when $p$ is prime and such a subring exists, and $0$ otherwise, and [`ArtinL.conductor ρ`](../def/ArtinL_Conductor.html#L101) is the finprod $\prod_p p^{\,f(\rho,p)}$.
--
--   **Relation to Mathlib.** Mathlib supplies valuation-theoretic decomposition and inertia subgroups; the lower ramification groups used here come from the project's [`IsLocalRing.lowerRamificationGroup`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) (the inertia of $\mathfrak m^{i+1}$), and `inertiaSubgroupIn` as well as the Artin conductor, Swan conductor and conductor exponent of a complex Galois representation are the project's own notions.
--
--   **Where it is used.** These definitions give the conductor appearing in the $L$-function package for complex Galois representations, and hence the level attached to an odd two-dimensional representation; they are used by the statement modules that relate conductors, levels and the representations arising from a Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ArtinL_Conductor.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Pointwise

namespace ArtinL

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

def splittingField (ρ : Γℚ →* GL (Fin n) ℂ) : IntermediateField ℚ ℚbar :=
  IntermediateField.fixedField ρ.ker

theorem apply_mem_splittingField (ρ : Γℚ →* GL (Fin n) ℂ) (σ : Γℚ) {x : ℚbar}
    (hx : x ∈ splittingField ρ) : σ x ∈ splittingField ρ := by
  rintro ⟨τ, hτ⟩
  change τ (σ x) = σ x
  have hmem : σ⁻¹ * τ * σ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker] at hτ ⊢
    rw [map_mul, map_mul, hτ, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have h := hx ⟨σ⁻¹ * τ * σ, hmem⟩
  change (σ⁻¹ * τ * σ) x = x at h
  simpa [AlgEquiv.mul_apply] using congrArg σ h

instance mulSemiringActionSplittingField (ρ : Γℚ →* GL (Fin n) ℂ) :
    MulSemiringAction Γℚ (splittingField ρ) where
  smul σ x := ⟨σ (x : ℚbar), apply_mem_splittingField ρ σ x.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero σ := Subtype.ext (map_zero σ)
  smul_add σ x y := Subtype.ext (map_add σ (x : ℚbar) (y : ℚbar))
  smul_one σ := Subtype.ext (map_one σ)
  smul_mul σ x y := Subtype.ext (map_mul σ (x : ℚbar) (y : ℚbar))

@[simp] theorem coe_smul_splittingField (ρ : Γℚ →* GL (Fin n) ℂ) (σ : Γℚ)
    (x : splittingField ρ) : ((σ • x : splittingField ρ) : ℚbar) = σ (x : ℚbar) := rfl

def placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) :
    ValuationSubring (splittingField ρ) :=
  A.comap (algebraMap (splittingField ρ) ℚbar)

theorem mem_placeUnder_iff (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (x : splittingField ρ) : x ∈ placeUnder ρ A ↔ (x : ℚbar) ∈ A := Iff.rfl

theorem smul_mem_placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (σ : A.decompositionSubgroup ℚ) {x : splittingField ρ} (hx : x ∈ placeUnder ρ A) :
    (σ : Γℚ) • x ∈ placeUnder ρ A := by
  rw [mem_placeUnder_iff] at hx ⊢
  have h : (σ : Γℚ) • (x : ℚbar) ∈ (σ : Γℚ) • (A : ValuationSubring ℚbar) :=
    Set.smul_mem_smul_set hx
  rw [σ.2] at h
  exact h

instance mulSemiringActionPlaceUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) :
    MulSemiringAction (A.decompositionSubgroup ℚ) (placeUnder ρ A) where
  smul σ x := ⟨(σ : Γℚ) • (x : splittingField ρ), smul_mem_placeUnder ρ A σ x.2⟩
  one_smul x := Subtype.ext (one_smul Γℚ (x : splittingField ρ))
  mul_smul σ τ x := Subtype.ext (mul_smul (σ : Γℚ) (τ : Γℚ) (x : splittingField ρ))
  smul_zero σ := Subtype.ext (smul_zero (σ : Γℚ))
  smul_add σ x y := Subtype.ext (smul_add (σ : Γℚ) (x : splittingField ρ) (y : splittingField ρ))
  smul_one σ := Subtype.ext (smul_one (σ : Γℚ))
  smul_mul σ x y :=
    Subtype.ext (MulSemiringAction.smul_mul (σ : Γℚ) (x : splittingField ρ) (y : splittingField ρ))

@[simp] theorem coe_coe_smul_placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (σ : A.decompositionSubgroup ℚ) (x : placeUnder ρ A) :
    (((σ • x : placeUnder ρ A) : splittingField ρ) : ℚbar) = (σ : Γℚ) ((x : splittingField ρ) : ℚbar) := rfl

def ramificationGroup (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) (i : ℕ) :
    Subgroup Γℚ :=
  A.inertiaSubgroupIn ℚ ⊓
    (IsLocalRing.lowerRamificationGroup (placeUnder ρ A) (A.decompositionSubgroup ℚ) i).map
      (A.decompositionSubgroup ℚ).subtype

def codimInvariants (ρ : Γℚ →* GL (Fin n) ℂ) (H : Subgroup Γℚ) : ℕ :=
  n - Module.finrank ℂ (invariantsUnder ρ H)

def swanConductor (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) : ℚ :=
  ∑ᶠ i : ℕ,
    (Nat.card ((ramificationGroup ρ A (i + 1)).map ρ) : ℚ) /
        (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ) : ℚ) *
      (codimInvariants ρ (ramificationGroup ρ A (i + 1)) : ℚ)

def conductorExponentAt (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) : ℕ :=
  codimInvariants ρ (A.inertiaSubgroupIn ℚ) + ⌈swanConductor ρ A⌉₊

open scoped Classical in

def conductorExponent (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) : ℕ :=
  if h : p.Prime ∧ ∃ A : ValuationSubring ℚbar, A.LiesOverPrime p then
    conductorExponentAt ρ h.2.choose
  else 0

def conductor (ρ : Γℚ →* GL (Fin n) ℂ) : ℕ :=
  ∏ᶠ p : ℕ, p ^ conductorExponent ρ p

end ArtinL

end


