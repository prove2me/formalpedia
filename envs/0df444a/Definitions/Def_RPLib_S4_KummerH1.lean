-- Prove2me | Definitions.Def_RPLib_S4_KummerH1
-- name    : RPLib_S4_KummerH1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:04:12.124484+00:00
-- url     : https://prove2.me/theorems/acdec790-a355-4b58-97a3-ea5f81093b88
-- title:
--   Kummer theory: $H^1(\Gamma, \mathbb{Z}/N)$ is the Kummer group, with its Frobenius action
-- statement:
--   With $K \subseteq E$ integral, $\Gamma \le \operatorname{Gal}(E/K)$ and a primitive $N$-th root of unity $\zeta$ fixed by $\Gamma$, the file proves that with trivial coefficients there are no coboundaries and that Kummer characters give an isomorphism $$\operatorname{rad}(\Gamma, N) / (E^\times)^\Gamma \;\cong\; H^1(\Gamma, \mathbb{Z}/N),$$ where $\operatorname{rad}(\Gamma, N)$ is the group of units $\alpha$ with $\alpha^N$ fixed by $\Gamma$. For $\psi$ normalising $\Gamma$ with $\psi\zeta = \zeta^{w'}$ the operator $T_\psi$ acts by $T_\psi[\kappa_\alpha] = w[\kappa_{\psi\alpha}]$ ($w w' = 1$); in particular a geometric Frobenius acts by $F[\kappa_\alpha] = q\,[\kappa_{\varphi^{-1}\alpha}]$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter IV, Section 3; J.-P. Serre, Galois Cohomology, Springer (1997), Chapter I, Section 2

import Mathlib
import Definitions.Def_RPLib_S4_KummerGal
import Definitions.Def_RPLib_S4_CurveCohPair

/-!
# S4-Kummer, part 2: `H¹(Γ, ZMod N)` is the Kummer group, with the Frobenius action

Setting of part 1 (`Def_RP_Kummer_Gal`): fields `K ⊆ E` with `E/K` integral, `Γ ≤ Gal(E/K)`, a primitive `N`-th root
of unity `ζ` fixed by `Γ`. Cohomology is the locally constant cohomology of `Def_RP_CurveCoh_Pair` with TRIVIAL
coefficients `ZMod N` (`triv K E N`).

* `B1_triv_eq_bot`, `H1mk_triv_injective`: with trivial coefficients there are no coboundaries;
* `kclass hζ hζΓ hα : H1 (triv K E N) Γ`: the class of the Kummer character of a radical `α`;
* `kummerEquiv`: **Kummer theory**, `rad Γ N / (Γ-fixed units) ≃* H¹(Γ, ZMod N)`;
* `frobH1_kclass`: for `ψ` with `ψ ζ = ζ ^ w'` (and `Γ` normal), `T_ψ [kchar α] = w • [kchar (ψ α)]` when `w w' = 1`;
* `geomFrob_kclass`: for an ARITHMETIC Frobenius `φ ζ = ζ ^ q`, the GEOMETRIC Frobenius `F = T_{φ⁻¹}` acts by
  `F [kchar α] = q • [kchar (φ⁻¹ α)]`: on `H¹(Γ, ZMod N) = (Kummer group) ⊗ μ_N^{⊗ -1}` the twist is the scalar `q`
  (review R4: eigenvalues `q / ω_i`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh

noncomputable section

section Triv

variable (K E : Type) [Field K] [Field E] [Algebra K E] (N : ℕ)

/-- Trivial `ZMod N` coefficients for `Gal(E/K)`. -/
abbrev triv : Representation (ZMod N) (E ≃ₐ[K] E) (ZMod N) :=
  Representation.trivial (ZMod N) (E ≃ₐ[K] E) (ZMod N)

variable {K E} (Γ : Subgroup (E ≃ₐ[K] E))

theorem mem_Z1_triv (c : Γ → ZMod N) :
    c ∈ Z1 (triv K E N) Γ ↔ IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + c h := by
  rw [mem_Z1]
  simp only [triv, Representation.trivial_apply]

theorem B1_triv_eq_bot : B1 (triv K E N) Γ = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨-, m, hm⟩
  rw [Submodule.mem_bot]
  funext g
  rw [hm g]
  simp [triv]

theorem H1mk_triv_injective : Function.Injective (H1.mk (triv K E N) Γ) := by
  rw [← LinearMap.ker_eq_bot, H1.mk, Submodule.ker_mkQ, B1_triv_eq_bot, Submodule.comap_bot,
    Submodule.ker_subtype]

end Triv

section Classes

variable {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsIntegral K E] {N : ℕ} [NeZero N]
  {Γ : Subgroup (E ≃ₐ[K] E)} {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)

include hζ hζΓ

theorem kchar_mem_Z1 {α : Eˣ} (hα : α ∈ rad Γ N) : kchar hζ (Γ := Γ) α ∈ Z1 (triv K E N) Γ :=
  (mem_Z1_triv N Γ _).2 ⟨isLocallyConstant_kchar hζ α, kchar_mul hζ hζΓ hα⟩

/-- The Kummer class `[kchar α] ∈ H¹(Γ, ZMod N)` of a radical `α`. -/
def kclass {α : Eˣ} (hα : α ∈ rad Γ N) : H1 (triv K E N) Γ :=
  H1.mk (triv K E N) Γ ⟨kchar hζ α, kchar_mem_Z1 hζ hζΓ hα⟩

theorem kclass_mul {α β : Eˣ} (hα : α ∈ rad Γ N) (hβ : β ∈ rad Γ N) :
    kclass hζ hζΓ ((rad Γ N).mul_mem hα hβ) = kclass hζ hζΓ hα + kclass hζ hζΓ hβ := by
  rw [kclass, kclass, kclass, ← map_add]
  congr 1
  apply Subtype.ext
  funext σ
  show kchar hζ (α * β) σ = kchar hζ α σ + kchar hζ β σ
  exact kchar_mul_left hζ hα hβ σ

theorem kclass_eq_zero_iff {α : Eˣ} (hα : α ∈ rad Γ N) : kclass hζ hζΓ hα = 0 ↔ α ∈ fixUnits Γ := by
  rw [kclass, map_eq_zero_iff _ (H1mk_triv_injective N Γ), Submodule.mk_eq_zero, funext_iff]
  exact kchar_eq_zero_iff hζ hα

/-- Every class is a Kummer class (Hilbert 90, `exists_kchar_eq`). -/
theorem kclass_surjective (x : H1 (triv K E N) Γ) : ∃ α : Eˣ, ∃ hα : α ∈ rad Γ N, kclass hζ hζΓ hα = x := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨α, hα, h⟩ := exists_kchar_eq hζ hζΓ c ((mem_Z1_triv N Γ c).1 hc).1 ((mem_Z1_triv N Γ c).1 hc).2
  refine ⟨α, hα, ?_⟩
  rw [kclass, H1.mk]
  congr 1
  apply Subtype.ext
  funext σ
  exact h σ

/-- The Kummer homomorphism `rad Γ N → H¹(Γ, ZMod N)` (target written multiplicatively). -/
def kummerHom : rad Γ N →* Multiplicative (H1 (triv K E N) Γ) where
  toFun α := Multiplicative.ofAdd (kclass hζ hζΓ α.2)
  map_one' := by
    rw [ofAdd_eq_one, kclass_eq_zero_iff]
    intro σ _
    simp
  map_mul' α β := by
    rw [← ofAdd_add, ← kclass_mul]

theorem ker_kummerHom : (kummerHom hζ hζΓ).ker = (fixUnits Γ).subgroupOf (rad Γ N) := by
  ext α
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  show Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one, kclass_eq_zero_iff]

theorem kummerHom_surjective : Function.Surjective (kummerHom hζ hζΓ) := by
  intro x
  obtain ⟨α, hα, h⟩ := kclass_surjective hζ hζΓ (Multiplicative.toAdd x)
  refine ⟨⟨α, hα⟩, ?_⟩
  show Multiplicative.ofAdd _ = x
  rw [h]
  rfl

/-- **Kummer theory**: `rad Γ N / (Γ-fixed units) ≃* H¹(Γ, ZMod N)`. -/
def kummerEquiv :
    rad Γ N ⧸ (fixUnits Γ).subgroupOf (rad Γ N) ≃* Multiplicative (H1 (triv K E N) Γ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_kummerHom hζ hζΓ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (kummerHom_surjective hζ hζΓ))

theorem kummerEquiv_mk {α : Eˣ} (hα : α ∈ rad Γ N) :
    kummerEquiv hζ hζΓ (QuotientGroup.mk ⟨α, hα⟩) = Multiplicative.ofAdd (kclass hζ hζΓ hα) := rfl

end Classes

section Frob

variable {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsIntegral K E] {N : ℕ} [NeZero N]
  {Γ : Subgroup (E ≃ₐ[K] E)} [hΓ : Γ.Normal] {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)

theorem conj_mem_of_normal (ψ : E ≃ₐ[K] E) : ∀ σ ∈ Γ, ψ⁻¹ * σ * ψ ∈ Γ := fun σ hσ => by
  simpa using hΓ.conj_mem σ hσ ψ⁻¹

/-- Radicals are stable under any automorphism normalising `Γ`. -/
theorem rad_map (ψ : E ≃ₐ[K] E) {α : Eˣ} (hα : α ∈ rad Γ N) : Units.map (ψ : E →* E) α ∈ rad Γ N := by
  intro σ hσ
  have h := hα _ (conj_mem_of_normal ψ σ hσ)
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← map_pow]
  calc σ (ψ ((α : E) ^ N)) = ψ ((ψ⁻¹ * σ * ψ) ((α : E) ^ N)) := by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    _ = ψ ((α : E) ^ N) := by rw [h]

theorem frobH1_mk (ψ : E ≃ₐ[K] E) (c : Z1 (triv K E N) Γ) :
    frobH1 (triv K E N) Γ ψ (H1.mk (triv K E N) Γ c) =
      H1.mk (triv K E N) Γ ⟨twist (triv K E N) Γ ψ c, twist_mem_Z1 _ Γ ψ c.2⟩ :=
  rfl

/-- Frobenius on Kummer classes: if `ψ ζ = ζ ^ w'` and `w w' = 1` then `T_ψ [kchar α] = w • [kchar (ψ α)]`. -/
theorem frobH1_kclass (ψ : E ≃ₐ[K] E) {w w' : ZMod N} (hψ : ψ ζ = epow ζ w') (hww : w * w' = 1)
    {α : Eˣ} (hα : α ∈ rad Γ N) :
    frobH1 (triv K E N) Γ ψ (kclass hζ hζΓ hα) = w • kclass hζ hζΓ (rad_map ψ hα) := by
  rw [kclass, kclass, frobH1_mk, ← map_smul]
  congr 1
  apply Subtype.ext
  funext σ
  show (triv K E N) ψ (kchar hζ α (conjΓ Γ ψ σ)) = w * kchar hζ (Units.map (ψ : E →* E) α) σ
  rw [Representation.trivial_apply, kchar_conj hζ ψ (conj_mem_of_normal ψ) hψ hα (rad_map ψ hα) σ, ← mul_assoc,
    hww, one_mul]
  rfl

include hζ in
/-- If `φ ζ = ζ ^ w` and `w w' = 1` then `φ⁻¹ ζ = ζ ^ w'`. -/
theorem inv_apply_zeta (φ : E ≃ₐ[K] E) {w w' : ZMod N} (hφ : φ ζ = epow ζ w) (hww : w * w' = 1) :
    φ⁻¹ ζ = epow ζ w' := by
  have h1 : φ (epow ζ w') = ζ := by
    calc φ (epow ζ w') = (φ ζ) ^ w'.val := map_pow φ ζ w'.val
      _ = epow ζ (w * w') := by rw [hφ, epow_pow hζ]
      _ = ζ := by rw [hww, epow, ZMod.val_one_eq_one_mod, pow_mod_N hζ, pow_one]
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
  exact h1.symm

/-- **Geometric Frobenius on Kummer classes** (review R4). For an arithmetic Frobenius `φ` (`φ ζ = ζ ^ q`, `q`
invertible mod `N`), the geometric Frobenius `F = T_{φ⁻¹}` acts by `F [kchar α] = q • [kchar (φ⁻¹ α)]`. -/
theorem geomFrob_kclass (φ : E ≃ₐ[K] E) {q : ℕ} {q' : ZMod N} (hφ : φ ζ = epow ζ (q : ZMod N))
    (hq : (q : ZMod N) * q' = 1) {α : Eˣ} (hα : α ∈ rad Γ N) :
    frobH1 (triv K E N) Γ φ⁻¹ (kclass hζ hζΓ hα) = (q : ZMod N) • kclass hζ hζΓ (rad_map φ⁻¹ hα) :=
  frobH1_kclass hζ hζΓ φ⁻¹ (inv_apply_zeta hζ φ hφ hq) hq hα

end Frob

end

end Kummer
end RamanujanPetersson


