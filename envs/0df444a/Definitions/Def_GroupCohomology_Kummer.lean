-- Prove2me | Definitions.Def_GroupCohomology_Kummer
-- name    : GroupCohomology_Kummer
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/42b84dac-c9a9-5dbc-9aaf-2883ceacbb2d
-- title:
--   Kummer cocycles and the Kummer map to H1(μp​)
-- statement:
--   For a field extension $L/K$ the module attaches to each $\alpha \in L^\times$ the function $\kappa_\alpha \colon \mathrm{Aut}_K(L) \to L^\times$, $\kappa_\alpha(\sigma) = \sigma(\alpha)/\alpha$ (`kummerCocycle`), and records its basic algebra: it is a multiplicative $1$-cocycle for the natural action of $L \simeq_\alpha[K] L$ on $L^\times$ (indeed a coboundary there), it is multiplicative in $\alpha$, it is $p$-torsion as soon as $\alpha^p$ lies in the image of $K$, and for two units $\alpha,\beta$ with $\alpha^p = \beta^p = a$ the quotient $\kappa_\alpha/\kappa_\beta$ is the coboundary $\sigma \mapsto \sigma(\alpha/\beta)/(\alpha/\beta)$ of the $p$-th root of unity $\alpha/\beta$. The action of $L \simeq_\alpha[K] L$ on $L^\times$ restricts to the subgroup $\mu_p(L) =$ `rootsOfUnity p L`, and this restriction is registered as a `MulDistribMulAction`; `kummerRep K L p` is the resulting $\mathbb{Z}$-linear representation of $L \simeq_\alpha[K] L$ on (the additive copy of) $\mu_p(L)$, so that Mathlib's `H1` of it is $H^1(\mathrm{Aut}_K(L), \mu_p(L))$.
--
--   Given $a \in K^\times$, $\alpha \in L^\times$ and a proof that $a = \alpha^p$ in $L$, `kummerCocycleRoots` is $\kappa_\alpha$ viewed as a cocycle with values in $\mu_p(L)$, `kummerCocycles` its incarnation as an element of `cocycles₁ (kummerRep K L p)`, and `kummerClass` its image in $H^1$; by the coboundary computation this class depends only on $a$, not on the chosen root. The subgroup `powerSubgroup K L p` of $K^\times$ consists of those $a$ whose image in $L$ is the $p$-th power of a unit of $L$, i.e. $K^\times \cap (L^\times)^p$; it contains the image of $a \mapsto a^p$ on $K^\times$. Choosing for each of its elements a $p$-th root (`chosenRoot`, by choice) yields the group homomorphism `kummerHom K L p` from $K^\times \cap (L^\times)^p$ to $H^1(\mathrm{Aut}_K(L),\mu_p(L))$ written multiplicatively, $a \mapsto [\kappa_{a^{1/p}}]$; its value on an explicitly presented element $\langle a, \alpha, \alpha^p = a\rangle$ is $[\kappa_\alpha]$. No hypothesis beyond the extension $L/K$ and the natural number $p$ enters these definitions.
--
--   **Relation to Mathlib.** The cohomological scaffolding is Mathlib's: `IsMulCocycle₁`, `IsMulCoboundary₁`, `cocycles₁`, `H1`, `H1π` and `Rep.ofMulDistribMulAction`. The `MulDistribMulAction` of `L ≃ₐ[K] L` on `rootsOfUnity p L` is added here as the restriction of the Mathlib action on `Lˣ`; the Kummer cocycle, the class `kummerClass`, the subgroup `powerSubgroup` and the map `kummerHom` are the project's own.
--
--   **Where it is used.** These constructions supply the Kummer-theoretic dictionary between $p$-th power classes in $K^\times$ and classes in $H^1(\mathrm{Aut}_K(L), \mu_p(L))$; the kernel and surjectivity statements for `kummerHom`, proved elsewhere under Galois hypotheses, are what make it usable in the descent and Galois-cohomology computations of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_Kummer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

namespace groupCohomology

namespace Kummer

section Unbundled

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

@[simp]
lemma val_smul_units (σ : L ≃ₐ[K] L) (α : Lˣ) : ((σ • α : Lˣ) : L) = σ (α : L) :=
  rfl

lemma smul_units_div (σ : L ≃ₐ[K] L) (x y : Lˣ) : σ • (x / y) = σ • x / σ • y := by
  ext
  simp only [val_smul_units, Units.val_div_eq_div_val, map_div₀]

lemma smul_units_pow (σ : L ≃ₐ[K] L) (x : Lˣ) (n : ℕ) : σ • (x ^ n) = (σ • x) ^ n := by
  ext
  simp only [val_smul_units, Units.val_pow_eq_pow_val, map_pow]

lemma smul_units_eq_self_of_mem_range (σ : L ≃ₐ[K] L) {α : Lˣ}
    (hα : (α : L) ∈ Set.range (algebraMap K L)) : σ • α = α := by
  obtain ⟨b, hb⟩ := hα
  ext
  rw [val_smul_units, ← hb, AlgEquiv.commutes]

def kummerCocycle (α : Lˣ) (σ : L ≃ₐ[K] L) : Lˣ :=
  σ • α / α

lemma kummerCocycle_apply (α : Lˣ) (σ : L ≃ₐ[K] L) :
    kummerCocycle α σ = σ • α / α := rfl

lemma isMulCoboundary₁_kummerCocycle (α : Lˣ) :
    IsMulCoboundary₁ (kummerCocycle (K := K) α) :=
  ⟨α, fun _ => rfl⟩

theorem isMulCocycle₁_kummerCocycle (α : Lˣ) :
    IsMulCocycle₁ (kummerCocycle (K := K) α) := by
  intro σ τ
  show (σ * τ) • α / α = σ • (τ • α / α) * (σ • α / α)
  rw [mul_smul, smul_units_div, div_mul_div_cancel]

theorem kummerCocycle_mul (α β : Lˣ) (σ : L ≃ₐ[K] L) :
    kummerCocycle (α * β) σ = kummerCocycle α σ * kummerCocycle β σ := by
  show σ • (α * β) / (α * β) = (σ • α / α) * (σ • β / β)
  rw [smul_mul', mul_div_mul_comm]

theorem kummerCocycle_pow_eq_one {p : ℕ} {a : K} {α : Lˣ}
    (hα : algebraMap K L a = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    kummerCocycle α σ ^ p = 1 := by
  have hmem : ((α ^ p : Lˣ) : L) ∈ Set.range (algebraMap K L) :=
    ⟨a, by rw [hα, Units.val_pow_eq_pow_val]⟩
  rw [kummerCocycle_apply, div_pow, ← smul_units_pow,
    smul_units_eq_self_of_mem_range σ hmem, div_self']

theorem kummerCocycle_div_kummerCocycle_of_pow_eq {p : ℕ} {a : K} {α β : Lˣ}
    (hα : algebraMap K L a = (α : L) ^ p) (hβ : algebraMap K L a = (β : L) ^ p) :
    (α / β) ^ p = 1 ∧
      ∀ σ : L ≃ₐ[K] L, kummerCocycle α σ / kummerCocycle β σ = σ • (α / β) / (α / β) := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [div_pow, div_eq_one]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hα, ← hβ]
  · rw [kummerCocycle_apply, kummerCocycle_apply, smul_units_div, div_div_div_comm]

lemma smul_mem_rootsOfUnity {p : ℕ} (σ : L ≃ₐ[K] L) {ζ : Lˣ} (hζ : ζ ∈ rootsOfUnity p L) :
    σ • ζ ∈ rootsOfUnity p L := by
  rw [mem_rootsOfUnity] at hζ ⊢
  rw [← smul_units_pow, hζ, smul_one]

instance instMulDistribMulActionRootsOfUnity (p : ℕ) :
    MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L) where
  smul σ ζ := ⟨σ • (ζ : Lˣ), smul_mem_rootsOfUnity σ ζ.2⟩
  one_smul ζ := Subtype.ext (one_smul _ (ζ : Lˣ))
  mul_smul σ τ ζ := Subtype.ext (mul_smul σ τ (ζ : Lˣ))
  smul_mul σ ζ η := Subtype.ext (smul_mul' σ (ζ : Lˣ) (η : Lˣ))
  smul_one σ := Subtype.ext (smul_one σ)

@[simp]
lemma coe_smul_rootsOfUnity {p : ℕ} (σ : L ≃ₐ[K] L) (ζ : rootsOfUnity p L) :
    ((σ • ζ : rootsOfUnity p L) : Lˣ) = σ • (ζ : Lˣ) :=
  rfl

lemma coe_div_rootsOfUnity {p : ℕ} (ζ η : rootsOfUnity p L) :
    ((ζ / η : rootsOfUnity p L) : Lˣ) = (ζ : Lˣ) / (η : Lˣ) :=
  rfl

end Unbundled

section RepLevel

variable {K L : Type} [Field K] [Field L] [Algebra K L]

noncomputable abbrev kummerRep (K L : Type) [Field K] [Field L] [Algebra K L] (p : ℕ) :
    Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L)

variable {p : ℕ} {a : Kˣ} {α : Lˣ}

def kummerCocycleRoots (hα : algebraMap K L (a : K) = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    rootsOfUnity p L :=
  ⟨kummerCocycle α σ, kummerCocycle_pow_eq_one hα σ⟩

@[simp]
lemma coe_kummerCocycleRoots (hα : algebraMap K L (a : K) = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    (kummerCocycleRoots hα σ : Lˣ) = kummerCocycle α σ :=
  rfl

theorem isMulCocycle₁_kummerCocycleRoots (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    IsMulCocycle₁ (kummerCocycleRoots hα) :=
  fun σ τ => Subtype.ext (isMulCocycle₁_kummerCocycle α σ τ)

noncomputable def kummerCocycles (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    cocycles₁ (kummerRep K L p) :=
  cocyclesOfIsMulCocycle₁ (isMulCocycle₁_kummerCocycleRoots hα)

lemma coe_kummerCocycles (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    ⇑(kummerCocycles hα) = Additive.ofMul ∘ kummerCocycleRoots hα :=
  rfl

noncomputable def kummerClass (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    H1 (kummerRep K L p) :=
  H1π (kummerRep K L p) (kummerCocycles hα)

theorem kummerClass_eq_of_pow_eq {β : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (a : K) = (β : L) ^ p) :
    kummerClass hα = kummerClass hβ := by
  obtain ⟨hpow, hcob⟩ := kummerCocycle_div_kummerCocycle_of_pow_eq hα hβ
  rw [kummerClass, kummerClass, H1π_eq_iff]
  exact (coboundariesOfIsMulCoboundary₁
    (f := fun σ => kummerCocycleRoots hα σ / kummerCocycleRoots hβ σ)
    ⟨⟨α / β, hpow⟩, fun σ => Subtype.ext (hcob σ).symm⟩).2

theorem mul_pow_eq {b : Kˣ} {β : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (b : K) = (β : L) ^ p) :
    algebraMap K L ((a * b : Kˣ) : K) = ((α * β : Lˣ) : L) ^ p := by
  rw [Units.val_mul, map_mul, hα, hβ, Units.val_mul, mul_pow]

theorem kummerClass_mul {b : Kˣ} {β : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (b : K) = (β : L) ^ p) :
    kummerClass (mul_pow_eq hα hβ) = kummerClass hα + kummerClass hβ := by
  rw [kummerClass, kummerClass, kummerClass, ← map_add]
  congr 1
  ext σ
  exact congrArg Additive.ofMul (Subtype.ext (kummerCocycle_mul α β σ))

theorem inv_pow_eq {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    algebraMap K L ((a⁻¹ : Kˣ) : K) = ((α⁻¹ : Lˣ) : L) ^ p := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, hα, Units.val_inv_eq_inv_val, inv_pow]

def powerSubgroup (K L : Type) [Field K] [Field L] [Algebra K L] (p : ℕ) : Subgroup Kˣ where
  carrier := {a : Kˣ | ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := fun ⟨α, hα⟩ ⟨β, hβ⟩ => ⟨α * β, mul_pow_eq hα hβ⟩
  inv_mem' := fun ⟨α, hα⟩ => ⟨α⁻¹, inv_pow_eq hα⟩

@[simp]
theorem mem_powerSubgroup_iff {a : Kˣ} :
    a ∈ powerSubgroup K L p ↔ ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p :=
  Iff.rfl

theorem range_powMonoidHom_le_powerSubgroup :
    (powMonoidHom p : Kˣ →* Kˣ).range ≤ powerSubgroup K L p := by
  rintro _ ⟨b, rfl⟩
  refine ⟨Units.map (algebraMap K L).toMonoidHom b, ?_⟩
  show algebraMap K L (((b ^ p : Kˣ) : K)) = (algebraMap K L (b : K)) ^ p
  rw [Units.val_pow_eq_pow_val, map_pow]

noncomputable def chosenRoot (a : powerSubgroup K L p) : Lˣ :=
  (mem_powerSubgroup_iff.mp a.2).choose

theorem chosenRoot_spec (a : powerSubgroup K L p) :
    algebraMap K L ((a : Kˣ) : K) = ((chosenRoot a : Lˣ) : L) ^ p :=
  (mem_powerSubgroup_iff.mp a.2).choose_spec

noncomputable def kummerHom (K L : Type) [Field K] [Field L] [Algebra K L] (p : ℕ) :
    powerSubgroup K L p →* Multiplicative (H1 (kummerRep K L p)) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (kummerClass (chosenRoot_spec a))) fun a b => by
    have h : kummerClass (chosenRoot_spec (a * b))
        = kummerClass (chosenRoot_spec a) + kummerClass (chosenRoot_spec b) := by
      rw [kummerClass_eq_of_pow_eq (chosenRoot_spec (a * b))
        (mul_pow_eq (chosenRoot_spec a) (chosenRoot_spec b))]
      exact kummerClass_mul _ _
    show Multiplicative.ofAdd (kummerClass (chosenRoot_spec (a * b)))
        = Multiplicative.ofAdd (kummerClass (chosenRoot_spec a))
          * Multiplicative.ofAdd (kummerClass (chosenRoot_spec b))
    rw [← ofAdd_add, h]

@[simp]
theorem kummerHom_apply (a : powerSubgroup K L p) :
    kummerHom K L p a = Multiplicative.ofAdd (kummerClass (chosenRoot_spec a)) :=
  rfl

theorem kummerHom_apply_mk (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    kummerHom K L p ⟨a, α, hα⟩ = Multiplicative.ofAdd (kummerClass hα) := by
  show Multiplicative.ofAdd (kummerClass (chosenRoot_spec ⟨a, α, hα⟩)) = _
  rw [kummerClass_eq_of_pow_eq (chosenRoot_spec ⟨a, α, hα⟩) hα]

end RepLevel

end Kummer

end groupCohomology


