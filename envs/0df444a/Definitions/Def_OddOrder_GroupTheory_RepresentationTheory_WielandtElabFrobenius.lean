-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtElabFrobenius
-- name    : OddOrder_GroupTheory_RepresentationTheory_WielandtElabFrobenius
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:44:58.180319+00:00
-- url     : https://prove2.me/theorems/803fb567-cc7d-4945-9e1f-162aeac57428
-- title:
--   Peterfalvi (9.1): the kernel-FPF identity ($\dagger$) over $\mathbb{F}_p$, via base change
-- statement:
--   The chief-factor dimension identity ($\star$) reduces to the kernel-FPF fact ($\dagger$) over the prime field $\mathbb{F}_p=\mathbb{Z}/p$: $\dim[V,U]=|E|\cdot\dim([V,U]\cap V^E)$. This file proves it from the algebraically closed case by base change. It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/WielandtElabFrobenius.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/WielandtElabFrobenius.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtKernelFPF
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BaseChange
import Definitions.Def_OddOrder_GroupTheory_WielandtPerFactorDischarge
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod

namespace OddOrder.GroupTheory.WielandtKernelFPF

open Module Representation

open OddOrder.RepresentationTheory (baseChangeRepresentation baseChangeRepresentation_comp
  invariants_baseChangeRepresentation_eq_bot finrank_invariants_baseChangeRepresentation)

open OddOrder.GroupTheory.WielandtCounting (ker_averageMap_comp_invariant
  eq_zero_of_mem_ker_averageMap_of_mem_invariants)

variable {L : Type*} [Group L] [Finite L]

/-- **The kernel-FPF dimension identity (†) over the prime field `𝔽_p`, full-module form.**  For
`U ◁ L` with `p ∤ |U|`, `E ≤ L` with `U ⊔ E = ⊤`, `|E| ⟂ |U|`, the conjugation action of `E` on `U`
fixed-point-free, and a finite-dimensional `𝔽_p[L]`-module `V` with no `U`-invariants (`Vᵁ = 0`):

`dim V = |E| · dim Vᴱ`.

No hypothesis relates `p` and `|E|` (the underlying count is characteristic-free).  This is the
form consumed by Peterfalvi Part II, Ch. II step (3) ([Is] Theorem 15.16 there): `M` a minimal
`KP`-invariant elementary abelian `r`-subgroup with the Frobenius kernel `K` acting
fixed-point-freely, so `dim M = |P| · dim C_M(P)` — where `r ≠ |P|` is a *conclusion* of step (3),
not an available hypothesis.  Proved by base change to `𝔽̄_p`, where
`finrank_eq_card_mul_finrank_invariants_kernelFPF` applies. -/
theorem finrank_eq_card_mul_finrank_invariants_kernelFPF_zmod {U E : Subgroup L} [U.Normal]
    [Fintype ↥E] {p : ℕ} [Fact p.Prime]
    (hsup : U ⊔ E = ⊤) (hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U)) (hEnt : 1 < Nat.card ↥E)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1)
    (hpU : ¬ p ∣ Nat.card ↥U)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρV : Representation (ZMod p) L V)
    (hVU : invariants (ρV.comp U.subtype) = ⊥) :
    Module.finrank (ZMod p) V =
      Fintype.card ↥E * Module.finrank (ZMod p) ↥(invariants (ρV.comp E.subtype)) := by
  let K := AlgebraicClosure (ZMod p)
  have : NeZero (Nat.card ↥U : K) :=
    ⟨fun h => hpU ((CharP.cast_eq_zero_iff K p _).mp h)⟩
  have hbarU : invariants ((baseChangeRepresentation K ρV).comp U.subtype) = ⊥ := by
    rw [← baseChangeRepresentation_comp]
    exact invariants_baseChangeRepresentation_eq_bot K (ρV.comp U.subtype) hVU
  have hkey := finrank_eq_card_mul_finrank_invariants_kernelFPF (baseChangeRepresentation K ρV)
    (U := U) (E := E) hsup hcopUE hEnt hfpf hbarU
  rwa [Module.finrank_baseChange, ← baseChangeRepresentation_comp,
    finrank_invariants_baseChangeRepresentation] at hkey

/-- **Peterfalvi (9.1), the kernel-FPF identity (†) over `𝔽_p`.**  For `U ◁ L` a `p′`-group, `E ≤ L`
with `U ⊔ E = ⊤`, `|E| ⟂ |U|`, the conjugation action of `E` on `U` fixed-point-free, and a
finite-dimensional `𝔽_p[L]`-module `V`:

`dim [V,U] = |E| · dim ([V,U] ⊓ Vᴱ)`,   where `[V,U] = ker (averageMap ρ|_U)`.

This is the `htag` hypothesis of `WielandtCounting.finrank_elab_identity`.  Proved by base change to
`𝔽̄_p`, where `finrank_eq_card_mul_finrank_invariants_kernelFPF` applies. -/
theorem htag_of_frobenius {U E : Subgroup L} [U.Normal] [Fintype ↥E]
    {p : ℕ} [Fact p.Prime] [Fintype ↥U] [Invertible (Fintype.card ↥U : ZMod p)]
    (hsup : U ⊔ E = ⊤) (hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U)) (hEnt : 1 < Nat.card ↥E)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1)
    (hpU : ¬ p ∣ Nat.card ↥U)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρV : Representation (ZMod p) L V) :
    Module.finrank (ZMod p) ↥(LinearMap.ker (averageMap (ρV.comp U.subtype))) =
      Fintype.card ↥E * Module.finrank (ZMod p)
        ↥(LinearMap.ker (averageMap (ρV.comp U.subtype)) ⊓ invariants (ρV.comp E.subtype)) := by
  classical
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  -- Make the augmentation submodule `[V,U]` opaque (its defining `averageMap` is `whnf`-heavy).
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Submodule (ZMod p) V,
      W₀ = LinearMap.ker (averageMap (ρV.comp U.subtype)) := ⟨_, rfl⟩
  rw [← hW₀]
  -- `W₀ = [V,U]` is `L`-invariant, so it is a subrepresentation `ρ_W`.
  have hinv : ∀ g : L, W₀ ≤ W₀.comap (ρV g) := by
    intro g x hx
    rw [hW₀] at hx ⊢
    rw [Submodule.mem_comap]
    exact ker_averageMap_comp_invariant ρV U g x hx
  let ρW : Representation (ZMod p) L ↥W₀ := ρV.subrepresentation W₀ hinv
  -- The action of `ρ_W` reads off the ambient action on representatives.
  have hρWval : ∀ (g : L) (w : ↥W₀), ((ρW g w : ↥W₀) : V) = ρV g (w : V) := fun g w => rfl
  -- (B) `W₀ = [V,U]` has no `U`-invariants.
  have hWUbot : invariants (ρW.comp U.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hwV_inv : (w : V) ∈ invariants (ρV.comp U.subtype) := fun u => by
      have h : ((ρW (U.subtype u) w : ↥W₀) : V) = (w : V) := congrArg Subtype.val (hw u)
      rw [hρWval] at h; exact h
    have hwV_ker : (w : V) ∈ LinearMap.ker (averageMap (ρV.comp U.subtype)) := hW₀ ▸ w.2
    exact Subtype.ext (eq_zero_of_mem_ker_averageMap_of_mem_invariants
      (ρV.comp U.subtype) hwV_ker hwV_inv)
  -- (†) over `𝔽_p` for the subrepresentation `ρ_W` (base change happens inside).
  have hkey := finrank_eq_card_mul_finrank_invariants_kernelFPF_zmod
    hsup hcopUE hEnt hfpf hpU ρW hWUbot
  -- `dim [V,U] = |E| · dim ([V,U]ᴱ)`; identify `[V,U]ᴱ` with `[V,U] ⊓ Vᴱ`.
  have hbridge : (invariants (ρW.comp E.subtype)).map W₀.subtype
      = W₀ ⊓ invariants (ρV.comp E.subtype) := by
    ext v
    simp only [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, fun e => ?_⟩
      have h : ((ρW (E.subtype e) w : ↥W₀) : V) = (w : V) := congrArg Subtype.val (hw e)
      rw [hρWval] at h; exact h
    · rintro ⟨hvW, hvE⟩
      refine ⟨⟨v, hvW⟩, fun e => ?_, rfl⟩
      apply Subtype.ext
      change ((ρW (E.subtype e) ⟨v, hvW⟩ : ↥W₀) : V) = v
      rw [hρWval]; exact hvE e
  rw [hkey, ← Submodule.finrank_map_subtype_eq W₀ (invariants (ρW.comp E.subtype)), hbridge]

/-- **Peterfalvi (9.1), the per-chief-factor dimension identity (⋆)** from the Frobenius data.  For
the elementary-abelian representation `elabRepresentation p φ` of `L = U ⋊ E` (Frobenius) on a
finite
`𝔽_p`-module `V` (`p ∤ |U|, |E|`), the dimension identity `WielandtDimIdentity p φ U E` holds.

This is `WielandtCounting.finrank_elab_identity` discharged by the kernel-FPF fact (†)
`htag_of_frobenius`.  Stated with the `𝔽_p`-module as an instance *binder* (not `letI`-bound) so the
`↥(Submodule …)` coercions resolve once here and survive substitution of the concrete chief-factor
module `Additive ↥N` — the same device piece C uses for `WielandtDimIdentity` (avoiding the
`Additive ↥N` diamond). -/
theorem wielandtDimIdentity_of_frobenius {U E : Subgroup L} [U.Normal] [Fintype ↥E]
    {p : ℕ} [Fact p.Prime] [Fintype ↥U] [Invertible (Fintype.card ↥U : ZMod p)]
    (hsup : U ⊔ E = ⊤) (hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U)) (hEnt : 1 < Nat.card ↥E)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1)
    (hpU : ¬ p ∣ Nat.card ↥U)
    {V : Type*} [CommGroup V] [Module (ZMod p) (Additive V)] [Finite V] (φ : L →* MulAut V) :
    WielandtDimIdentity p φ U E :=
  WielandtCounting.finrank_elab_identity (elabRepresentation p φ) U E hsup
    (htag_of_frobenius hsup hcopUE hEnt hfpf hpU (elabRepresentation p φ))

end OddOrder.GroupTheory.WielandtKernelFPF


