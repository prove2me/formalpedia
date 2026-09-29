-- Prove2me | Definitions.Def_GaloisRep_AdZero
-- name    : GaloisRep_AdZero
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/799485c5-2bba-53c3-86c9-018286883520
-- title:
--   Adjoint and trace-zero adjoint of a residual Galois representation
-- statement:
--   Throughout, $k$ is a field and $\bar\rho$ is a [`ResidualGaloisRep k`](../def/GaloisRep_Residual.html#L22): a $k$-vector space $V$ with $\dim_k V = 2$, a monoid homomorphism $\bar\rho \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k(V)$, and a witness that $\bar\rho$ is trivial on the elements fixing some finite-dimensional intermediate field of $\overline{\mathbb Q}/\mathbb Q$ pointwise. The module builds the conjugation action attached to $\bar\rho$. First, `adRep` is the representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on the $k$-module $\mathrm{End}_k(V)$ sending $\sigma$ to the $k$-linear map $f \mapsto \bar\rho(\sigma)\, f\, \bar\rho(\sigma^{-1})$, composed of left multiplication by $\bar\rho(\sigma)$ and right multiplication by $\bar\rho(\sigma^{-1})$; `adRep_apply` records this formula. Since $\bar\rho(\sigma)\bar\rho(\sigma^{-1}) = 1$, the trace is invariant: `trace_adRep_apply` states $\mathrm{tr}(\bar\rho(\sigma) f \bar\rho(\sigma^{-1})) = \mathrm{tr}(f)$, and `ker_trace_le_comap_adRep` deduces that the kernel of $\mathrm{tr} \colon \mathrm{End}_k(V) \to k$ is contained in its own preimage under each $\mathrm{ad}\,\bar\rho(\sigma)$. Consequently `adZeroRep` is the subrepresentation of `adRep` carried by the trace-zero endomorphisms $\ker(\mathrm{tr})$, and `adZero` packages it as an object of the category `Rep k` of representations of the absolute Galois group of $\mathbb Q$; two lemmas identify the underlying action, one by the conjugation formula on representatives and one by identifying the action of `adZero` with `adZeroRep`. Finally, for a $k$-subspace $L \subseteq V$, `adZeroFil` is the $k$-submodule of $\ker(\mathrm{tr})$ consisting of those trace-zero $f$ with $f(v) \in L$ for every $v \in V$ and $f(v) = 0$ for every $v \in L$ — the endomorphisms factoring through $V/L$ with image in $L$ — with `mem_adZeroFil_iff` restating this membership condition. No Galois-stability of `adZeroFil` is asserted here.
--
--   **Relation to Mathlib.** `Representation`, its subrepresentations and the category `Rep` are Mathlib's; the residual representation structure and the adjoint and trace-zero adjoint built from it are the project's own, there being no notion of $\mathrm{ad}^0$ in Mathlib.
--
--   **Where it is used.** The trace-zero adjoint $\mathrm{ad}^0\bar\rho$ is the coefficient module for the Galois cohomology groups that govern the deformation theory of a residual representation: $H^1$ of $\mathrm{ad}^0\bar\rho$ and its local restrictions and dual twist carry the tangent space and Selmer group computations of the modularity lifting argument. The subspace `adZeroFil L` attached to a line $L \subseteq V$ provides the filtration used to impose local conditions at a prime where $\bar\rho$ has a distinguished stable line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_AdZero.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ResidualGaloisRep

variable {k : Type} [Field k]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

noncomputable def adRep (ρbar : ResidualGaloisRep k) : Representation k Γℚ (Module.End k ρbar.V) where
  toFun σ := LinearMap.mulLeft k (ρbar.ρ σ) ∘ₗ LinearMap.mulRight k (ρbar.ρ σ⁻¹)
  map_one' := by
    ext f
    simp
  map_mul' σ τ := by
    ext f
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      Module.End.mul_apply, mul_inv_rev, map_mul, mul_assoc]

@[simp]
theorem adRep_apply (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : Module.End k ρbar.V) :
    ρbar.adRep σ f = ρbar.ρ σ * f * ρbar.ρ σ⁻¹ := rfl

theorem trace_adRep_apply (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : Module.End k ρbar.V) :
    LinearMap.trace k ρbar.V (ρbar.adRep σ f) = LinearMap.trace k ρbar.V f := by
  rw [adRep_apply, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem ker_trace_le_comap_adRep (ρbar : ResidualGaloisRep k) (σ : Γℚ) :
    LinearMap.ker (LinearMap.trace k ρbar.V) ≤ (LinearMap.ker (LinearMap.trace k ρbar.V)).comap (ρbar.adRep σ) := by
  intro f hf
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hf ⊢
  rw [trace_adRep_apply, hf]

noncomputable def adZeroRep (ρbar : ResidualGaloisRep k) :
    Representation k Γℚ (LinearMap.ker (LinearMap.trace k ρbar.V)) :=
  ρbar.adRep.subrepresentation _ ρbar.ker_trace_le_comap_adRep

noncomputable abbrev adZero (ρbar : ResidualGaloisRep k) : Rep k Γℚ :=
  Rep.of ρbar.adZeroRep

@[simp]
theorem adZeroRep_apply_coe (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    ((ρbar.adZeroRep σ f : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V)
      = ρbar.ρ σ * (f : Module.End k ρbar.V) * ρbar.ρ σ⁻¹ :=
  rfl

theorem adZero_ρ (ρbar : ResidualGaloisRep k) : ρbar.adZero.ρ = ρbar.adZeroRep := rfl

def adZeroFil (ρbar : ResidualGaloisRep k) (L : Submodule k ρbar.V) :
    Submodule k (LinearMap.ker (LinearMap.trace k ρbar.V)) where
  carrier := {f | (∀ v, (f : Module.End k ρbar.V) v ∈ L) ∧ ∀ v ∈ L, (f : Module.End k ρbar.V) v = 0}
  zero_mem' := ⟨fun _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · simpa using L.add_mem (hf1 v) (hg1 v)
    · simp [hf2 v hv, hg2 v hv]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · simpa using L.smul_mem c (hf1 v)
    · simp [hf2 v hv]

theorem mem_adZeroFil_iff (ρbar : ResidualGaloisRep k) (L : Submodule k ρbar.V) (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    f ∈ ρbar.adZeroFil L ↔ (∀ v, (f : Module.End k ρbar.V) v ∈ L) ∧ ∀ v ∈ L, (f : Module.End k ρbar.V) v = 0 :=
  Iff.rfl

end ResidualGaloisRep


