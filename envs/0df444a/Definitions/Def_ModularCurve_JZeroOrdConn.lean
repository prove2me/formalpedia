-- Prove2me | Definitions.Def_ModularCurve_JZeroOrdConn
-- name    : ModularCurve_JZeroOrdConn
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/fc864617-6f38-576e-a732-d436e3826ee4
-- title:
--   Specialisation kernel and ordinary-connectedness for J0​(N)
-- statement:
--   Throughout, $A$ is a valuation subring of $\overline{\mathbb{Q}}$, $\ell$ a prime, $N$ a positive level, and $D$ a good-reduction specialisation datum `JZeroGoodReductionSpecialization_alt` for $J_0(N)$ at $A$: an additive map $\mathrm{sp}$ from `JZero N` onto the degree-zero divisor class group of the modular function field over the residue field of $A$, together with an endomorphism $F$ of the target, surjectivity of $\mathrm{sp}$, Hecke-equivariance, invariance of $\mathrm{sp}$ under the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\ \mathbb{Q}$, compatibility of Frobenius elements with $F$, injectivity of $\mathrm{sp}$ on $p$-power torsion for $p$ not divisible by $\ell$, and the Eichler–Shimura relation $F^2 - T_\ell F + \ell = 0$. The Tate module [`TateModule ℓ (JZero N)`](../def/EllipticCurve_TateModule.html#L15) is realised concretely as the Hecke-submodule of sequences $x \colon \mathbb{N} \to$ `JZero N` with $x_0 = 0$ and $\ell \cdot x_{n+1} = x_n$.
--
--   `specKernelSet D` is the set of such sequences $x$ all of whose terms are killed by $\mathrm{sp}$. For a coefficient ring $O''$ over $\mathbb{Z}_\ell$ and a field $K$ over $O''$, `specKernel D O'' K` is the $K$-subspace of $K \otimes_{O''} (O'' \otimes_{\mathbb{Z}_\ell} T_\ell)$ spanned by the elements $1 \otimes (a \otimes z)$ with $a \in O''$ and $z \in$ `specKernelSet D`. The structure `JZeroOrdConn D W`, for a $K$-subspace $W$ of that tensor product, is a proposition with the single field asserting $\dim_K (W \cap \mathrm{specKernel}) \le 1$.
--
--   Three facts are recorded. If $\rho_M$ is a monoid homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to the $O''$-endomorphisms of $O'' \otimes_{\mathbb{Z}_\ell} T_\ell$ which acts on pure tensors $a \otimes x$ by the Galois action on the underlying sequence, then for $\sigma$ in the inertia subgroup and any $w$, the difference $(\rho_M\sigma)_K(w) - w$ lies in `specKernel D O'' K`; this uses only the inertia-invariance field of $D$. Any $W$ with $\dim_K W \le 1$ satisfies `JZeroOrdConn D W`, and the whole space does not when $\dim_K \mathrm{specKernel} \ge 2$. Three auxiliary span lemmas establish the corresponding statement over a general base.
--
--   **Relation to Mathlib.** The specialisation datum, the sequence model of the Tate module and the ordinary-connectedness predicate are the project's own; Mathlib supplies the surrounding apparatus (`Submodule.span`, `Module.finrank`, `LinearMap.baseChange`, tensor products and valuation-subring inertia subgroups).
--
--   **Where it is used.** These notions express, in the $\lambda$-adic setting, the line inside a two-dimensional eigenspace cut out by the kernel of specialisation at a prime $\ell$ of bad reduction: inertia at $\ell$ moves vectors into that line, so a plane satisfying `JZeroOrdConn` has at most one such direction. This is the vocabulary used in the level-lowering step at $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroOrdConn.lean

import Definitions.Def_ModularCurve_JZeroGoodReductionV3
import Definitions.Def_ModularCurve_EichlerShimuraData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

namespace ModularCurve

section KernelSpan

variable {R O'' K : Type} [CommRing R] [CommRing O''] [Algebra R O''] [Field K] [Algebra O'' K]
variable {V₀ : Type} [AddCommGroup V₀] [Module R V₀]

private theorem tmul_tmul_mem_span {Z : Set V₀} (k : K) (a : O'') {z : V₀} (hz : z ∈ Z) :
    k ⊗ₜ[O''] (a ⊗ₜ[R] z) ∈ Submodule.span K
      (Set.range fun p : O'' × Z => (1 : K) ⊗ₜ[O''] (p.1 ⊗ₜ[R] (p.2 : V₀))) := by
  have h : k ⊗ₜ[O''] (a ⊗ₜ[R] z) = k • ((1 : K) ⊗ₜ[O''] (a ⊗ₜ[R] z)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem _ k (Submodule.subset_span ⟨(a, ⟨z, hz⟩), rfl⟩)

private theorem tmul_apply_sub_mem_span {Z : Set V₀} (φ : Module.End O'' (O'' ⊗[R] V₀))
    (hφ : ∀ x : V₀, ∃ y : V₀, y - x ∈ Z ∧ ∀ a : O'', φ (a ⊗ₜ[R] x) = a ⊗ₜ[R] y)
    (k : K) (v : O'' ⊗[R] V₀) :
    k ⊗ₜ[O''] (φ v) - k ⊗ₜ[O''] v ∈ Submodule.span K
      (Set.range fun p : O'' × Z => (1 : K) ⊗ₜ[O''] (p.1 ⊗ₜ[R] (p.2 : V₀))) := by
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.tmul_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul a x =>
    obtain ⟨y, hyx, hφx⟩ := hφ x
    rw [hφx a, ← TensorProduct.tmul_sub k, ← TensorProduct.tmul_sub a]
    exact tmul_tmul_mem_span k a hyx
  | add v₁ v₂ h₁ h₂ =>
    rw [map_add, TensorProduct.tmul_add, TensorProduct.tmul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h₁ h₂

private theorem baseChange_sub_mem_span {Z : Set V₀} (φ : Module.End O'' (O'' ⊗[R] V₀))
    (hφ : ∀ x : V₀, ∃ y : V₀, y - x ∈ Z ∧ ∀ a : O'', φ (a ⊗ₜ[R] x) = a ⊗ₜ[R] y)
    (w : K ⊗[O''] (O'' ⊗[R] V₀)) :
    φ.baseChange K w - w ∈ Submodule.span K
      (Set.range fun p : O'' × Z => (1 : K) ⊗ₜ[O''] (p.1 ⊗ₜ[R] (p.2 : V₀))) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul k v => rw [LinearMap.baseChange_tmul]; exact tmul_apply_sub_mem_span φ hφ k v
  | add w₁ w₂ h₁ h₂ => rw [map_add, add_sub_add_comm]; exact Submodule.add_mem _ h₁ h₂

end KernelSpan

noncomputable section OrdConn

open AlgebraicCurve IsLocalRing

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime] {N : ℕ} [NeZero N]

variable [Module HeckeAlg (JZero N)]
variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]
variable (D : JZeroGoodReductionSpecialization_alt A ℓ Fact.out N)

def specKernelSet : Set (TateModule ℓ (JZero N)) :=
  {x | ∀ n : ℕ, D.sp ((x : ℕ → JZero N) n) = 0}

variable (O'' : Type) [CommRing O''] [Algebra ℤ_[ℓ] O''] (K : Type) [Field K] [Algebra O'' K]
variable [Module ℤ_[ℓ] (TateModule ℓ (JZero N))]

def specKernel : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N))) :=
  Submodule.span K (Set.range fun p : O'' × specKernelSet D =>
    (1 : K) ⊗ₜ[O''] (p.1 ⊗ₜ[ℤ_[ℓ]] (p.2 : TateModule ℓ (JZero N))))

variable {O'' K}

structure JZeroOrdConn (W : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N)))) : Prop where
  finrank_inf_specKernel_le_one : Module.finrank K ↥(W ⊓ specKernel D O'' K) ≤ 1

set_option maxSynthPendingDepth 3 in

theorem baseChange_sub_mem_specKernel
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End O'' (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N)))
    (hρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x y : TateModule ℓ (JZero N)),
      (y : ℕ → JZero N) = σ • (x : ℕ → JZero N) →
        ∀ a : O'', ρM σ (a ⊗ₜ[ℤ_[ℓ]] x) = a ⊗ₜ[ℤ_[ℓ]] y)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (w : K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N))) :
    (ρM σ).baseChange K w - w ∈ specKernel D O'' K :=
  baseChange_sub_mem_span (Z := specKernelSet D) (ρM σ) (fun x =>
    ⟨⟨σ • (x : ℕ → JZero N), ModularCurve.TateModule.smul_mem σ x.2⟩,
      by
        intro n
        show D.sp (σ • (x : ℕ → JZero N) n - (x : ℕ → JZero N) n) = 0
        rw [map_sub, D.inertia_comm σ hσ, sub_self],
      fun a => hρ σ x ⟨σ • (x : ℕ → JZero N), ModularCurve.TateModule.smul_mem σ x.2⟩ rfl a⟩) w

theorem JZeroOrdConn.of_finrank_le_one
    (W : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N)))) [Module.Finite K W]
    (hW : Module.finrank K W ≤ 1) : JZeroOrdConn D W :=
  ⟨le_trans (Submodule.finrank_mono (inf_le_left : W ⊓ specKernel D O'' K ≤ W)) hW⟩

theorem not_jZeroOrdConn_top_of_two_le_finrank_specKernel [Module.Finite K (specKernel D O'' K)]
    (h : 2 ≤ Module.finrank K (specKernel D O'' K)) :
    ¬ JZeroOrdConn D (⊤ : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N)))) := by
  intro hc
  have h1 := hc.finrank_inf_specKernel_le_one
  haveI : IsNoetherian K ↥(specKernel D O'' K) :=
    isNoetherian_of_isNoetherianRing_of_finite K ↥(specKernel D O'' K)
  haveI : Module.Finite K ↥((⊤ : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N)))) ⊓
      specKernel D O'' K) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_right) (Submodule.inclusion_injective _)
  have h2 := Submodule.finrank_mono (le_inf le_top le_rfl : specKernel D O'' K ≤
    (⊤ : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[ℓ]] TateModule ℓ (JZero N)))) ⊓ specKernel D O'' K)
  omega

end OrdConn

end ModularCurve


