-- Prove2me | Definitions.Def_PadicComplex_GaloisAction
-- name    : PadicComplex_GaloisAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/6cc6fb72-00b9-5aa4-9186-44bc523259b7
-- title:
--   Galois action on the p-adic complex numbers Cp​
-- statement:
--   Fix a prime $p$. The abbreviation [`PadicComplex.Gal p`](../def/PadicComplex_GaloisAction.html#L14) denotes the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p`, an algebraic closure of $\mathbb{Q}_p$ carrying the spectral norm; $\mathbb{C}_p$ (`ℂ_[p]`) is its completion. The module equips $\mathbb{C}_p$ with the Galois action obtained by extension by continuity and records the arithmetic of that action. `isometry_algEquiv` states that each $\sigma \in$ `Gal p` is an isometry of `PadicAlgCl p`, this being the invariance of the spectral norm under $\mathbb{Q}_p$-automorphisms; from it the instance `uniformContinuousConstSMul_gal` asserts that each $\sigma$ acts uniformly continuously, which is what makes the scalar action on the completion well behaved. `smul_coe` is the compatibility $\sigma \cdot \iota(x) = \iota(\sigma x)$ for $x$ in `PadicAlgCl p`, where $\iota$ is the canonical map into the completion, and `continuous_smul_left`, `uniformContinuous_smul_left` give continuity and uniform continuity of $x \mapsto \sigma \cdot x$ on $\mathbb{C}_p$. The instance `mulSemiringAction` upgrades the additive action to an action by ring automorphisms, $\sigma \cdot 1 = 1$ and $\sigma\cdot(xy) = (\sigma\cdot x)(\sigma\cdot y)$, the multiplicativity being proved by density from the corresponding identity on `PadicAlgCl p`. The norm is preserved: `norm_smul_eq` and `nnnorm_smul_eq` give $\|\sigma\cdot x\| = \|x\|$ in $\mathbb{R}$ and in $\mathbb{R}_{\ge 0}$, and `isometry_smul` restates this as the isometry property of $x \mapsto \sigma \cdot x$ on $\mathbb{C}_p$. The instances `smulCommClass_gal_padic` and `smulCommClass_padic_gal` record that the Galois action commutes with the $\mathbb{Q}_p$-scalar multiplication in either order, and `smul_algebraMap` that the action fixes the image of $\mathbb{Q}_p$ in $\mathbb{C}_p$ pointwise; consequently `galAlgHom p σ` is $\sigma$ viewed as a $\mathbb{Q}_p$-algebra endomorphism of $\mathbb{C}_p$, with `galAlgHom_apply` identifying its values with $\sigma \cdot x$. Finally `smul_coe_padicEmbedding` compares the local and global pictures: for $a$ in `AlgebraicClosure ℚ`, $\sigma$ applied to the image of $a$ under [`padicEmbedding p`](../def/GaloisRep_CompletionBridge.html#L17) (viewed in $\mathbb{C}_p$) equals the image of [`localGaloisToGlobal p σ a`](../def/GaloisRep_CompletionBridge.html#L41), where [`localGaloisToGlobal`](../def/GaloisRep_CompletionBridge.html#L41) is the homomorphism from $\mathbb{Q}_p$-automorphisms of `PadicAlgCl p` to $\mathbb{Q}$-automorphisms of `AlgebraicClosure ℚ` obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension.
--
--   **Relation to Mathlib.** Mathlib supplies `PadicAlgCl p`, its spectral norm, the completion `ℂ_[p]` and the scalar action of an isometric group action on a completion; what is added here is the `MulSemiringAction` instance of the $\mathbb{Q}_p$-automorphism group on `ℂ_[p]` together with the norm-invariance, commuting-scalars and algebra-map lemmas, and the comparison with the embedding of `AlgebraicClosure ℚ`.
--
--   **Where it is used.** These instances make $\mathbb{C}_p$ a topological $\mathbb{Q}_p$-algebra with a continuous, isometric, $\mathbb{Q}_p$-linear action of the local Galois group, the setting in which $p$-adic Hodge-theoretic conditions on the Galois representations attached to the Frey curve are formulated. The final compatibility lemma is what transports statements about the global Galois group of $\mathbb{Q}$, acting on torsion points via the chosen embedding of $\overline{\mathbb{Q}}$ into $\overline{\mathbb{Q}}_p$, into local statements over $\mathbb{C}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PadicComplex_GaloisAction.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open UniformSpace

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

abbrev Gal : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

theorem isometry_algEquiv (σ : Gal p) : Isometry σ := by
  refine AddMonoidHomClass.isometry_of_norm σ fun x => ?_
  exact (spectralNorm_eq_of_equiv σ x).symm

instance uniformContinuousConstSMul_gal :
    UniformContinuousConstSMul (Gal p) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_algEquiv p σ).uniformContinuous⟩

@[simp]
theorem smul_coe (σ : Gal p) (x : PadicAlgCl p) :
    σ • ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ x).symm

theorem continuous_smul_left (σ : Gal p) : Continuous fun x : ℂ_[p] => σ • x :=
  continuous_const_smul σ

theorem uniformContinuous_smul_left (σ : Gal p) : UniformContinuous fun x : ℂ_[p] => σ • x :=
  uniformContinuous_const_smul σ

instance mulSemiringAction : MulSemiringAction (Gal p) ℂ_[p] :=
  { (inferInstance : DistribMulAction (Gal p) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq ((continuous_fst.mul continuous_snd).const_smul σ)
          ((continuous_fst.const_smul σ).mul (continuous_snd.const_smul σ))
      · intro a b
        rw [← Completion.coe_mul, smul_coe, smul_coe, smul_coe, map_mul, Completion.coe_mul] }

@[simp]
theorem norm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((continuous_norm).comp (continuous_const_smul σ)) continuous_norm
  · intro a
    rw [smul_coe, norm_extends, norm_extends]
    exact (spectralNorm_eq_of_equiv σ a).symm

@[simp]
theorem nnnorm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖₊ = ‖x‖₊ :=
  NNReal.eq (norm_smul_eq p σ x)

theorem isometry_smul (σ : Gal p) : Isometry fun x : ℂ_[p] => σ • x :=
  AddMonoidHomClass.isometry_of_norm (MulSemiringAction.toRingHom (Gal p) ℂ_[p] σ)
    (norm_smul_eq p σ)

instance smulCommClass_gal_padic : SMulCommClass (Gal p) ℚ_[p] ℂ_[p] :=
  inferInstance

instance smulCommClass_padic_gal : SMulCommClass ℚ_[p] (Gal p) ℂ_[p] :=
  SMulCommClass.symm _ _ _

@[simp]
theorem smul_algebraMap (σ : Gal p) (q : ℚ_[p]) :
    σ • (algebraMap ℚ_[p] ℂ_[p] q) = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

abbrev galAlgHom (σ : Gal p) : ℂ_[p] →ₐ[ℚ_[p]] ℂ_[p] :=
  MulSemiringAction.toAlgHom ℚ_[p] ℂ_[p] σ

@[simp]
theorem galAlgHom_apply (σ : Gal p) (x : ℂ_[p]) : galAlgHom p σ x = σ • x := rfl

theorem smul_coe_padicEmbedding (σ : Gal p) (a : AlgebraicClosure ℚ) :
    σ • ((padicEmbedding p a : PadicAlgCl p) : ℂ_[p]) =
      ((padicEmbedding p (localGaloisToGlobal p σ a) : PadicAlgCl p) : ℂ_[p]) := by
  rw [smul_coe, padicEmbedding_localGaloisToGlobal]

end PadicComplex

end


