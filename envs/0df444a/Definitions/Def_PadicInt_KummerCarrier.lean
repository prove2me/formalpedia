-- Prove2me | Definitions.Def_PadicInt_KummerCarrier
-- name    : PadicInt_KummerCarrier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/56d4373f-efa5-5e82-b1f5-362db9c5595a
-- title:
--   Kummer carrier algebra over Zp​ with comultiplication and counit
-- statement:
--   Fix a prime $p$ and a unit $u \in \mathbb{Z}_p^{\times}$. For $j \in \mathbb{Z}/p$ write $j.\mathrm{val} \in \{0,\dots,p-1\}$ for its canonical representative. The module sets $\mathtt{kpoly}\,j = X^p - u^{j.\mathrm{val}} \in \mathbb{Z}_p[X]$, records that this polynomial is monic, and defines $A_j := \mathbb{Z}_p[X]/(X^p - u^{j.\mathrm{val}})$ as `AdjoinRoot` of it, together with the resulting freeness and finiteness of $A_j$ as a $\mathbb{Z}_p$-module. The carrier is the product algebra $\mathrm{Carrier} = \prod_{j \in \mathbb{Z}/p} A_j$, free of rank $p^2$ over $\mathbb{Z}_p$; $z_j \in A_j$ denotes the image of $X$, and $z_j^p$ is the image of $u^{j.\mathrm{val}}$ under the structure map.
--
--   Three structure maps are then given as $\mathbb{Z}_p$-algebra homomorphisms. The counit $\varepsilon \colon \mathrm{Carrier} \to \mathbb{Z}_p$ projects to the component $j = 0$ and sends $z_0 \mapsto 1$. The factor $c_{a,b} := (u^{-1})^{\lfloor (a.\mathrm{val} + b.\mathrm{val})/p \rfloor}$ (so $c_{a,b} \in \{1, u^{-1}\}$) satisfies $c_{a,b}^p \, u^{a.\mathrm{val}+b.\mathrm{val}} = u^{(a+b).\mathrm{val}}$, which is exactly what makes $\mu_{a,b} \colon \mathrm{Carrier} \to A_a \otimes_{\mathbb{Z}_p} A_b$ — projection to the component $a+b$ followed by $z_{a+b} \mapsto c_{a,b}\,(z_a \otimes z_b)$ — well defined. The algebra isomorphism $\mathtt{piPiEquiv} \colon \mathrm{Carrier} \otimes_{\mathbb{Z}_p} \mathrm{Carrier} \simeq \prod_{a}\prod_{b} A_a \otimes_{\mathbb{Z}_p} A_b$, characterised on pure tensors by $f \otimes g \mapsto (a,b) \mapsto f(a) \otimes g(b)$, is used to transport the family $(\mu_{a,b})$ into a comultiplication $\Delta \colon \mathrm{Carrier} \to \mathrm{Carrier} \otimes_{\mathbb{Z}_p} \mathrm{Carrier}$.
--
--   Finally, for a commutative $\mathbb{Z}_p$-algebra $L$, an index $j$ and $w \in L$ with $w^p = u^{j.\mathrm{val}}$, $\mathtt{evalAt}$ is the algebra homomorphism $\mathrm{Carrier} \to L$ projecting to component $j$ and sending $z_j \mapsto w$; $\mathtt{polyLift}$ assigns to $h \in \mathrm{Carrier}$ and $j$ the degree-$< p$ polynomial representative of $h(j)$ obtained by division by the monic $\mathtt{kpoly}\,j$, and $\mathtt{evalAt}$ of $h$ equals the evaluation of that representative at $w$.
--
--   **Relation to Mathlib.** Built from Mathlib's `AdjoinRoot`, the freeness and finiteness of quotients by monic polynomials, and the product/tensor-product algebra equivalences `Algebra.TensorProduct.piRight` and `Algebra.TensorProduct.comm`. Mathlib has no notion of the group schemes of order $p^2$ involved, so the carrier and its structure maps are the project's own; the bialgebra and Hopf-algebra axioms for $(\varepsilon, \Delta)$, and the antipode, are not part of this module.
--
--   **Where it is used.** The algebra constructed here is the coordinate ring of the finite flat group scheme of order $p^2$ over $\mathbb{Z}_p$ prolonging an extension of $\mathbb{Z}/p$ by $\mu_p$ with Kummer class $[u] \in \mathbb{Z}_p^{\times}/(\mathbb{Z}_p^{\times})^p$, its comultiplication encoding the group law $(j_1,\xi_1)(j_2,\xi_2) = (j_1+j_2, c_{j_1,j_2}\xi_1\xi_2)$. It supports the existence statement for such a finite flat Hopf algebra, with its comultiplication and its $L$-points, used in the local analysis at $p$ of the Galois representations attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PadicInt_KummerCarrier.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open Polynomial

namespace PadicInt.KummerCarrier

variable (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ)

noncomputable abbrev kpoly (j : ZMod p) : ℤ_[p][X] := X ^ p - C ((u : ℤ_[p]) ^ j.val)

lemma kpoly_monic (j : ZMod p) : (kpoly p u j).Monic :=
  (monic_X_pow p).sub_of_left <| by
    apply lt_of_le_of_lt degree_C_le
    rw [degree_X_pow]; exact_mod_cast (Fact.out : p.Prime).pos

noncomputable abbrev A (j : ZMod p) := AdjoinRoot (kpoly p u j)

noncomputable instance (j : ZMod p) : Module.Free ℤ_[p] (A p u j) :=
  (kpoly_monic p u j).free_adjoinRoot
noncomputable instance (j : ZMod p) : Module.Finite ℤ_[p] (A p u j) :=
  (kpoly_monic p u j).finite_adjoinRoot

noncomputable abbrev Carrier := Π j : ZMod p, A p u j

noncomputable abbrev z (j : ZMod p) : A p u j := AdjoinRoot.root (kpoly p u j)

lemma z_pow_p (j : ZMod p) :
    z p u j ^ p = algebraMap ℤ_[p] (A p u j) ((u : ℤ_[p]) ^ j.val) := by
  have h : (Polynomial.aeval (z p u j)) (kpoly p u j) = 0 := by
    rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

noncomputable def ε : Carrier p u →ₐ[ℤ_[p]] ℤ_[p] :=
  (AdjoinRoot.liftAlgHom (kpoly p u 0) (Algebra.ofId ℤ_[p] ℤ_[p]) 1
    (by simp [kpoly, ZMod.val_zero, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C])).comp
    (Pi.evalAlgHom _ _ 0)

noncomputable def piPiEquiv :
    Carrier p u ⊗[ℤ_[p]] Carrier p u ≃ₐ[ℤ_[p]]
      Π a : ZMod p, Π b : ZMod p, A p u a ⊗[ℤ_[p]] A p u b :=
  (Algebra.TensorProduct.comm ℤ_[p] _ _).trans <|
    (Algebra.TensorProduct.piRight ℤ_[p] ℤ_[p] (Carrier p u) (A p u)).trans <|
      AlgEquiv.piCongrRight fun a =>
        (Algebra.TensorProduct.comm ℤ_[p] _ _).trans <|
          Algebra.TensorProduct.piRight ℤ_[p] ℤ_[p] (A p u a) (A p u)

lemma piPiEquiv_tmul (f g : Carrier p u) (a b : ZMod p) :
    piPiEquiv p u (f ⊗ₜ g) a b = f a ⊗ₜ g b := by
  simp [piPiEquiv, Algebra.TensorProduct.piRight_tmul, Algebra.TensorProduct.comm_tmul]

noncomputable def cfac (a b : ZMod p) : ℤ_[p] := ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ ((a.val + b.val) / p)

lemma cfac_pow_p_mul (a b : ZMod p) :
    cfac p u a b ^ p * (u : ℤ_[p]) ^ (a.val + b.val) = (u : ℤ_[p]) ^ (a + b).val := by
  unfold cfac
  rw [ZMod.val_add, ← pow_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 1
  rw [← zpow_natCast u, ← zpow_natCast u, ← zpow_natCast u⁻¹, inv_zpow, ← zpow_neg, ← zpow_add]
  congr 1
  have hmd := Nat.mod_add_div (a.val + b.val) p
  have hmc : (a.val + b.val) / p * p = p * ((a.val + b.val) / p) := Nat.mul_comm _ _
  omega

noncomputable def μ (a b : ZMod p) : Carrier p u →ₐ[ℤ_[p]] A p u a ⊗[ℤ_[p]] A p u b :=
  (AdjoinRoot.liftAlgHom (kpoly p u (a + b)) (Algebra.ofId _ _)
    (cfac p u a b • (z p u a ⊗ₜ z p u b))
    (by
      simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
        _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
      rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u a),
        Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u b),
        TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
        ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
      rfl)).comp
    (Pi.evalAlgHom _ _ (a + b))

noncomputable def Δ : Carrier p u →ₐ[ℤ_[p]] Carrier p u ⊗[ℤ_[p]] Carrier p u :=
  (piPiEquiv p u).symm.toAlgHom.comp
    (Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => μ p u a b)

variable {L : Type*} [CommRing L] [Algebra ℤ_[p] L]

noncomputable def evalAt (j : ZMod p) (w : L)
    (hw : w ^ p = algebraMap ℤ_[p] L ((u : ℤ_[p]) ^ j.val)) :
    Carrier p u →ₐ[ℤ_[p]] L :=
  (AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId ℤ_[p] L) w
    (by
      simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
      exact hw.trans rfl)).comp
    (Pi.evalAlgHom _ _ j)

noncomputable def polyLift (h : Carrier p u) (j : ZMod p) : Polynomial ℤ_[p] :=
  AdjoinRoot.modByMonicHom (kpoly_monic p u j) (h j)

lemma evalAt_eq_aeval_polyLift (j : ZMod p) (w : L)
    (hw : w ^ p = algebraMap ℤ_[p] L ((u : ℤ_[p]) ^ j.val)) (h : Carrier p u) :
    evalAt p u j w hw h = Polynomial.aeval w (polyLift p u h j) := by
  unfold evalAt polyLift
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply]
  conv_lhs => rw [show (h j) = AdjoinRoot.mk _
    (AdjoinRoot.modByMonicHom (kpoly_monic p u j) (h j)) from
    (AdjoinRoot.mk_leftInverse (kpoly_monic p u j) (h j)).symm]
  rw [AdjoinRoot.liftAlgHom_mk]
  rfl

end PadicInt.KummerCarrier


