-- Prove2me | Definitions.Def_CohCarrier_Inst
-- name    : CohCarrier_Inst
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/c03bdd0a-39b0-54b9-b5d6-cdd2d11daa67
-- title:
--   Hecke datum on the level-(M,H) cohomology carrier
-- statement:
--   The standing context is a modulus $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, a set $S$ of naturals, a commutative ring $\mathcal{O}$ and a field $k$ that is an $\mathcal{O}$-algebra. The carrier is $H^1(M,H,\mathcal{O}) = \mathrm{Hom}(\Gamma_H(M), \mathcal{O})$, realised as additive homomorphisms out of `Additive` of the group $\Gamma_H(M) = \{\gamma \in \Gamma_0(M) : \gamma_{11} \bmod M \in H\}$, with its natural $\mathcal{O}$-module structure.
--
--   Two families of operators are packaged as $\mathcal{O}$-linear endomorphisms of this carrier. For $\ell \neq 0$, `heckeTL` sends $\varphi$ to the additive corestriction (group transfer) along the finite-index subgroup $\{\gamma \in \Gamma_H(M) : \gamma_{01} \equiv 0 \bmod \ell\}$ of the composite of $\varphi$ with the conjugation homomorphism $\begin{pmatrix}a&b\\c&d\end{pmatrix} \mapsto \begin{pmatrix}a&b/\ell\\c\ell&d\end{pmatrix}$ into $\Gamma_H(M)$; it agrees on the nose with the underlying additive operator `heckeT`. For diamond operators, `gamma0Units_surjective` establishes that $\gamma \mapsto \gamma_{11} \bmod M$ is a surjection $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ (by an explicit matrix), and `diamondL` $d$ is precomposition with conjugation by a chosen preimage of $d$; `diamondL_eq_diamondRaw` shows the result is the same for every preimage $\sigma$ of $d$, two preimages differing by an element of $\Gamma_H(M)$, whose conjugation acts trivially on homomorphisms out of $\Gamma_H(M)$.
--
--   The inductive type `Gen M S` has generators $T_\ell$ for primes $\ell \notin S$ with $\ell \nmid M$, generators $U_q$ for primes $q \mid M$, and $\langle d\rangle$ for $d \in (\mathbb{Z}/M)^\times$; `opFamily` sends $T_\ell$ and $U_q$ to `heckeTL` at $\ell$ resp. $q$, and $\langle d \rangle$ to `diamondL` $d$. Given a proof `hcomm` that this family commutes pairwise and a residual eigensystem $\bar\theta : \mathrm{Gen}\,M\,S \to k$, `hdata` is the corresponding `HeckeData` (generators, operators, the commutativity proof as a field, and $\bar\theta$), and `MLAt` abbreviates its localisation: the carrier viewed as a module over $\mathcal{O}[X_g]$ via the operators, localised at the complement of the prime $\ker(\mathrm{aeval}\ \bar\theta)$.
--
--   **Relation to Mathlib.** Mathlib supplies the congruence subgroups $\Gamma_0(M)$, $\Gamma(M)$ and the group transfer `MonoidHom.transfer`; the subgroups $\Gamma_H(M)$, the additive corestriction `coresAdd`, the carrier `H1`, the generator type `Gen` and the structure `HeckeData` with its localisation `ML` are the project's own, and the Hecke operators are built by transfer rather than from Mathlib's modular-forms material.
--
--   **Where it is used.** These definitions give the Hecke module at a fixed level $(M,H)$, localised at the maximal ideal attached to a residual eigensystem $\bar\theta$; modules of this shape, at a base level and at auxiliary Taylor–Wiles levels, are the objects whose freeness over diamond-operator rings feeds the patching argument in the modularity lifting theorem. The retention of generators $U_q$ at all primes $q \mid M$ allows the operators at auxiliary primes to be used at raised level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CohCarrier_Inst.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_HeckeData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CohCarrier

open CongruenceSubgroup
open scoped MatrixGroups

inductive Gen (M : ℕ) (S : Set ℕ) : Type
  | T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M)
  | U (q : ℕ) (hq : q.Prime) (hqM : q ∣ M)
  | dia (d : (ZMod M)ˣ)

section Inst

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]

def heckeTL (ℓ : ℕ) [NeZero ℓ] : Module.End 𝒪 (H1 M H 𝒪) where
  toFun φ := coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL M H ℓ)))
  map_add' φ ψ := by
    have : (φ + ψ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) + ψ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : (r • φ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        r • φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

theorem heckeTL_apply (ℓ : ℕ) [NeZero ℓ] (φ : H1 M H 𝒪) :
    heckeTL M H 𝒪 ℓ φ = heckeT M H ℓ 𝒪 φ := rfl

theorem gamma0Units_surjective [NeZero M] : Function.Surjective (gamma0Units M) := by

  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ) - 1 : ℤ) : ZMod M) = 0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k; (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Gamma0Map]
  simp [γ]

def diamondL [NeZero M] (d : (ZMod M)ˣ) : Module.End 𝒪 (H1 M H 𝒪) where
  toFun φ := diamondRaw M H 𝒪 (Classical.choose (gamma0Units_surjective M d)) φ
  map_add' φ ψ := map_add _ φ ψ
  map_smul' r φ := by ext; rfl

theorem diamondL_eq_diamondRaw [NeZero M] (d : (ZMod M)ˣ) (σ : Gamma0 M)
    (hσ : gamma0Units M σ = d) (φ : H1 M H 𝒪) :
    diamondL M H 𝒪 d φ = diamondRaw M H 𝒪 σ φ := by
  have hσ₀ : gamma0Units M (Classical.choose (gamma0Units_surjective M d)) = d :=
    Classical.choose_spec (gamma0Units_surjective M d)
  set σ₀ := Classical.choose (gamma0Units_surjective M d)

  have hκu : gamma0Units M (σ₀ * σ⁻¹) = 1 := by
    rw [map_mul, map_inv, hσ₀, hσ, mul_inv_cancel]
  have hκH : ((σ₀ * σ⁻¹ : Gamma0 M) : SL(2, ℤ)) ∈ GammaH M H := by
    rw [mem_GammaH_iff]
    exact ⟨(σ₀ * σ⁻¹).2, hκu ▸ one_mem H⟩
  set κ : ↥(GammaH M H) := ⟨((σ₀ * σ⁻¹ : Gamma0 M) : SL(2, ℤ)), hκH⟩ with hκdef

  have hconj : ∀ γ : ↥(GammaH M H),
      conjHom M H σ₀ γ = κ * conjHom M H σ γ * κ⁻¹ := by
    intro γ
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, hκdef, Subgroup.coe_mul,
      InvMemClass.coe_inv, Subgroup.coe_mul]
    group

  ext γ
  show φ (Additive.ofMul (conjHom M H σ₀ (Additive.toMul γ))) = φ (Additive.ofMul (conjHom M H σ (Additive.toMul γ)))
  rw [hconj (Additive.toMul γ)]
  have hsplit : Additive.ofMul (κ * conjHom M H σ (Additive.toMul γ) * κ⁻¹) =
      Additive.ofMul κ + Additive.ofMul (conjHom M H σ (Additive.toMul γ)) + (-(Additive.ofMul κ)) := by
    rw [ofMul_mul, ofMul_mul, ofMul_inv]
  rw [hsplit, map_add, map_add, map_neg]
  abel

def opFamily [NeZero M] : Gen M S → Module.End 𝒪 (H1 M H 𝒪)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M H 𝒪 ℓ
  | .U q hq _ => haveI : NeZero q := ⟨hq.ne_zero⟩; heckeTL M H 𝒪 q
  | .dia d => diamondL M H 𝒪 d

def hdata [NeZero M]
    (hcomm : ∀ g h : Gen M S, opFamily M H S 𝒪 g * opFamily M H S 𝒪 h =
      opFamily M H S 𝒪 h * opFamily M H S 𝒪 g)
    (θbar : Gen M S → k) : HeckeData 𝒪 (H1 M H 𝒪) k where
  Gen := Gen M S
  op := opFamily M H S 𝒪
  comm := hcomm
  θbar := θbar

abbrev MLAt [NeZero M]
    (hcomm : ∀ g h : Gen M S, opFamily M H S 𝒪 g * opFamily M H S 𝒪 h =
      opFamily M H S 𝒪 h * opFamily M H S 𝒪 g)
    (θbar : Gen M S → k) : Type :=
  (hdata M H S 𝒪 k hcomm θbar).ML

example [NeZero M] (hcomm) (θbar : Gen M S → k) : Module 𝒪 (MLAt M H S 𝒪 k hcomm θbar) :=
  inferInstance

end Inst

end CohCarrier

end


